// Asm to Mach: parses x86 assembly into Mach IR (reverses CompCert's x86/Asmgen.v).

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::mreg::Mreg;
use crate::util::multi_synth_address_is_encodable;
use crate::x86::asm::{Freg, Ireg, Preg, TestCond};
use crate::x86::op::{Addressing, Comparison, Condition, Operation, OverflowArithmetic};
use crate::x86::types::*;
use ascent::aggregators;
use ascent::ascent_par;
use ascent::lattice::constant_propagation::ConstPropagation;
use ascent::lattice::set::Set;
use ascent::Dual;
use either::Either;
use log::warn;
use std::sync::Arc;

fn shift_stack_offsets(offsets: &Set<i64>, delta: i64) -> Set<i64> {
    Set(offsets
        .iter()
        .filter_map(|offset| offset.checked_add(delta))
        .collect())
}

fn exact_stack_offset(offsets: &Set<i64>) -> Option<i64> {
    if offsets.len() == 1 {
        offsets.iter().next().copied()
    } else {
        None
    }
}

// Exact architectural width of an x86 general-purpose register view.  Mreg
// and Ireg intentionally canonicalize AL/AX/EAX/RAX to one physical register;
// value proofs must retain the view width separately or a byte/word write can
// masquerade as a complete 32-bit definition.
fn x86_gpr_view_width(reg: &str) -> Option<i64> {
    match reg {
        "RAX" | "RBX" | "RCX" | "RDX" | "RSI" | "RDI" | "RBP" | "RSP" | "R8" | "R9" | "R10"
        | "R11" | "R12" | "R13" | "R14" | "R15" => Some(8),
        "EAX" | "EBX" | "ECX" | "EDX" | "ESI" | "EDI" | "EBP" | "ESP" | "R8D" | "R9D" | "R10D"
        | "R11D" | "R12D" | "R13D" | "R14D" | "R15D" => Some(4),
        "AX" | "BX" | "CX" | "DX" | "SI" | "DI" | "BP" | "SP" | "R8W" | "R9W" | "R10W" | "R11W"
        | "R12W" | "R13W" | "R14W" | "R15W" => Some(2),
        "AL" | "BL" | "CL" | "DL" | "AH" | "BH" | "CH" | "DH" | "SIL" | "DIL" | "BPL" | "SPL"
        | "R8B" | "R9B" | "R10B" | "R11B" | "R12B" | "R13B" | "R14B" | "R15B" => Some(1),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RawGprValue {
    LiveIn(Mreg, i64),
    Definition(Address, Mreg, i64),
    Constant(u64),
}

/// A finite non-negative byte-offset family
/// `{0, stride, 2*stride, ..., (count-1)*stride}`.  The payload is deliberately
/// constant-sized so the point-keyed dataflow below remains O(V * GPRs).  The
/// origin is the instruction which established the bound (normally a low-bit
/// AND); copies and exact scaling preserve it so independent table fields can
/// share one physical owner without using address proximity as dataflow.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct BoundedOffsetShape {
    origin: Address,
    stride: u64,
    count: usize,
    max: u64,
}

fn contiguous_low_mask_shape(
    origin: Address,
    destination: &str,
    immediate: i64,
) -> Option<BoundedOffsetShape> {
    let mask = match x86_gpr_view_width(destination)? {
        4 => (immediate as u32) as u64,
        8 => immediate as u64,
        _ => return None,
    };
    let count = mask.checked_add(1)?;
    if !count.is_power_of_two() {
        return None;
    }
    Some(BoundedOffsetShape {
        origin,
        stride: 1,
        count: usize::try_from(count).ok()?,
        max: mask,
    })
}

fn scale_bounded_offset_state(
    state: &ConstPropagation<BoundedOffsetShape>,
    destination: &str,
    factor: u64,
) -> ConstPropagation<BoundedOffsetShape> {
    let bit_width = match x86_gpr_view_width(destination) {
        Some(4) => 32,
        Some(8) => 64,
        _ => return ConstPropagation::Top,
    };
    let ConstPropagation::Constant(shape) = state else {
        return ConstPropagation::Top;
    };
    let Some(stride) = shape.stride.checked_mul(factor) else {
        return ConstPropagation::Top;
    };
    let Some(max) = shape.max.checked_mul(factor) else {
        return ConstPropagation::Top;
    };
    if bit_width == 32 && max > u32::MAX as u64 {
        return ConstPropagation::Top;
    }
    ConstPropagation::Constant(BoundedOffsetShape {
        origin: shape.origin,
        stride,
        count: shape.count,
        max,
    })
}

fn shift_bounded_offset_state(
    state: &ConstPropagation<BoundedOffsetShape>,
    destination: &str,
    shift: i64,
) -> ConstPropagation<BoundedOffsetShape> {
    let bit_width = match x86_gpr_view_width(destination) {
        Some(4) => 32,
        Some(8) => 64,
        _ => return ConstPropagation::Top,
    };
    let Ok(shift) = u32::try_from(shift) else {
        return ConstPropagation::Top;
    };
    if shift >= bit_width {
        return ConstPropagation::Top;
    }
    let Some(factor) = 1_u64.checked_shl(shift) else {
        return ConstPropagation::Top;
    };
    scale_bounded_offset_state(state, destination, factor)
}

fn copy_bounded_offset_state(
    state: &ConstPropagation<BoundedOffsetShape>,
    mnemonic: &str,
    destination: &str,
    source: &str,
) -> ConstPropagation<BoundedOffsetShape> {
    let destination_width = x86_gpr_view_width(destination);
    let source_width = x86_gpr_view_width(source);
    if mnemonic != "MOV"
        || destination_width != source_width
        || !matches!(destination_width, Some(4 | 8))
    {
        return ConstPropagation::Top;
    }
    let ConstPropagation::Constant(shape) = state else {
        return ConstPropagation::Top;
    };
    if destination_width == Some(4) && shape.max > u32::MAX as u64 {
        return ConstPropagation::Top;
    }
    ConstPropagation::Constant(*shape)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct UnsignedAffineValue {
    holder: Mreg,
    displacement: i64,
    holder_value: RawGprValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ExactOverflowShape {
    operation: OverflowArithmetic,
    width: i64,
    result: Mreg,
    source: Option<Mreg>,
}

fn lower_exact_overflow_condition(
    shape: ExactOverflowShape,
    test: TestCond,
) -> Option<(Condition, Arc<Vec<Mreg>>)> {
    let args = match shape.operation {
        OverflowArithmetic::Add | OverflowArithmetic::Sub => {
            Arc::new(vec![shape.result, shape.source?])
        }
        OverflowArithmetic::AddImmediate(_)
        | OverflowArithmetic::SubImmediate(_)
        | OverflowArithmetic::Neg => {
            if shape.source.is_some() {
                return None;
            }
            Arc::new(vec![shape.result])
        }
    };
    let condition = match test {
        TestCond::CondO => Condition::Carithoverflow(shape.operation, shape.width),
        TestCond::CondNo => Condition::Cnarithoverflow(shape.operation, shape.width),
        _ => return None,
    };
    Some((condition, args))
}

// MOV r32,imm32 zero-extends its destination on x86-64, so it is an exact
// value for both the 32-bit and 64-bit abstract views.  Narrow writes are not.
fn exact_mov_immediate_value(dst: &str, immediate: i64, tracked_width: i64) -> Option<u64> {
    match (x86_gpr_view_width(dst)?, tracked_width) {
        (4, 4 | 8) => Some((immediate as u32) as u64),
        (8, 4) => Some((immediate as u64) & u32::MAX as u64),
        (8, 8) => Some(immediate as u64),
        _ => None,
    }
}

fn raw_move_preserves_width(mnem: &str, dst: &str, src: &str, tracked_width: i64) -> bool {
    let Some(dst_width) = x86_gpr_view_width(dst) else {
        return false;
    };
    let Some(src_width) = x86_gpr_view_width(src) else {
        return false;
    };
    match mnem {
        "MOV" => dst_width == src_width && dst_width >= tracked_width,
        // The low dword of a sign extension is exactly its source dword.
        "MOVSXD" => tracked_width == 4 && dst_width == 8 && src_width == 4,
        _ => false,
    }
}

fn q_participants_with(participants: &Set<Address>, address: Address) -> Option<Set<Address>> {
    let mut result = participants.clone();
    result.0.insert(address);
    (result.len() <= 4).then_some(result)
}

fn q_participants_merge(
    left: &Set<Address>,
    right: &Set<Address>,
    address: Address,
) -> Option<Set<Address>> {
    let mut result = left.clone();
    result.0.extend(right.0.iter().copied());
    result.0.insert(address);
    (result.len() <= 4).then_some(result)
}

fn participants_with(participants: &Set<Address>, address: Address) -> Set<Address> {
    let mut result = participants.clone();
    result.0.insert(address);
    result
}

// SETcc writes one low-byte lane, while reg_def deliberately normalizes every
// subregister write to its architectural parent. Keep the stronger low-byte
// boolean property in a separate must lattice. Any parent-register write kills
// it; a low-byte SETcc at the same point then generates it again.
fn low_byte_boolean_transfer(
    incoming: &Set<Mreg>,
    definitions: &Set<Mreg>,
    generated: &Set<Mreg>,
) -> Set<Mreg> {
    let mut outgoing = incoming.0.clone();
    for reg in definitions.iter() {
        outgoing.remove(reg);
    }
    outgoing.extend(generated.iter().copied());
    Set(outgoing)
}

// Strict-dominator set plus the block itself.  Asm's exact-SP lattice uses
// this point-keyed dominator state to identify structural loop back edges;
// retaining pairwise dominance/reachability here would be quadratic.
fn asm_dom_set_with_self(strict: &Set<Address>, block: Address) -> Set<Address> {
    let mut dominators = strict.0.clone();
    dominators.insert(block);
    Set(dominators)
}

// The width-suffixed bswap builtin for an operand register: 32-bit for an E-prefixed or R8D..R15D form, 64-bit otherwise, since a bare __builtin_bswap is undefined at link.
fn bswap_builtin_for_reg(r: &str) -> &'static str {
    let u = r.to_ascii_uppercase();
    if u.starts_with('E') || u.ends_with('D') {
        "__builtin_bswap32"
    } else {
        "__builtin_bswap64"
    }
}

// Genuinely-packed SIMD mnemonics with no scalar lowering, whose presence fingerprints an auto-vectorized loop; excludes block moves, PXOR and all scalar FP ops so struct-copy recovery is untouched.
fn is_packed_alu_mnem(mnem: &str) -> bool {
    let m = mnem.to_ascii_uppercase();
    let m = m.strip_prefix('V').unwrap_or(&m);
    matches!(
        m,
        // packed integer add/sub (byte/word/dword/qword), with/without saturation
        "PADDB" | "PADDW" | "PADDD" | "PADDQ" | "PADDSB" | "PADDSW" | "PADDUSB" | "PADDUSW"
        | "PSUBB" | "PSUBW" | "PSUBD" | "PSUBQ" | "PSUBSB" | "PSUBSW" | "PSUBUSB" | "PSUBUSW"
        // packed integer multiply / multiply-add
        | "PMULLW" | "PMULLD" | "PMULHW" | "PMULHUW" | "PMULDQ" | "PMULUDQ" | "PMADDWD" | "PMADDUBSW"
        // packed integer min/max/abs/avg
        | "PMINSB" | "PMINSW" | "PMINSD" | "PMINUB" | "PMINUW" | "PMINUD"
        | "PMAXSB" | "PMAXSW" | "PMAXSD" | "PMAXUB" | "PMAXUW" | "PMAXUD"
        | "PABSB" | "PABSW" | "PABSD" | "PAVGB" | "PAVGW"
        // packed compare (eq/gt) -- byte/word/dword/qword
        | "PCMPEQB" | "PCMPEQW" | "PCMPEQD" | "PCMPEQQ"
        | "PCMPGTB" | "PCMPGTW" | "PCMPGTD" | "PCMPGTQ"
        // packed shuffle / unpack / pack / blend
        | "PSHUFB" | "PSHUFD" | "PSHUFW" | "PSHUFLW" | "PSHUFHW"
        | "PUNPCKLBW" | "PUNPCKLWD" | "PUNPCKLDQ" | "PUNPCKLQDQ"
        | "PUNPCKHBW" | "PUNPCKHWD" | "PUNPCKHDQ" | "PUNPCKHQDQ"
        | "PACKSSWB" | "PACKSSDW" | "PACKUSWB" | "PACKUSDW" | "PBLENDW" | "PBLENDVB"
        // movemask / packed-vector convert (note scalar forms are CVTSI2SS/CVTSS2SI etc.)
        | "PMOVMSKB" | "CVTDQ2PS" | "CVTDQ2PD" | "CVTPS2DQ" | "CVTTPS2DQ" | "CVTPD2DQ" | "CVTTPD2DQ"
        // packed float arithmetic (scalar forms are ADDSS/MULSS/...; these are the *PS/*PD lanes)
        | "ADDPS" | "ADDPD" | "SUBPS" | "SUBPD" | "MULPS" | "MULPD" | "DIVPS" | "DIVPD"
        | "MAXPS" | "MAXPD" | "MINPS" | "MINPD" | "HADDPS" | "HADDPD" | "HSUBPS" | "HSUBPD"
        // packed shifts by immediate/reg (vector lane shifts; scalar is SHL/SHR/SAR)
        | "PSLLW" | "PSLLD" | "PSLLQ" | "PSRLW" | "PSRLD" | "PSRLQ" | "PSRAW" | "PSRAD"
    )
}

// A whole-register SSE/AVX move: both 64-bit lanes of the destination come from
// the source, so the high lane is copied rather than defined or killed.
fn is_wide_simd_mov_mnem(mnem: &str) -> bool {
    let m = mnem.to_ascii_uppercase();
    let m = m.strip_prefix('V').unwrap_or(&m);
    matches!(
        m,
        "MOVAPS" | "MOVAPD" | "MOVUPS" | "MOVUPD" | "MOVDQA" | "MOVDQU"
    )
}

// A GP-to-XMM or narrow load into an XMM: x86 defines these to zero bits 64..127.
fn simd_zeroes_high_lane_mnem(mnem: &str) -> bool {
    let m = mnem.to_ascii_uppercase();
    let m = m.strip_prefix('V').unwrap_or(&m);
    matches!(m, "MOVQ" | "MOVD")
}

// Self-XOR of an XMM: the compiler's zero idiom, both lanes cleared.
fn simd_self_zero_mnem(mnem: &str) -> bool {
    let m = mnem.to_ascii_uppercase();
    let m = m.strip_prefix('V').unwrap_or(&m);
    matches!(m, "PXOR" | "XORPS" | "XORPD")
}

// A legacy packed equality compare with the same source and destination is an
// all-ones idiom: every lane compares equal to itself, so all 128 result bits
// are set.  Keep this separate from general packed-ALU lowering; the identity
// is exact for every input bit pattern and therefore has a scalar low/high-lane
// representation even though an arbitrary packed compare does not.
fn simd_self_all_ones_mnem(mnem: &str) -> bool {
    matches!(
        mnem.to_ascii_uppercase().as_str(),
        "PCMPEQB" | "PCMPEQW" | "PCMPEQD" | "PCMPEQQ"
    )
}

// Low-quadword interleave: the destination's high lane becomes the source's low
// lane, which is how gcc pairs two 8-byte values before one 16-byte store.
fn simd_hi_from_low_mnem(mnem: &str) -> bool {
    let m = mnem.to_ascii_uppercase();
    let m = m.strip_prefix('V').unwrap_or(&m);
    matches!(m, "PUNPCKLQDQ" | "UNPCKLPD" | "MOVLHPS")
}

// A packed dword value can be scalarized without changing the memory-access
// contract only when each 32-bit lane is naturally aligned.  The aligned move
// forms additionally carry the architectural 16-byte alignment requirement.
fn simd_dword_load_alignment_ok(mnem: &str, target: Address) -> bool {
    let upper = mnem.to_ascii_uppercase();
    let normalized = upper.strip_prefix('V').unwrap_or(&upper);
    match normalized {
        "MOVDQA" | "MOVAPS" => target % 16 == 0,
        "MOVDQU" | "MOVUPS" => target % 4 == 0,
        _ => false,
    }
}

// Exact lane-wise 32-bit operations.  The integer tag crosses the pass
// boundary; rtl_pass maps it back to the corresponding CompCert operation.
// Keeping this small, semantic alphabet is preferable to treating every
// packed mnemonic as if it had dword lanes.
fn simd_dword_binop_kind(mnem: &str) -> Option<i64> {
    let upper = mnem.to_ascii_uppercase();
    let normalized = upper.strip_prefix('V').unwrap_or(&upper);
    match normalized {
        "PADDD" => Some(1),
        "PSUBD" => Some(2),
        "PAND" => Some(3),
        "POR" => Some(4),
        "PXOR" => Some(5),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SimdDwordDefinition {
    Unknown,
    Event(Address),
}

fn chunk_from_mnem(mnem: &str) -> MemoryChunk {
    let m = mnem.to_ascii_uppercase();
    if m.contains("MOVB") || m.ends_with('B') {
        MemoryChunk::MInt8Unsigned
    } else if m.contains("MOVW") || m.ends_with('W') {
        MemoryChunk::MInt16Unsigned
    } else if m.contains("MOVL") || m.ends_with('L') {
        MemoryChunk::MInt32
    } else if m.contains("MOVQ") || m.ends_with('Q') {
        MemoryChunk::MInt64
    } else if m.contains("MOVSS") {
        MemoryChunk::MFloat32
    } else if m.contains("MOVSD") {
        MemoryChunk::MAny64
    }
    // MOVD/VMOVD (not MOVDQA/MOVDQU) is a 32-bit GP<->XMM transfer, sized 32-bit so the float-bits shuffle does not over-read the source's upper half.
    else if m == "MOVD" || m == "VMOVD" {
        MemoryChunk::MInt32
    } else {
        MemoryChunk::MAny64
    }
}

// Like chunk_from_mnem but also handles the sign/zero-extend load spellings; Intel forms carry no source width, so signedness is set here and the 8-vs-16 narrowing comes from the operand width.
fn chunk_from_mnem_ext(mnem: &str) -> MemoryChunk {
    let m = mnem.to_ascii_uppercase();
    if m.contains("MOVZB") {
        MemoryChunk::MInt8Unsigned
    } else if m.contains("MOVSB") {
        MemoryChunk::MInt8Signed
    } else if m.contains("MOVZW") {
        MemoryChunk::MInt16Unsigned
    } else if m.contains("MOVSW") {
        MemoryChunk::MInt16Signed
    } else if m.contains("MOVSXD") {
        MemoryChunk::MInt32
    } else if m.contains("MOVZX") {
        MemoryChunk::MInt8Unsigned
    } else if m.contains("MOVSX") {
        MemoryChunk::MInt8Signed
    } else {
        chunk_from_mnem(mnem)
    }
}

// Narrow a mnemonic-derived chunk to the capstone operand byte width (B5); Intel syntax has no size suffix so chunk_from_mnem defaults to MAny64 and the operand width is authoritative. Preserves sign/float-ness; never widens.
fn refine_chunk_with_size(mc: MemoryChunk, size: usize) -> MemoryChunk {
    let signed = matches!(mc, MemoryChunk::MInt8Signed | MemoryChunk::MInt16Signed);
    match size {
        1 => {
            if signed {
                MemoryChunk::MInt8Signed
            } else {
                MemoryChunk::MInt8Unsigned
            }
        }
        2 => {
            if signed {
                MemoryChunk::MInt16Signed
            } else {
                MemoryChunk::MInt16Unsigned
            }
        }
        // A 4-byte access through a float register is a single (movss); MFloat64 narrows to MFloat32, never to an int chunk.
        4 => {
            if mc == MemoryChunk::MFloat32 || mc == MemoryChunk::MFloat64 {
                MemoryChunk::MFloat32
            } else {
                MemoryChunk::MInt32
            }
        }
        _ => mc,
    }
}

// Integer read/modify/write instructions encode the physical memory width on
// the memory operand.  That decoded width determines both the load/store chunk
// and whether CompCert's integer operation uses its 32- or 64-bit family; a
// register alias or immediate encoding must never widen a CL/AX-sized access.
// Reject decoder widths outside the x86 integer scalar set rather than
// silently treating an unknown width as four bytes.
fn integer_memory_chunk(size: usize) -> Option<MemoryChunk> {
    match size {
        1 => Some(MemoryChunk::MInt8Unsigned),
        2 => Some(MemoryChunk::MInt16Unsigned),
        4 => Some(MemoryChunk::MInt32),
        8 => Some(MemoryChunk::MInt64),
        _ => None,
    }
}

// A load's memory width belongs to its source operand, not to the destination
// register that receives the extended value. Most load rules flow through
// `transl_load` and already preserve that distinction. Direct symbol-backed
// MOV rules bypass that path, so refine their typed destination chunk with the
// source width here. MOVSX/MOVZX also carry signedness in the mnemonic; keep
// that signedness while selecting the 8- or 16-bit source chunk.
fn refine_direct_load_chunk(
    mnem: &str,
    destination_chunk: MemoryChunk,
    source_width: usize,
) -> MemoryChunk {
    let upper = mnem.to_ascii_uppercase();
    let source_chunk = if upper.contains("MOVZ") || upper.contains("MOVS") {
        chunk_from_mnem_ext(mnem)
    } else {
        destination_chunk
    };
    refine_chunk_with_size(source_chunk, source_width)
}

/// Maps SETcc TestCond (CF/ZF unsigned-style) to the float Condition it materializes (A->Cgt, AE->Cge, B->Clt, BE->Cle, E->Ceq, NE->Cnotcompf(Ceq)); returns None for parity/signed conditions a bare float setcc cannot express.
fn fcmp_setcc_condition(tc: TestCond, is_double: bool) -> Option<Condition> {
    let cmp = match tc {
        TestCond::CondA => Comparison::Cgt,
        TestCond::CondAe => Comparison::Cge,
        TestCond::CondB => Comparison::Clt,
        TestCond::CondBe => Comparison::Cle,
        TestCond::CondE => Comparison::Ceq,
        TestCond::CondNe => {
            return Some(if is_double {
                Condition::Cnotcompf(Comparison::Ceq)
            } else {
                Condition::Cnotcompfs(Comparison::Ceq)
            })
        }
        _ => return None,
    };
    Some(if is_double {
        Condition::Ccompf(cmp)
    } else {
        Condition::Ccompfs(cmp)
    })
}

fn recover_signed_divisor(magic: i64, total_shift: i64) -> Option<i64> {
    if magic <= 0 || total_shift < 32 {
        return None;
    }
    let num = 1u128 << total_shift as u32;
    let mag = magic as u128;
    let d = (num + (mag / 2)) / mag; // rounded division
    if d <= 1 || d > i64::MAX as u128 {
        return None;
    }
    // Verify: magic ~= 2^total_shift / d
    let check = num / d;
    if (check as i64 - magic).unsigned_abs() <= 1 {
        Some(d as i64)
    } else {
        None
    }
}

fn recover_signed_divisor_compensating(magic_signed_i32: i64, total_shift: i64) -> Option<i64> {
    if total_shift < 32 || total_shift > 63 {
        return None;
    }
    // magic_signed_i32 came from a 32-bit immediate; interpret as i32 then add 2^32.
    let m_low = (magic_signed_i32 as i32) as i64;
    if m_low >= 0 {
        // Non-compensating already handled by recover_signed_divisor.
        return None;
    }
    let effective = (m_low as i64).wrapping_add(1i64 << 32);
    if effective <= 0 {
        return None;
    }
    let mag = effective as u128;
    let num = 1u128 << total_shift as u32;
    let d = (num + (mag / 2)) / mag;
    if d <= 1 || d > i64::MAX as u128 {
        return None;
    }
    let check = num / d;
    let check_i = check as i64;
    if (check_i - effective).unsigned_abs() <= 1 {
        Some(d as i64)
    } else {
        None
    }
}

fn recover_unsigned_divisor(magic: i64, total_shift: i64, input_width: i64) -> Option<i64> {
    if !matches!(input_width, 32 | 64) || total_shift < input_width || total_shift >= 128 {
        return None;
    }
    let mag = magic as u64 as u128;
    if mag == 0 {
        return None;
    }
    let num = 1u128 << total_shift as u32;
    // The simple lowering q=(n*magic)>>shift requires the upward reciprocal.
    // A downward-rounded multiplier already fails at n=d.  Recover the only
    // possible divisor from ceil(2^shift/d), then prove the quotient identity
    // over the entire unsigned input domain using the exact remainder bound.
    let d = num.checked_add(mag - 1)?.checked_div(mag)?;
    if d <= 1 || d > i64::MAX as u128 {
        return None;
    }
    let scaled = mag.checked_mul(d)?;
    if scaled < num {
        None
    } else {
        let error = scaled - num;
        let max_input = (1u128 << input_width as u32) - 1;
        let final_q = max_input / d;
        let final_r = max_input % d;
        let final_residual = final_q
            .checked_mul(error)?
            .checked_add(final_r.checked_mul(mag)?)?;

        // The end of the last complete quotient interval can have a larger
        // residual than max_input when the domain ends partway through an
        // interval.  These two extrema cover every n=q*d+r because residual
        // is monotone in q and r inside their respective ranges.
        let complete_intervals = (max_input + 1) / d;
        let complete_residual = if complete_intervals == 0 {
            0
        } else {
            (complete_intervals - 1)
                .checked_mul(error)?
                .checked_add((d - 1).checked_mul(mag)?)?
        };
        (final_residual.max(complete_residual) < num).then_some(d as i64)
    }
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct AsmPassProgram;

    relation arg_constrained_as_ptr(Node, RTLReg);
    relation avx_masked_site(Address);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation call_return_reg(Node, RTLReg);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_function_return_type_candidate(Address, ClightType);
    relation emit_goto_target(Address, Node);

    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation func_param_struct_type_candidate(Address, usize, usize);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);

    relation instr_in_function(Node, Address);
    relation is_callee_saved(Mreg);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation main_function(Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_id_to_canonical(usize, usize);

    relation block_in_function(Node, Address);
    relation instr_in_function(Node, Address);


    relation preg_of(Mreg, Preg);
    relation ireg_of(Preg, Ireg);

    preg_of(Mreg::AX, Preg::Ir(Ireg::RAX));
    preg_of(Mreg::BX, Preg::Ir(Ireg::RBX));
    preg_of(Mreg::CX, Preg::Ir(Ireg::RCX));
    preg_of(Mreg::DX, Preg::Ir(Ireg::RDX));
    preg_of(Mreg::SI, Preg::Ir(Ireg::RSI));
    preg_of(Mreg::DI, Preg::Ir(Ireg::RDI));
    preg_of(Mreg::BP, Preg::Ir(Ireg::RBP));
    preg_of(Mreg::R8, Preg::Ir(Ireg::R8));
    preg_of(Mreg::R9, Preg::Ir(Ireg::R9));
    preg_of(Mreg::R10, Preg::Ir(Ireg::R10));
    preg_of(Mreg::R11, Preg::Ir(Ireg::R11));
    preg_of(Mreg::R12, Preg::Ir(Ireg::R12));
    preg_of(Mreg::R13, Preg::Ir(Ireg::R13));
    preg_of(Mreg::R14, Preg::Ir(Ireg::R14));
    preg_of(Mreg::R15, Preg::Ir(Ireg::R15));

    preg_of(Mreg::X0, Preg::Fr(Freg::XMM0));
    preg_of(Mreg::X1, Preg::Fr(Freg::XMM1));
    preg_of(Mreg::X2, Preg::Fr(Freg::XMM2));
    preg_of(Mreg::X3, Preg::Fr(Freg::XMM3));
    preg_of(Mreg::X4, Preg::Fr(Freg::XMM4));
    preg_of(Mreg::X5, Preg::Fr(Freg::XMM5));
    preg_of(Mreg::X6, Preg::Fr(Freg::XMM6));
    preg_of(Mreg::X7, Preg::Fr(Freg::XMM7));
    preg_of(Mreg::X8, Preg::Fr(Freg::XMM8));
    preg_of(Mreg::X9, Preg::Fr(Freg::XMM9));
    preg_of(Mreg::X10, Preg::Fr(Freg::XMM10));
    preg_of(Mreg::X11, Preg::Fr(Freg::XMM11));
    preg_of(Mreg::X12, Preg::Fr(Freg::XMM12));
    preg_of(Mreg::X13, Preg::Fr(Freg::XMM13));
    preg_of(Mreg::X14, Preg::Fr(Freg::XMM14));
    preg_of(Mreg::X15, Preg::Fr(Freg::XMM15));

    preg_of(Mreg::FP0, Preg::ST0);


    ireg_of(Preg::Ir(Ireg::RAX), Ireg::RAX);
    ireg_of(Preg::Ir(Ireg::RBX), Ireg::RBX);
    ireg_of(Preg::Ir(Ireg::RCX), Ireg::RCX);
    ireg_of(Preg::Ir(Ireg::RDX), Ireg::RDX);
    ireg_of(Preg::Ir(Ireg::RSI), Ireg::RSI);
    ireg_of(Preg::Ir(Ireg::RDI), Ireg::RDI);
    ireg_of(Preg::Ir(Ireg::RBP), Ireg::RBP);
    ireg_of(Preg::Ir(Ireg::RSP), Ireg::RSP);
    ireg_of(Preg::Ir(Ireg::R8), Ireg::R8);
    ireg_of(Preg::Ir(Ireg::R9), Ireg::R9);
    ireg_of(Preg::Ir(Ireg::R10), Ireg::R10);
    ireg_of(Preg::Ir(Ireg::R11), Ireg::R11);
    ireg_of(Preg::Ir(Ireg::R12), Ireg::R12);
    ireg_of(Preg::Ir(Ireg::R13), Ireg::R13);
    ireg_of(Preg::Ir(Ireg::R14), Ireg::R14);
    ireg_of(Preg::Ir(Ireg::R15), Ireg::R15);

    relation symbols(Address, Symbol, Symbol);
    relation symbol_size(Address, usize, Symbol);
    relation builtins(Symbol);

    relation func_entry(Symbol, Address);

    relation next(Address, Address);
    relation op_register(Symbol, &'static str);
    relation op_immediate(Symbol, i64, usize);
    relation block_boundaries(Address, Address, Address);
    relation reg_use(Address, Mreg);
    relation reg_def(Address, Mreg);
    relation decoded_reg_def(Address, Mreg);
    relation stack_def(Address, Symbol, i64);
    relation stack_use(Address, Symbol, i64);
    relation stack_def_used(Address, Symbol, i64, Address, Symbol, i64);
    relation flags_and_jump_pair(Address, Address, &'static str);

    // The compare/test node whose flags a SETcc materializes.  The boolean
    // write must live at the SETcc node (its real machine-order position),
    // while RTL resolves the compared operands at this origin node.  Keeping
    // both addresses prevents a scheduled flag-neutral instruction between
    // CMP and SETcc from observing the future boolean value.
    relation setcc_compare_site(Address, Address);

    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);

    relation code_in_block(Address, Address);

    relation block(Address);

    relation ddisasm_cfg_edge(Address, Address, Symbol);
    relation direct_call(Address, Address);

    relation direct_jump(Address, Address);

    relation stack_base_move(Address, Symbol, Symbol);

    // A function has a frame pointer (mov rsp,rbp); when BP is not the frame pointer, BP-relative accesses are regular loads/stores.
    #[local] relation func_has_frame_pointer(Address);
    func_has_frame_pointer(func) <--
        stack_base_move(addr, src, dst),
        if *src == "RSP" && *dst == "RBP",
        instr_in_function(addr, func);

    // The decoder assigns every real/normalized instruction to a basic block,
    // and function inference assigns blocks by CFG reachability.  Preserve all
    // owners of a shared block.  Do not extend ownership along `next`: that
    // relation is physical instruction adjacency and can cross a function
    // boundary.  Synthetic RTL nodes are introduced later and inherit their
    // producer's owner in rtl_pass.
    instr_in_function(addr, func) <--
        block_in_function(blockaddr, func),
        code_in_block(addr, blockaddr);


    relation pcast(Address, Symbol, Symbol);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CQO", src, dst, _, _, _, _);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CDQ", src, dst, _, _, _, _);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CWD", src, dst, _, _, _, _);


    relation pmov(Address, Symbol, Symbol);
    pmov(addr, dst, src)<--
        instruction(addr, _, _, "MOV", src, dst, _, _, _, _);

    pmov(addr, dst, src)<--
        instruction(addr, _, _, "MOVZX", src, dst, _, _, _, _);

    pmov(addr, dst, src) <--
        instruction(addr, _, _, "MOVSX", src, dst, _, _, _, _);
    pmov(addr, dst, src) <--
        instruction(addr, _, _, "MOVSXD", src, dst, _, _, _, _);

    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVAPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVAPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVUPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVUPS", src, dst, _, _, _, _);
    // Packed-double reg moves (double counterpart of MOVAPS/MOVUPS): absent from pmov, a reg-reg movapd produced no mach_inst, leaving dst undefined and silently dropping the double dataflow through it (e.g. an XMM copy feeding fabs(p1-p2)).
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVAPD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVAPD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVUPD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVUPD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVDQA", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVDQA", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVDQU", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVDQU", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVQ", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVQ", src, dst, _, _, _, _);
    // MOVD is the 32-bit GP<->XMM transfer of the float-bits shuffle; absent from the move list and excluded from ALU lowering, it produced no instruction and the float value became 0.
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVSD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVSD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVSS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVSS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVABS", src, dst, _, _, _, _);

    // Scalar dword -> XMM, PSHUFD $0, then a 16-byte vector store is the
    // compiler's ordinary four-lane integer broadcast.  The point-keyed CFG
    // lattice below recognizes this even across independent instructions.
    relation simd_dword_broadcast_store(Address, Address, &'static str, &'static str, i64, i64, Mreg);

    // Event-time packed-dword provenance consumed by rtl_pass.  kind 0 is a
    // four-lane global load; kinds 1..5 are the operations documented by
    // simd_dword_binop_kind.  `input` names the preceding vector-definition
    // event, and `target` names the memory operand read at THIS event.  The
    // frame-store relation points at the final definition without moving any
    // memory read to the later spill.
    relation simd_dword_lane_event(Address, i64, Address, Address);
    relation simd_dword_lane_frame_store(Address, i64, Address);


    relation pand(Address, Symbol, Symbol);
    pand(addr, dst, src)<--
        instruction(addr, _, _, "AND", src, dst, _, _, _, _);
    // Atomic RMW: capstone glues the lock prefix onto the mnemonic, so the bare-mnemonic rule never fires; the memory-dest lowering is identical to the non-atomic load-op-store.
    pand(addr, dst, src)<--
        instruction(addr, _, _, "LOCK AND", src, dst, _, _, _, _);

    relation psetcc(Address, TestCond, Symbol);
    psetcc(addr, TestCond::CondNp, dst)<--
        instruction(addr, _, _, "SETNP", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondP, dst)<--
        instruction(addr, _, _, "SETP", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondE, dst)<--
        instruction(addr, _, _, "SETE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondNe, dst)<--
        instruction(addr, _, _, "SETNE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondB, dst)<--
        instruction(addr, _, _, "SETB", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondBe, dst)<--
        instruction(addr, _, _, "SETBE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondAe, dst)<--
        instruction(addr, _, _, "SETAE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondA, dst)<--
        instruction(addr, _, _, "SETA", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "SETL", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondLe, dst)<--
        instruction(addr, _, _, "SETLE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "SETGE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondG, dst)<--
        instruction(addr, _, _, "SETG", dst, _, _, _, _, _);

    relation pxor(Address, Symbol, Symbol);
    pxor(addr, dst, src)<--
        instruction(addr, _, _, "XOR", src, dst, _, _, _, _);

    pxor(addr, dst, src)<--
        instruction(addr, _, _, "XORL", src, dst, _, _, _, _);
    pxor(addr, dst, src)<--
        instruction(addr, _, _, "LOCK XOR", src, dst, _, _, _, _);

    // Bit-test-and-modify with an immediate index, modelled as a masked bitwise op (BTC xor, BTS or, BTR and-not); BT is excluded since it writes no register and a fabricated def would corrupt dataflow.
    relation pbtc(Address, Symbol, Symbol);
    pbtc(addr, dst, src)<--
        instruction(addr, _, _, "BTC", src, dst, _, _, _, _);

    relation pbts(Address, Symbol, Symbol);
    pbts(addr, dst, src)<--
        instruction(addr, _, _, "BTS", src, dst, _, _, _, _);

    relation pbtr(Address, Symbol, Symbol);
    pbtr(addr, dst, src)<--
        instruction(addr, _, _, "BTR", src, dst, _, _, _, _);

    // Address of a genuinely-packed SIMD op: these produce no mach_inst, so this flag is the only surviving trace, plumbed downstream so structuring can recognize an auto-vectorized loop.
    relation packed_alu_addr(Address);
    packed_alu_addr(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if is_packed_alu_mnem(mnem);

    relation por(Address, Symbol, Symbol);
    por(addr, dst, src)<--
        instruction(addr, _, _, "OR", src, dst, _, _, _, _);
    por(addr, dst, src)<--
        instruction(addr, _, _, "LOCK OR", src, dst, _, _, _, _);

    relation pneg(Address, Symbol);
    pneg(addr, dst)<--
        instruction(addr, _, _, "NEG", dst, _, _, _, _, _);

    relation psub(Address, Symbol, Symbol);
    psub(addr, dst, src)<--
        instruction(addr, _, _, "SUB", src, dst, _, _, _, _);
    psub(addr, dst, src)<--
        instruction(addr, _, _, "LOCK SUB", src, dst, _, _, _, _);

    relation padd(Address, Symbol, Symbol);
    padd(addr, dst, src)<--
        instruction(addr, _, _, "ADD", src, dst, _, _, _, _);
    padd(addr, dst, src)<--
        instruction(addr, _, _, "LOCK ADD", src, dst, _, _, _, _);

    relation pjcc(Address, TestCond, Symbol);
    pjcc(addr, TestCond::CondNp, dst)<--
        instruction(addr, _, _, "JNP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondP, dst)<--
        instruction(addr, _, _, "JP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondE, dst)<--
        instruction(addr, _, _, "JE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondNe, dst)<--
        instruction(addr, _, _, "JNE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondB, dst)<--
        instruction(addr, _, _, "JB", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondBe, dst)<--
        instruction(addr, _, _, "JBE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondAe, dst)<--
        instruction(addr, _, _, "JAE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondA, dst)<--
        instruction(addr, _, _, "JA", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "JL", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondLe, dst)<--
        instruction(addr, _, _, "JLE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "JGE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondG, dst)<--
        instruction(addr, _, _, "JG", dst, _, _, _, _, _);

    // OF-only branches are intentionally separate from comparison JCCs.
    // Generic CMP/TEST/SUB consumers interpret `pjcc` through CompCert
    // comparisons, while JO/JNO require the exact flags producer semantics.
    #[local] relation overflow_jcc(Address, TestCond, Symbol);
    overflow_jcc(addr, TestCond::CondO, dst)<--
        instruction(addr, _, _, "JO", dst, _, _, _, _, _);
    overflow_jcc(addr, TestCond::CondNo, dst)<--
        instruction(addr, _, _, "JNO", dst, _, _, _, _, _);

    relation pcmp(Address, Symbol, Symbol);
    pcmp(addr, dst, src)<--
        instruction(addr, _, _, "CMP", src, dst, _, _, _, _);

    #[local] relation pcmov(Address, TestCond, Symbol, Symbol);

    pcmov(addr, TestCond::CondE, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVE" || *inst == "CMOVZ";

    pcmov(addr, TestCond::CondNe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVNE" || *inst == "CMOVNZ";

    pcmov(addr, TestCond::CondB, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVB" || *inst == "CMOVC" || *inst == "CMOVNAE";

    pcmov(addr, TestCond::CondAe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVAE" || *inst == "CMOVNC" || *inst == "CMOVNB";

    pcmov(addr, TestCond::CondBe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVBE" || *inst == "CMOVNA";

    pcmov(addr, TestCond::CondA, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVA" || *inst == "CMOVNBE";

    pcmov(addr, TestCond::CondL, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVL" || *inst == "CMOVNGE";

    pcmov(addr, TestCond::CondGe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVGE" || *inst == "CMOVNL";

    pcmov(addr, TestCond::CondLe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVLE" || *inst == "CMOVNG";

    pcmov(addr, TestCond::CondG, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVG" || *inst == "CMOVNLE";

    pcmov(addr, TestCond::CondP, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVP" || *inst == "CMOVPE";

    pcmov(addr, TestCond::CondNp, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVNP" || *inst == "CMOVPO";

    // CMOVS (sign flag set = negative) maps to CondL (same as JS)
    pcmov(addr, TestCond::CondL, dst, src) <--
        instruction(addr, _, _, "CMOVS", src, dst, _, _, _, _);

    // CMOVNS (sign flag clear = non-negative) maps to CondGe (same as JNS)
    pcmov(addr, TestCond::CondGe, dst, src) <--
        instruction(addr, _, _, "CMOVNS", src, dst, _, _, _, _);

    relation pmul(Address, Symbol);
    pmul(addr, dst)<--
        instruction(addr, _, _, "IMUL", dst, "0", _, _, _, _);
    pmul(addr, dst)<--
        instruction(addr, _, _, "MUL", dst, "0", _, _, _, _);

    relation pimul(Address, Symbol, Symbol);
    pimul(addr, dst, src)<--
        instruction(addr, _, _, "IMUL", src, dst, op3, _, _, _),
        if *dst != "0",
        if *op3 == "0";

    // 3-operand IMUL: imul dst, src, imm (dst = src * imm)
    relation pimul3(Address, Symbol, Symbol, Symbol);
    pimul3(addr, dst, src, imm)<--
        instruction(addr, _, _, "IMUL", src, dst, imm, _, _, _),
        if *dst != "0",
        if *imm != "0";

    relation ppush(Address, Symbol);
    ppush(addr, src)<--
        instruction(addr, _, _, "PUSH", src, _, _, _, _, _);

    relation ppop(Address, Symbol);
    ppop(addr, dst)<--
        instruction(addr, _, _, "POP", dst, _, _, _, _, _);

    relation pidiv(Address, Symbol, Symbol);
    pidiv(addr, src, dst)<--
        instruction(addr, _, _, "IDIV", src, dst, _, _, _, _);

    relation pudiv(Address, Symbol, Symbol);
    pudiv(addr, src, dst)<--
        instruction(addr, _, _, "DIV", src, dst, _, _, _, _);

    relation pdiv(Address, Symbol, Symbol);
    pdiv(addr, src, dst) <-- pidiv(addr, src, dst);
    pdiv(addr, src, dst) <-- pudiv(addr, src, dst);

    relation pnot(Address, Symbol);
    pnot(addr, dst)<--
        instruction(addr, _, _, "NOT", dst, _, _, _, _, _);

    relation psal(Address, Symbol, Symbol);
    psal(addr, dst, src)<--
        instruction(addr, _, _, "SAL", src, dst, _, _, _, _);
    psal(addr, dst, src)<--
        instruction(addr, _, _, "SHL", src, dst, _, _, _, _);

    relation psar(Address, Symbol, Symbol);
    psar(addr, dst, src)<--
        instruction(addr, _, _, "SAR", src, dst, _, _, _, _);

    relation pshr(Address, Symbol, Symbol);
    pshr(addr, dst, src)<--
        instruction(addr, _, _, "SHR", src, dst, _, _, _, _);

    relation pror(Address, Symbol, Symbol);
    pror(addr, dst, src)<--
        instruction(addr, _, _, "ROR", src, dst, _, _, _, _);

    relation prol(Address, Symbol, Symbol);
    prol(addr, dst, src)<--
        instruction(addr, _, _, "ROL", src, dst, _, _, _, _);

    relation pmovsd(Address, Symbol, Symbol);
    pmovsd(addr, dst, src)<--
        instruction(addr, _, _, "MOVSD", src, dst, _, _, _, _);
    pmovsd(addr, dst, src)<--
        instruction(addr, _, _, "VMOVSD", src, dst, _, _, _, _);

    relation ppxor(Address, Symbol, Symbol);
    ppxor(addr, dst, src)<--
        instruction(addr, _, _, "PXOR", src, dst, _, _, _, _);
    ppxor(addr, dst, src)<--
        instruction(addr, _, _, "VPXOR", src, dst, _, _, _, _);

    relation pcvtsi2sd(Address, Symbol, Symbol);
    pcvtsi2sd(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSI2SD") || mnemonic.starts_with("VCVTSI2SD");

    relation pcvtsd2si(Address, Symbol, Symbol);
    pcvtsd2si(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSD2SI") || mnemonic.starts_with("CVTTSD2SI")
           || mnemonic.starts_with("VCVTSD2SI") || mnemonic.starts_with("VCVTTSD2SI");

    relation paddsd(Address, Symbol, Symbol);
    paddsd(addr, dst, src)<--
        instruction(addr, _, _, "ADDSD", src, dst, _, _, _, _);

    relation psubsd(Address, Symbol, Symbol);
    psubsd(addr, dst, src)<--
        instruction(addr, _, _, "SUBSD", src, dst, _, _, _, _);

    relation pmulsd(Address, Symbol, Symbol);
    pmulsd(addr, dst, src)<--
        instruction(addr, _, _, "MULSD", src, dst, _, _, _, _);

    relation pdivsd(Address, Symbol, Symbol);
    pdivsd(addr, dst, src)<--
        instruction(addr, _, _, "DIVSD", src, dst, _, _, _, _);

    relation pucomisd(Address, Symbol, Symbol);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "UCOMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "COMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "VUCOMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "VCOMISD", src, dst, _, _, _, _);

    relation pucomiss(Address, Symbol, Symbol);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "UCOMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "COMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "VUCOMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "VCOMISS", src, dst, _, _, _, _);

    relation paddss(Address, Symbol, Symbol);
    paddss(addr, dst, src)<--
        instruction(addr, _, _, "ADDSS", src, dst, _, _, _, _);

    relation psubss(Address, Symbol, Symbol);
    psubss(addr, dst, src)<--
        instruction(addr, _, _, "SUBSS", src, dst, _, _, _, _);

    relation pmulss(Address, Symbol, Symbol);
    pmulss(addr, dst, src)<--
        instruction(addr, _, _, "MULSS", src, dst, _, _, _, _);

    relation pdivss(Address, Symbol, Symbol);
    pdivss(addr, dst, src)<--
        instruction(addr, _, _, "DIVSS", src, dst, _, _, _, _);

    relation pcvtsd2ss(Address, Symbol, Symbol);
    pcvtsd2ss(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if *mnemonic == "CVTSD2SS" || *mnemonic == "VCVTSD2SS";

    relation pcvtss2sd(Address, Symbol, Symbol);
    pcvtss2sd(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if *mnemonic == "CVTSS2SD" || *mnemonic == "VCVTSS2SD";

    relation pcvtsi2ss(Address, Symbol, Symbol);
    pcvtsi2ss(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSI2SS") || mnemonic.starts_with("VCVTSI2SS");

    relation pcvtss2si(Address, Symbol, Symbol);
    pcvtss2si(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSS2SI") || mnemonic.starts_with("CVTTSS2SI")
           || mnemonic.starts_with("VCVTSS2SI") || mnemonic.starts_with("VCVTTSS2SI");

    relation pxorpd(Address, Symbol, Symbol);
    pxorpd(addr, dst, src)<--
        instruction(addr, _, _, "XORPD", src, dst, _, _, _, _);
    pxorpd(addr, dst, src)<--
        instruction(addr, _, _, "VXORPD", src, dst, _, _, _, _);

    relation pandpd(Address, Symbol, Symbol);
    pandpd(addr, dst, src)<--
        instruction(addr, _, _, "ANDPD", src, dst, _, _, _, _);
    pandpd(addr, dst, src)<--
        instruction(addr, _, _, "VANDPD", src, dst, _, _, _, _);

    relation pxorps(Address, Symbol, Symbol);
    pxorps(addr, dst, src)<--
        instruction(addr, _, _, "XORPS", src, dst, _, _, _, _);
    pxorps(addr, dst, src)<--
        instruction(addr, _, _, "VXORPS", src, dst, _, _, _, _);

    relation pandps(Address, Symbol, Symbol);
    pandps(addr, dst, src)<--
        instruction(addr, _, _, "ANDPS", src, dst, _, _, _, _);
    pandps(addr, dst, src)<--
        instruction(addr, _, _, "VANDPS", src, dst, _, _, _, _);

    relation pmaxsd(Address, Symbol, Symbol);
    pmaxsd(addr, dst, src)<--
        instruction(addr, _, _, "MAXSD", src, dst, _, _, _, _);
    pmaxsd(addr, dst, src)<--
        instruction(addr, _, _, "VMAXSD", src, dst, _, _, _, _);

    relation pminsd(Address, Symbol, Symbol);
    pminsd(addr, dst, src)<--
        instruction(addr, _, _, "MINSD", src, dst, _, _, _, _);
    pminsd(addr, dst, src)<--
        instruction(addr, _, _, "VMINSD", src, dst, _, _, _, _);

    relation pmovss(Address, Symbol, Symbol);
    pmovss(addr, dst, src)<--
        instruction(addr, _, _, "MOVSS", src, dst, _, _, _, _);
    pmovss(addr, dst, src)<--
        instruction(addr, _, _, "VMOVSS", src, dst, _, _, _, _);

    relation pswap(Address, Symbol);
    pswap(addr, dst)<--
        instruction(addr, _, _, "BSWAP", dst, _, _, _, _, _);

    relation plabel(Address, Symbol);


    relation phlt(Address);
    phlt(addr) <--
        instruction(addr, _, _, "HLT", _, _, _, _, _, _);

    relation ptest(Address, Symbol, Symbol);
    ptest(addr, dst, src) <--
        instruction(addr, _, _, "TEST", src, dst, _, _, _, _);

    // TEST reg, reg is semantically CMP reg, 0: emit pcmp with a synthesized zero immediate
    pcmp(addr, dst, zero_sym), op_immediate(zero_sym, 0, 0) <--
        ptest(addr, dst, src),
        op_register(dst, r1),
        op_register(src, r2),
        if r1 == r2,
        let zero_sym = Box::leak(format!("__test_zero_{:x}", addr).into_boxed_str()) as &'static str;

    relation pbsr(Address, Symbol, Symbol);
    pbsr(addr, dst, src) <--
        instruction(addr, _, _, "BSR", src, dst, _, _, _, _);

    relation pbsf(Address, Symbol, Symbol);
    pbsf(addr, dst, src) <--
        instruction(addr, _, _, "BSF", src, dst, _, _, _, _);

    relation psqrt(Address, Symbol, Symbol);
    psqrt(addr, dst, src) <--
        instruction(addr, _, _, "SQRTSD", src, dst, _, _, _, _);
    psqrt(addr, dst, src) <--
        instruction(addr, _, _, "VSQRTSD", src, dst, _, _, _, _);

    relation psqrtss(Address, Symbol, Symbol);
    psqrtss(addr, dst, src) <--
        instruction(addr, _, _, "SQRTSS", src, dst, _, _, _, _);
    psqrtss(addr, dst, src) <--
        instruction(addr, _, _, "VSQRTSS", src, dst, _, _, _, _);

    relation psqrtsd(Address, Symbol, Symbol);
    psqrtsd(addr, res, a1) <--
        instruction(addr, _, _, "SQRTPD", a1, res, _, _, _, _);
    psqrtsd(addr, res, a1) <--
        instruction(addr, _, _, "VSQRTPD", a1, res, _, _, _, _);

    relation padc(Address, Symbol, Symbol);
    padc(addr, dst, src)<--
        instruction(addr, _, _, "ADC", src, dst, _, _, _, _);

    relation psbb(Address, Symbol, Symbol);
    psbb(addr, res, a1)<--
        instruction(addr, _, _, "SBB", a1, res, _, _, _, _);

    relation pjmp(Address, Symbol);
    pjmp(addr, dst)<--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "JNS", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "JS", dst, _, _, _, _, _);

    relation plea(Address, Symbol, Symbol);
    plea(addr, dst, src)<--
        instruction(addr, _, _, "LEA", src, dst, _, _, _, _);

    pxor(addr, dst, src)<--
        instruction(addr, _, _, "PXOR", src, dst, _, _, _, _);

    relation unrefinedinstruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation symbol_table(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol);
    relation plt_entry(Address, Symbol);
    relation plt_block(Address, Symbol);
    // Loader-resolved symbol addresses, and the ABI's always-noreturn symbol
    // set from abi_pass; together they identify a call that cannot fall through.
    relation symbol_resolved_addr(Symbol, Address);
    relation is_known_noreturn_function(Symbol);
    relation code_in_refined_block(Address, Address);
    relation code_pointer_in_data(Address, Address);
    // A recovered indirect-jump dispatch is a switch implementation, never a
    // tail call.  Memory JMPs without this positive table classification are
    // preserved below as indirect tail transfers.
    relation jump_table_target(Node, usize, Node);
    // A data slot holding a pointer to a DATA target, from ELF relocations or non-PIE section bytes; the slot is provably a pointer with initializer &target.
    relation pointer_in_data(Address, Address);
    // [start, end) ranges of allocated data sections (pushed by the loader), used to distinguish a genuine no-base absolute/scaled-index data address from a small arithmetic displacement (e.g. `lea 0x8(,%rsi,8)`).
    relation data_section_range(Address, Address);
    // Whether raw linked values are absolute virtual addresses in this image.
    // ELF ET_DYN is false: its in-image pointers require load-base/relocation
    // evidence, so an immediate that merely equals a symbol offset is numeric.
    relation raw_image_addresses_are_absolute(bool);
    // Read-only addresses holding an IEEE-754 sign-clear mask with its width, the positive evidence that lets the reg-reg andps/andpd form lower to Oabsfs/Oabsf.
    relation fp_sign_clear_mask(Address, usize);
    relation pointer_to_external_symbol(Address, Symbol);
    relation global_symbol(Address, Symbol);
    // A global_symbol row that is a synthesized placeholder (SUB_/TABLE_), used to keep a rip-relative indirect call through a mutable function-pointer slot from resolving to a bogus direct call.
    relation synthesized_global_symbol(Address);
    relation arch_bit(i64);
    relation trim_instruction(Address);
    relation vla_alloca(Address, Mreg, Mreg);
    // Legacy MOVHPS preserves the low XMM quadword and loads only the high
    // quadword. Carry its normalized memory operand to RTL, where the second
    // effect is materialized on a private node.
    relation movhps_hi_load(Address, Mreg, &'static str, &'static str, i64, i64, bool);

    relation mach_inst(Address, MachInst);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation func_span(Symbol, Address, Address);
    relation resolved_addr_to_symbol(Address, Ident, i64);
    #[local] relation site_resolved_addr_to_symbol(Address, Address, Ident, i64);

    relation type_size(Typ, u64);
    relation ireg_hold_type(String, Typ);
    relation reg_64(&'static str);
    relation reg_is_64(&'static str, bool);
    relation reg_cx(&'static str);
    relation reg_sp(&'static str);
    relation reg_bp(&'static str);
    relation reg_ip(&'static str);
    relation reg_xmm(&'static str);
    relation type_to_memchunk(Typ, MemoryChunk);
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation rip_target_addr(Address, Address);
    relation abs_target_addr(Address, Address);
    relation is_external_function(Address);
    relation function_symbol(Address, Symbol);
    relation prev_instr(Address, Address);
    relation is_tail_call_jmp(Address);
    relation stack_delta(Address, i64);
    lattice stack_offset(Address, Address, Dual<Set<i64>>);
    relation transl_store_inferred(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation transl_store(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    // Resolution is site-keyed.  Addrmode is a value shape and can recur at an
    // unrelated instruction; a proof at one node must never rewrite another.
    relation addrmode_needs_resolution(Address, Addrmode, Address);
    // (function, access node, physical owner, field byte offset, index stride,
    // index count, bound-defining origin, access width).  This is the compact
    // certificate consumed by global-array recovery after the exact point-
    // keyed bounded-offset lattice has validated `[gpr + absolute-data]`.
    relation bounded_absolute_data_access(Address, Address, Ident, i64, u64, usize, Address, usize);
    relation addr_requiring_symbol(Address);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    // A SETcc whose destination is a scalar frame cell cannot be represented
    // as one Mach instruction: Ocmp produces a register while Mstore consumes
    // one.  Preserve the complete value operation and its exact frame cell for
    // RTL, where the condition can define the cell's canonical SSA identity
    // directly.  (setcc addr, frame offset, flags origin, operation, operands)
    relation mach_stack_setcc(Address, i64, Address, Operation, Arc<Vec<Mreg>>);
    // Carries the size-narrowed MemoryChunk, not a Typ: Typ cannot represent MInt8/MInt16, so an immediate byte store over-widened to 4 bytes and mis-scaled its pointer arithmetic.
    relation mach_imm_indirect_store(Address, i64, MemoryChunk, Mreg, i64);
    // Memory-source arithmetic: load from [base+disp], then apply op with dst_reg.
    relation arith_load_op(Address, Operation, MemoryChunk, Mreg, i64, Mreg);
    // Memory-dest arithmetic with register source: load [base+disp], op with src_reg, store back.
    relation arith_store_reg(Address, Operation, MemoryChunk, Mreg, i64, Mreg);
    // Memory-dest arithmetic with immediate source: load [base+disp], op_imm, store back.
    relation arith_store_imm(Address, Operation, MemoryChunk, Mreg, i64);
    // Absolute addressing arith store: read-modify-write at global symbol address.
    relation arith_store_abs_reg(Address, Operation, MemoryChunk, Ident, i64, Mreg);
    relation arith_store_abs_imm(Address, Operation, MemoryChunk, Ident, i64);
    // Single source of truth for the no-linear-op semantic-operation class
    // (fused mem-arith RMW, immediate indirect/absolute stores, and memory
    // reads materialized only in RTL), which linear_pass keeps self-canonical
    // so a goto cannot thread past one.
    relation node_unlowered_side_effect(Address);
    node_unlowered_side_effect(addr) <-- mach_imm_indirect_store(addr, _, _, _, _);
    node_unlowered_side_effect(addr) <-- arith_load_op(addr, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- arith_store_reg(addr, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- arith_store_imm(addr, _, _, _, _);
    node_unlowered_side_effect(addr) <-- arith_store_abs_reg(addr, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- arith_store_abs_imm(addr, _, _, _, _);
    node_unlowered_side_effect(addr) <-- float_load_op(addr, _, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- float_arith_stack_op(addr, _, _, _, _);
    node_unlowered_side_effect(addr) <-- mach_stack_setcc(addr, _, _, _, _);
    // A memory CMP/TEST is split in RTL into a load at the flag-setting point
    // and a condition at its structurally linked consumer.  It has no Linear
    // instruction of its own, so treating its bare Lbranch as a trampoline
    // skips the load and lets the condition read an uninitialized temporary.
    node_unlowered_side_effect(addr) <-- pcmp(addr, mem, _), op_indirect(mem, _, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- pcmp(addr, _, mem), op_indirect(mem, _, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- ptest(addr, mem, _), op_indirect(mem, _, _, _, _, _, _);
    node_unlowered_side_effect(addr) <-- ptest(addr, _, mem), op_indirect(mem, _, _, _, _, _, _);
    relation transl_load_inferred(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation transl_load(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation expand_builtin_inline(Address, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>);
    relation expand_builtin_va_start_32(Address, Ireg);
    relation pallocframe(Address, i64);
    relation pallocframe_by_func(Symbol, Address, i64);

    type_size(Typ::Tint, 4);
    type_size(Typ::Tfloat, 8);
    type_size(Typ::Tsingle, 4);
    type_size(Typ::Tany32, 4);

    type_size(Typ::Tlong, 8) <-- arch_bit(64);
    type_size(Typ::Tany64, 8) <-- arch_bit(64);

    // 64-bit registers use Tany64 (not Tlong) to let downstream type inference determine the actual type from usage context.
    ireg_hold_type("RAX".to_string(), Typ::Tany64);
    ireg_hold_type("RBX".to_string(), Typ::Tany64);
    ireg_hold_type("RCX".to_string(), Typ::Tany64);
    ireg_hold_type("RDX".to_string(), Typ::Tany64);
    ireg_hold_type("RSI".to_string(), Typ::Tany64);
    ireg_hold_type("RDI".to_string(), Typ::Tany64);
    ireg_hold_type("RBP".to_string(), Typ::Tany64);
    ireg_hold_type("RSP".to_string(), Typ::Tany64);
    ireg_hold_type("R8".to_string(), Typ::Tany64);
    ireg_hold_type("R9".to_string(), Typ::Tany64);
    ireg_hold_type("R10".to_string(), Typ::Tany64);
    ireg_hold_type("R11".to_string(), Typ::Tany64);
    ireg_hold_type("R12".to_string(), Typ::Tany64);
    ireg_hold_type("R13".to_string(), Typ::Tany64);
    ireg_hold_type("R14".to_string(), Typ::Tany64);
    ireg_hold_type("R15".to_string(), Typ::Tany64);
    reg_64("RAX"); reg_64("RBX"); reg_64("RCX"); reg_64("RDX");
    reg_64("RSI"); reg_64("RDI"); reg_64("RBP"); reg_64("RSP");
    reg_64("R8");  reg_64("R9");  reg_64("R10"); reg_64("R11");
    reg_64("R12"); reg_64("R13"); reg_64("R14"); reg_64("R15");
    reg_is_64("RAX", true); reg_is_64("RBX", true); reg_is_64("RCX", true); reg_is_64("RDX", true);
    reg_is_64("RSI", true); reg_is_64("RDI", true); reg_is_64("RBP", true); reg_is_64("RSP", true);
    reg_is_64("R8", true);  reg_is_64("R9", true);  reg_is_64("R10", true); reg_is_64("R11", true);
    reg_is_64("R12", true); reg_is_64("R13", true); reg_is_64("R14", true); reg_is_64("R15", true);
    reg_is_64("EAX", false); reg_is_64("EBX", false); reg_is_64("ECX", false); reg_is_64("EDX", false);
    reg_is_64("ESI", false); reg_is_64("EDI", false); reg_is_64("EBP", false); reg_is_64("ESP", false);
    reg_is_64("R8D", false); reg_is_64("R9D", false); reg_is_64("R10D", false); reg_is_64("R11D", false);
    reg_is_64("R12D", false); reg_is_64("R13D", false); reg_is_64("R14D", false); reg_is_64("R15D", false);
    // 16- and 8-bit sub-registers are sub-64-bit: without these facts every reg_is_64 join silently fails for a byte operand, so the CMP+CMOV/SETcc Osel never forms and the value chain is DCE'd.
    reg_is_64("AX", false); reg_is_64("BX", false); reg_is_64("CX", false); reg_is_64("DX", false);
    reg_is_64("SI", false); reg_is_64("DI", false); reg_is_64("BP", false); reg_is_64("SP", false);
    reg_is_64("R8W", false); reg_is_64("R9W", false); reg_is_64("R10W", false); reg_is_64("R11W", false);
    reg_is_64("R12W", false); reg_is_64("R13W", false); reg_is_64("R14W", false); reg_is_64("R15W", false);
    reg_is_64("AL", false); reg_is_64("BL", false); reg_is_64("CL", false); reg_is_64("DL", false);
    reg_is_64("AH", false); reg_is_64("BH", false); reg_is_64("CH", false); reg_is_64("DH", false);
    reg_is_64("SIL", false); reg_is_64("DIL", false); reg_is_64("BPL", false); reg_is_64("SPL", false);
    reg_is_64("R8B", false); reg_is_64("R9B", false); reg_is_64("R10B", false); reg_is_64("R11B", false);
    reg_is_64("R12B", false); reg_is_64("R13B", false); reg_is_64("R14B", false); reg_is_64("R15B", false);
    reg_cx("RCX"); reg_cx("ECX"); reg_cx("CX"); reg_cx("CL"); reg_cx("CH");
    reg_sp("RSP"); reg_sp("ESP"); reg_sp("SP"); reg_sp("SPL");
    reg_bp("RBP"); reg_bp("EBP"); reg_bp("BP"); reg_bp("BPL");
    reg_ip("RIP"); reg_ip("EIP"); reg_ip("IP");
    reg_xmm("XMM0"); reg_xmm("XMM1"); reg_xmm("XMM2"); reg_xmm("XMM3");
    reg_xmm("XMM4"); reg_xmm("XMM5"); reg_xmm("XMM6"); reg_xmm("XMM7");
    reg_xmm("XMM8"); reg_xmm("XMM9"); reg_xmm("XMM10"); reg_xmm("XMM11");
    reg_xmm("XMM12"); reg_xmm("XMM13"); reg_xmm("XMM14"); reg_xmm("XMM15");
    // YMM registers alias to their XMM counterparts for scalarization
    reg_xmm("YMM0"); reg_xmm("YMM1"); reg_xmm("YMM2"); reg_xmm("YMM3");
    reg_xmm("YMM4"); reg_xmm("YMM5"); reg_xmm("YMM6"); reg_xmm("YMM7");
    reg_xmm("YMM8"); reg_xmm("YMM9"); reg_xmm("YMM10"); reg_xmm("YMM11");
    reg_xmm("YMM12"); reg_xmm("YMM13"); reg_xmm("YMM14"); reg_xmm("YMM15");
    ireg_hold_type("EAX".to_string(), Typ::Tint);
    ireg_hold_type("EBX".to_string(), Typ::Tint);
    ireg_hold_type("ECX".to_string(), Typ::Tint);
    ireg_hold_type("EDX".to_string(), Typ::Tint);
    ireg_hold_type("ESI".to_string(), Typ::Tint);
    ireg_hold_type("EDI".to_string(), Typ::Tint);
    ireg_hold_type("EBP".to_string(), Typ::Tint);
    ireg_hold_type("ESP".to_string(), Typ::Tint);
    ireg_hold_type("R8D".to_string(), Typ::Tint);
    ireg_hold_type("R9D".to_string(), Typ::Tint);
    ireg_hold_type("R10D".to_string(), Typ::Tint);
    ireg_hold_type("R11D".to_string(), Typ::Tint);
    ireg_hold_type("R12D".to_string(), Typ::Tint);
    ireg_hold_type("R13D".to_string(), Typ::Tint);
    ireg_hold_type("R14D".to_string(), Typ::Tint);
    ireg_hold_type("R15D".to_string(), Typ::Tint);
    // XMM registers use Tany64, not Tfloat: floatness is a property of the INSTRUCTION, and gcc uses XMM as 16-byte block movers, so Tfloat made struct recovery emit double fields for pointer data.
    ireg_hold_type("XMM0".to_string(), Typ::Tany64);
    ireg_hold_type("XMM1".to_string(), Typ::Tany64);
    ireg_hold_type("XMM2".to_string(), Typ::Tany64);
    ireg_hold_type("XMM3".to_string(), Typ::Tany64);
    ireg_hold_type("XMM4".to_string(), Typ::Tany64);
    ireg_hold_type("XMM5".to_string(), Typ::Tany64);
    ireg_hold_type("XMM6".to_string(), Typ::Tany64);
    ireg_hold_type("XMM7".to_string(), Typ::Tany64);
    ireg_hold_type("XMM8".to_string(), Typ::Tany64);
    ireg_hold_type("XMM9".to_string(), Typ::Tany64);
    ireg_hold_type("XMM10".to_string(), Typ::Tany64);
    ireg_hold_type("XMM11".to_string(), Typ::Tany64);
    ireg_hold_type("XMM12".to_string(), Typ::Tany64);
    ireg_hold_type("XMM13".to_string(), Typ::Tany64);
    ireg_hold_type("XMM14".to_string(), Typ::Tany64);
    ireg_hold_type("XMM15".to_string(), Typ::Tany64);
    ireg_hold_type("FP0".to_string(), Typ::Tfloat);
    ireg_hold_type("FP1".to_string(), Typ::Tfloat);
    ireg_hold_type("FP2".to_string(), Typ::Tfloat);
    ireg_hold_type("FP3".to_string(), Typ::Tfloat);
    ireg_hold_type("FP4".to_string(), Typ::Tfloat);
    ireg_hold_type("FP5".to_string(), Typ::Tfloat);
    ireg_hold_type("FP6".to_string(), Typ::Tfloat);
    ireg_hold_type("FP7".to_string(), Typ::Tfloat);
    ireg_hold_type("AX".to_string(), Typ::Tint);
    ireg_hold_type("BX".to_string(), Typ::Tint);
    ireg_hold_type("CX".to_string(), Typ::Tint);
    ireg_hold_type("DX".to_string(), Typ::Tint);
    ireg_hold_type("SI".to_string(), Typ::Tint);
    ireg_hold_type("DI".to_string(), Typ::Tint);
    ireg_hold_type("BP".to_string(), Typ::Tint);
    ireg_hold_type("SP".to_string(), Typ::Tint);
    ireg_hold_type("R8W".to_string(), Typ::Tint);
    ireg_hold_type("R9W".to_string(), Typ::Tint);
    ireg_hold_type("R10W".to_string(), Typ::Tint);
    ireg_hold_type("R11W".to_string(), Typ::Tint);
    ireg_hold_type("R12W".to_string(), Typ::Tint);
    ireg_hold_type("R13W".to_string(), Typ::Tint);
    ireg_hold_type("R14W".to_string(), Typ::Tint);
    ireg_hold_type("R15W".to_string(), Typ::Tint);
    ireg_hold_type("AL".to_string(), Typ::Tint);
    ireg_hold_type("BL".to_string(), Typ::Tint);
    ireg_hold_type("CL".to_string(), Typ::Tint);
    ireg_hold_type("DL".to_string(), Typ::Tint);
    ireg_hold_type("SIL".to_string(), Typ::Tint);
    ireg_hold_type("DIL".to_string(), Typ::Tint);
    ireg_hold_type("BPL".to_string(), Typ::Tint);
    ireg_hold_type("SPL".to_string(), Typ::Tint);
    ireg_hold_type("R8B".to_string(), Typ::Tint);
    ireg_hold_type("R9B".to_string(), Typ::Tint);
    ireg_hold_type("R10B".to_string(), Typ::Tint);
    ireg_hold_type("R11B".to_string(), Typ::Tint);
    ireg_hold_type("R12B".to_string(), Typ::Tint);
    ireg_hold_type("R13B".to_string(), Typ::Tint);
    ireg_hold_type("R14B".to_string(), Typ::Tint);
    ireg_hold_type("R15B".to_string(), Typ::Tint);
    ireg_hold_type("AH".to_string(), Typ::Tint);
    ireg_hold_type("BH".to_string(), Typ::Tint);
    ireg_hold_type("CH".to_string(), Typ::Tint);
    ireg_hold_type("DH".to_string(), Typ::Tint);

    type_to_memchunk(Typ::Tint, MemoryChunk::MInt32);
    type_to_memchunk(Typ::Tlong, MemoryChunk::MInt64);
    type_to_memchunk(Typ::Tfloat, MemoryChunk::MFloat64);
    type_to_memchunk(Typ::Tsingle, MemoryChunk::MFloat32);
    type_to_memchunk(Typ::Tany32, MemoryChunk::MAny32);
    type_to_memchunk(Typ::Tany64, MemoryChunk::MAny64);

    resolved_addr_to_symbol(addr, ident, 0) <--
        symbols(addr, _, _),
        let ident = *addr as Ident;

    // Positive evidence for immediate -> &symbol: the exact symbol is inside a
    // loaded data section and this image represents linked addresses as raw
    // absolute values. Generic `symbols` also contains inferred FUN_/L_ code
    // labels, while ET_DYN offsets can freely collide with integer literals;
    // neither is pointer evidence by itself.
    #[local] relation immediate_nonzero_data_symbol(Address);
    immediate_nonzero_data_symbol(addr) <--
        raw_image_addresses_are_absolute(raw_absolute),
        if *raw_absolute,
        symbols(addr, _, _),
        data_section_range(start, end),
        if *addr != 0,
        if *addr >= *start && *addr < *end;

    resolved_addr_to_symbol(immediate_addr, ident, offset) <--
        addr_requiring_symbol(immediate_addr),
        func_span(_, start, end),
        if *immediate_addr >= *start,
        if *immediate_addr < *end,
        let ident = *start as Ident,
        let offset = (*immediate_addr - *start) as i64;

    resolved_addr_to_symbol(plt_addr, ident, 0) <--
        plt_entry(plt_addr, _),
        let ident = *plt_addr as Ident;


    rip_target_addr(addr, target) <--
        plea(addr, _, am),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        pmov(addr, _, am),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        pmov(addr, am, _),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    // RIP-relative target for comiss/ucomiss/comisd/ucomisd with memory operand
    rip_target_addr(addr, target) <--
        pucomiss(addr, _, src),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(src, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        pucomisd(addr, _, src),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(src, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    // Generic RIP-relative catch-all for instructions with a RIP-relative operand.
    rip_target_addr(addr, target) <--
        instruction(addr, size, _, _, op1, _, _, _, _, _),
        op_indirect(op1, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        instruction(addr, size, _, _, _, op2, _, _, _, _),
        op_indirect(op2, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    // Absolute addressing (clang -fno-pie): base="NONE", no index, displacement IS the address
    abs_target_addr(addr, target) <--
        pmov(addr, _, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pmov(addr, am, _),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        plea(addr, _, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pucomiss(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pucomisd(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    // Absolute addressing for padd/psub (arith_store patterns)
    abs_target_addr(addr, target) <--
        padd(addr, dst, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        psub(addr, dst, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    // Absolute addressing for padd/psub memory-SOURCE direction (`add 0x404024,%eax`, 3.8c)
    abs_target_addr(addr, target) <--
        padd(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        psub(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pand(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        por(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pxor(addr, _, src),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    // Absolute addressing for the float/SSE memory-source op family (addsd/mulss/... 0x..., 3.8a)
    abs_target_addr(addr, target) <--
        float_mem_op_raw(addr, _, _, src, _, _),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    // Scaled-index absolute addressing (clang const-table load): the displacement must land in a real data section, since a small arithmetic displacement is an index computation, not a table base.
    abs_target_addr(addr, target) <--
        pmov(addr, _, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address,
        data_section_range(start, end),
        if target >= *start && target < *end;

    // Absolute memory-indirect calls need the same global/table-base naming as
    // ordinary absolute loads.  Without these facts a base-less unresolved
    // CALL survives as Mach control flow but has no addressable callee load.
    abs_target_addr(addr, target) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address,
        data_section_range(start, end),
        if target >= *start && target < *end;

    abs_target_addr(addr, target) <--
        pmov(addr, am, _),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address,
        data_section_range(start, end),
        if target >= *start && target < *end;

    abs_target_addr(addr, target) <--
        plea(addr, _, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address,
        data_section_range(start, end),
        if target >= *start && target < *end;

    resolved_addr_to_symbol(target, ident, 0) <--
        rip_target_addr(_, target),
        symbols(target, _, _),
        let ident = *target as Ident;

    resolved_addr_to_symbol(target, ident, offset) <--
        rip_target_addr(_, target),
        func_span(_, start, end),
        if *target >= *start && *target < *end,
        let ident = *start as Ident,
        let offset = (target - start) as i64;

    // Symbol resolution for absolute addressing targets
    resolved_addr_to_symbol(target, ident, 0) <--
        abs_target_addr(_, target),
        symbols(target, _, _),
        let ident = *target as Ident;

    resolved_addr_to_symbol(target, ident, offset) <--
        abs_target_addr(_, target),
        func_span(_, start, end),
        if *target >= *start && *target < *end,
        let ident = *start as Ident,
        let offset = (target - start) as i64;


    plt_entry(addr, name) <--
        symbol_table(addr, _, _, _, _, _, section_name, _, name),
        if *section_name == ".plt" || *section_name == ".plt.got";

    is_external_function(addr) <-- plt_entry(addr, _);
    is_external_function(addr) <-- plt_block(addr, _);

    is_external_function(addr) <--
        symbol_table(addr, _, sym_type, _, _, _, section_name, _, _),
        if *sym_type == "FUNC",
        if *section_name == ".init" || *section_name == ".fini";

    function_symbol(addr, name) <--
        symbol_table(addr, _size, _type, _binding, _section_type, _section_idx, _section_name, _name_idx, name),
        if *_binding == "GLOBAL" || *_binding == "LOCAL",
        if *_type == "FUNC",
        if *addr > 0;

    function_symbol(addr, name) <--
        plt_entry(addr, name);

    function_symbol(addr, name) <--
        plt_block(addr, name);

    global_symbol(addr, name) <--
        symbol_table(addr, _size, _type, _binding, _section_type, _section_idx, _section_name, _name_idx, name),
        if *_binding == "GLOBAL" || *_binding == "LOCAL",
        if *_type == "OBJECT",
        if *addr > 0;

    global_symbol(target_addr, name_sym), synthesized_global_symbol(target_addr) <--
        rip_target_addr(_, target_addr),
        if *target_addr > 0,
        !symbol_table(target_addr, _, _, _, _, _, _, _, _),
        !function_symbol(target_addr, _),
        !plt_entry(target_addr, _),
        !func_entry(_, target_addr),
        let name_string = format!("SUB_{:x}", target_addr),
        let name_sym = Box::leak(name_string.into_boxed_str()) as &'static str;

    // Synthesise a global symbol for absolute-addressed targets (clang -fno-pie const-table loads) so the table base resolves to Aglobal instead of `&0`.
    global_symbol(target_addr, name_sym), synthesized_global_symbol(target_addr) <--
        abs_target_addr(_, target_addr),
        if *target_addr > 0,
        !symbol_table(target_addr, _, _, _, _, _, _, _, _),
        !function_symbol(target_addr, _),
        !plt_entry(target_addr, _),
        !func_entry(_, target_addr),
        let name_string = format!("TABLE_{:x}", target_addr),
        let name_sym = Box::leak(name_string.into_boxed_str()) as &'static str;

    // Create one anonymous physical owner for every certified bounded-index
    // family, not one symbol per field coordinate.  Interior fields remain
    // byte offsets of this owner in `bounded_absolute_data_access`.
    global_symbol(owner_address, name_sym), synthesized_global_symbol(owner_address) <--
        bounded_absolute_data_access(_, _, owner, _, _, _, _, _),
        let owner_address = *owner as Address,
        if owner_address > 0,
        !symbol_table(owner_address, _, _, _, _, _, _, _, _),
        !function_symbol(owner_address, _),
        !plt_entry(owner_address, _),
        !func_entry(_, owner_address),
        let name_string = format!("TABLE_{:x}", owner_address),
        let name_sym = Box::leak(name_string.into_boxed_str()) as &'static str;

    symbols(addr, name, name) <--
        function_symbol(addr, name);

    symbols(addr, name, name) <--
        global_symbol(addr, name);


    instruction(addr, size, mnemonic, dst, src1, src2, src3, src4, prefix, suffix) <--
        unrefinedinstruction(addr, size, mnemonic, dst, src1, src2, src3, src4, prefix, suffix),
        code_in_refined_block(addr, _),
        !trim_instruction(addr);

    mach_inst(addr, MachInst::Mbuiltin(
        "alloca".to_string(),
        vec![BuiltinArg::BA(*size_mreg)],
        BuiltinArg::BA(*result_mreg),
    )) <--
        vla_alloca(addr, size_mreg, result_mreg);

    mach_inst(addr, MachInst::Mcall(Either::Left(Mreg::x86(Ireg::from(reg_str))))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_register(dst, reg_str);

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Right(*imm_str)))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_immediate(dst, imm_str, _),
        !symbols(*imm_str as Address, _, _);

    // Resolve `call *disp(%rip)` via rip_target_addr to the GOT slot, then to an extern symbol or named symbol, emitting a named direct call so the known extern signature applies (RIP has no GP-reg).
    relation rip_indirect_call_resolved(Address);

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(name)))),
    rip_indirect_call_resolved(*addr) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, _, _),
        reg_ip(*base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        rip_target_addr(addr, target),
        pointer_to_external_symbol(target, name);

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(name)))),
    rip_indirect_call_resolved(*addr) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, _, _),
        reg_ip(*base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        rip_target_addr(addr, target),
        !pointer_to_external_symbol(target, _),
        // Only a REAL named target may become a direct call; a synthesized SUB_/TABLE_ placeholder means a mutable function-pointer slot, so exclude it and fall through to the indirect path.
        !synthesized_global_symbol(*target),
        symbols(*target, name, _);

    // Non-position-independent x86-32 (every PE32, and ELF -fno-pie) spells the same import slot ABSOLUTELY -- `call dword ptr [0x4020dc]` -- with no base or index and the slot address in the displacement. Without this the operand has no base register, so the fallback below cannot fire either and the call is dropped outright.
    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(name)))),
    rip_indirect_call_resolved(*addr) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        pointer_to_external_symbol(*disp as Address, name);

    // Register-indirect (`call *%rax`) and unresolved RIP-relative calls fall back to Mcall(Left(base)); resolvable RIP slots are handled above and excluded here so no call is dropped.
    mach_inst(addr, MachInst::Mcall(Either::Left(Mreg::x86(Ireg::from(base_str))))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, _, _, _, _),
        if base_str != &"NONE",
        !rip_indirect_call_resolved(*addr);

    // Absolute/index-only memory calls have no architectural base register.
    // Preserve the semantic Lcall with an explicit placeholder; rtl_pass uses
    // the raw memory operand to replace it with an Eload callee.
    mach_inst(addr, MachInst::Mcall(Either::Left(Mreg::Unknown))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, _, _, _, _),
        if *base_str == "NONE" || base_str.is_empty(),
        !rip_indirect_call_resolved(*addr);


    prev_instr(next_addr, curr_addr) <-- next(curr_addr, next_addr);

    mach_inst(addr, MachInst::Mtailcall(Either::Left(Mreg::x86(Ireg::from(reg_str))))),
    reg_use(addr, Mreg::x86(Ireg::from(reg_str))) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, dst),
        op_register(dst, reg_str);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Right(*imm_str)))) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, dst),
        op_immediate(dst, imm_str, _),
        // Require a real function-entry target: an `L_<addr>` label (e.g. shared epilogue) is not a tailcall and would fabricate a call to an undefined `L_<addr>()` (S5).
        func_entry(_, *imm_str as u64);


    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))), plabel(addr1, sym) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, sym),
        op_indirect(sym, _, _, _, _, _, _);

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        func_entry(_, target_addr_addr),
        if *target_addr as u64 == *target_addr_addr,
        // ASM-4: a JMP to its own function's entry is an intra-function jump, not a tail call; excluded via structural CFG containment so it becomes Mgoto.
        !jmp_target_in_own_func(addr);

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        next(addr, next_addr),
        !instr_in_function(next_addr, func),
        // Exclude intra-function jumps (loop back-edges at function boundaries are not tail calls).
        !instr_in_function(*target_addr as u64, func),
        // Require a real function-entry target: an `L_<addr>` label (e.g. landing-pad continuation) is not a tailcall and lets the JMP fall through to Mgoto instead of an undefined `L_<addr>()` (S5).
        func_entry(_, *target_addr as u64);

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        func_entry(_, target_func),
        if *target_addr as u64 == *target_func,
        if *target_func != *func;

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", _, _, _, _, _, _),
        plt_entry(addr, _);

    // Forwarder thunk (mov args; jmp <plt_stub>): the stub is not a func_entry, so classify a JMP-to-extern as its own tail-call kind or the body collapses to goto <sym> and the function is dropped.
    relation is_extern_tailcall_jmp(Address);
    // PE import thunks end in jmp qword ptr [rip+IAT]; resolve the slot like the indirect CALL path so the thunk becomes a named tail call and inherits the extern signature.
    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(name)))),
    is_extern_tailcall_jmp(*addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, _, _),
        reg_ip(*base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        rip_target_addr(addr, target),
        pointer_to_external_symbol(target, name);

    // The x86-32 spelling of the same import thunk: `jmp dword ptr [0x4020dc]`, absolute rather than RIP-relative.
    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(name)))),
    is_extern_tailcall_jmp(*addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        pointer_to_external_symbol(*disp as Address, name);

    is_extern_tailcall_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        plt_block(*target_addr as u64, _);
    is_extern_tailcall_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        plt_entry(*target_addr as u64, _);
    is_extern_tailcall_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        is_external_function(*target_addr as u64);

    // An unresolved memory-indirect JMP is the memory spelling of an indirect
    // tail call.  Recovered switch dispatchers carry jump_table_target facts
    // and are deliberately excluded; import thunks were resolved to a named
    // target above and are excluded as well.  Mreg::Unknown is only a Mach
    // placeholder -- rtl_pass reconstructs the exact base/index/scale/disp
    // from the retained operand and emits an explicit function-pointer load.
    relation is_memory_tailcall_jmp(Address);
    mach_inst(addr, MachInst::Mtailcall(Either::Left(Mreg::Unknown))),
    is_memory_tailcall_jmp(*addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_indirect(dst, _, _, index, _, _, _),
        // An unresolved indexed memory jump remains a possible switch table
        // even when target recovery declined it. Do not turn that ambiguity
        // into a call; the load-backed tail family is the unindexed vtable/GOT
        // spelling.
        if *index == "NONE" || index.is_empty(),
        !jump_table_target(addr, _, _),
        !is_extern_tailcall_jmp(addr);

    // A direct JMP landing back inside its own function is an intra-function jump, never a tail call; exposed so the mach-level restore-then-goto heuristic cannot fabricate an L_<addr>() call.
    relation jmp_target_in_own_func(Address);
    jmp_target_in_own_func(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        instr_in_function(*target_addr as u64, func);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))) <--
        instruction(addr, _, _, "JMP", _, _, _, _, _, _),
        plt_entry(addr, sym);

    // Thunk JMP-to-PLT-stub: emit a named tail call to the extern (symbol form), mirroring the direct-PLT-entry rule above so the same extern signature applies. The stub's plt_block/plt_entry name IS the extern name.
    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        plt_block(*target_addr as u64, sym);
    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        plt_entry(*target_addr as u64, sym);
    // Thunk JMP to a non-PLT extern (.init/.fini FUNC): resolve the target address to its symbol name and emit the named tail call.
    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        is_external_function(*target_addr as u64),
        !plt_block(*target_addr as u64, _),
        !plt_entry(*target_addr as u64, _),
        symbols(*target_addr as u64, sym, _);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Right(*target_addr)))) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        is_tail_call_jmp(addr);

    // Mgoto fallback fires only for a genuine intra-function/structured jump: it must be neither an inter-function tail call (is_tail_call_jmp) nor a thunk JMP-to-extern (is_extern_tailcall_jmp), or the thunk body would collapse to `goto <sym>` and the function would be dropped.
    mach_inst(addr, MachInst::Mgoto(dst)) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        !is_tail_call_jmp(addr),
        !is_extern_tailcall_jmp(addr),
        !is_memory_tailcall_jmp(addr);

    mach_inst(addr, MachInst::Mreturn) <--
        instruction(addr, _, _, "RET", _, _, _, _, _, _);

    // RET imm16 PROVES the callee pops its own stack arguments (stdcall/fastcall/thiscall on Windows x86-32) and states the exact byte count; the RET is tied to its function STRUCTURALLY through instr_in_function, never by address proximity.
    relation func_callee_pop_bytes(Address, i64);
    func_callee_pop_bytes(func, *bytes) <--
        instruction(addr, _, _, "RET", imm, _, _, _, _, _),
        op_immediate(imm, bytes, _),
        if *bytes > 0,
        instr_in_function(addr, func);


    // No-result builtin: BAInt(0) is the canonical empty-result form (matching cminor_pass) so downstream does not synthesize a dst and render `var = __builtin_unreachable()`.
    mach_inst(addr, MachInst::Mbuiltin(
        "__builtin_unreachable".to_string(),
        vec![],
        BuiltinArg::BAInt(0)
    )) <--
        phlt(addr),
        builtins("__builtin_unreachable");


    stack_delta(addr, -(*sz as i64)) <--
        ppush(addr, sym),
        op_register(sym, ireg_r),
        ireg_hold_type(ireg_r.to_string(), typ),
        type_size(typ, sz);

    stack_delta(addr, -(*bits / 8)) <--
        ppush(addr, sym),
        op_immediate(sym, _, _),
        arch_bit(bits);

    // PUSH reads may come from memory as well as a register/immediate. Its
    // stack effect is still the operand width. Omitting this form makes a
    // balanced outgoing-argument sequence look unbalanced at a loop backedge;
    // the exact stack-state lattice then becomes unknown and every later
    // SP-relative frame access (including wide MOVAPS stores) disappears.
    stack_delta(addr, -(*sz as i64)) <--
        ppush(addr, sym),
        op_indirect(sym, _, _, _, _, _, sz),
        if *sz > 0;

    stack_delta(addr, *sz as i64) <--
        ppop(addr, ireg_sym),
        op_register(ireg_sym, ireg_r),
        ireg_hold_type(ireg_r.to_string(), typ),
        type_size(typ, sz);


    stack_offset(func_start, func_start, Dual(Set::singleton(0))) <--
        func_span(_, func_start, _);

    // A loop back edge is not another predecessor state at the loop header:
    // feeding it into exact stack height makes every nonzero stack-probe loop
    // intersect its entry height with the height after one probe iteration and
    // become unknown.  Once unknown, every later SP-relative frame load/store
    // silently loses its Mach instruction.  Detect back edges structurally by
    // block dominance, mirroring RTL's SP lattice.  The dominator state stays a
    // Dual<Set> lattice keyed by (function, block), never a pairwise relation.
    #[local] relation stack_func_entry_block(Address, Address);
    stack_func_entry_block(*func, *entry_block) <--
        block_in_function(entry_block, func),
        code_in_block(func, entry_block);

    #[local] relation stack_offset_inter_step(Address, Address);
    stack_offset_inter_step(src, dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !noreturn_call_site(src);

    #[local] relation stack_block_next(Address, Address);
    stack_block_next(*src_block, *dst_block) <--
        stack_offset_inter_step(src, dst),
        code_in_block(src, src_block),
        code_in_block(dst, dst_block);

    #[local] lattice stack_block_strict_dom_set(Address, Address, Dual<Set<Address>>);
    #[local] lattice stack_block_dom_set(Address, Address, Dual<Set<Address>>);

    stack_block_dom_set(*func, *entry_block, Dual(Set::singleton(*entry_block))) <--
        stack_func_entry_block(func, entry_block);

    stack_block_strict_dom_set(*func, *block, Dual(parent_doms.0.clone())) <--
        stack_block_dom_set(func, parent, parent_doms),
        stack_block_next(parent, block),
        block_in_function(block, func),
        !stack_func_entry_block(func, block);

    stack_block_dom_set(*func, *block, Dual(asm_dom_set_with_self(&strict.0, *block))) <--
        stack_block_strict_dom_set(func, block, strict),
        !stack_func_entry_block(func, block);

    #[local] relation stack_offset_back_edge(Address, Address, Address);
    stack_offset_back_edge(*func, *src, *dst) <--
        stack_offset_inter_step(src, dst),
        code_in_block(src, src_block),
        code_in_block(dst, dst_block),
        instr_in_function(src, func),
        instr_in_function(dst, func),
        stack_block_dom_set(func, src_block, dominators),
        if dominators.0.contains(dst_block);

    // Measurement-only counterfactual for the exact family repaired here.
    // Re-evaluate the old transfer function (which admitted back edges), but
    // only for functions whose loop-header block changes SP.  That is the
    // stack-probe/nonzero-loop shape capable of erasing later frame accesses,
    // and keeps this second O(V * depth) lattice out of ordinary functions.
    #[local] relation func_with_stack_delta_back_edge(Address);
    func_with_stack_delta_back_edge(*func) <--
        stack_offset_back_edge(func, _, dst),
        code_in_block(dst, header_block),
        code_in_block(delta_addr, header_block),
        stack_delta(delta_addr, delta),
        if *delta != 0,
        instr_in_function(dst, func);

    #[local] lattice stack_offset_with_back_edges(Address, Address, Dual<Set<i64>>);
    stack_offset_with_back_edges(*func_start, *func_start, Dual(Set::singleton(0))) <--
        func_span(_, func_start, _),
        func_with_stack_delta_back_edge(func_start);
    stack_offset_with_back_edges(*func_start, *curaddr, Dual(shift_stack_offsets(&prev_offsets.0, *delta))) <--
        stack_offset_with_back_edges(func_start, prevaddr, prev_offsets),
        cfg_step(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        if curaddr != func_start,
        stack_delta(prevaddr, delta);
    stack_offset_with_back_edges(*func_start, *curaddr, Dual(prev_offsets.0.clone())) <--
        stack_offset_with_back_edges(func_start, prevaddr, prev_offsets),
        cfg_step(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        if curaddr != func_start,
        !stack_delta(prevaddr, _);

    // Lattice projections can observe improving intermediate values.  Record
    // unknown explicitly and stratify the public marker through its negation;
    // a transient exact value at a real forward disagreement therefore cannot
    // be reported as rescued.
    #[local] relation corrected_stack_offset_exact(Address, Address);
    #[local] relation corrected_stack_offset_unknown(Address, Address);
    #[local] relation old_stack_offset_unknown(Address, Address);
    corrected_stack_offset_exact(*func, *addr) <--
        stack_offset(func, addr, offsets),
        if exact_stack_offset(&offsets.0).is_some();
    corrected_stack_offset_unknown(*func, *addr) <--
        stack_offset(func, addr, offsets),
        if exact_stack_offset(&offsets.0).is_none();
    old_stack_offset_unknown(*func, *addr) <--
        stack_offset_with_back_edges(func, addr, offsets),
        if exact_stack_offset(&offsets.0).is_none();

    #[local] relation sp_relative_mov_access(Address);
    sp_relative_mov_access(addr) <--
        pmov(addr, memory, _),
        op_indirect(memory, _, base, index, _, _, _),
        if Mreg::x86(*base) == Mreg::SP,
        if *index == "NONE" || index.is_empty();
    sp_relative_mov_access(addr) <--
        pmov(addr, _, memory),
        op_indirect(memory, _, base, index, _, _, _),
        if Mreg::x86(*base) == Mreg::SP,
        if *index == "NONE" || index.is_empty();

    // Public only so RTL can intersect the exact old-lattice gap with incoming
    // parameter spill/reload facts and print a corpus-wide before/after gauge.
    relation stack_offset_backedge_rescued_access(Address, Address);
    stack_offset_backedge_rescued_access(*func, *addr) <--
        corrected_stack_offset_exact(func, addr),
        !corrected_stack_offset_unknown(func, addr),
        old_stack_offset_unknown(func, addr),
        sp_relative_mov_access(addr);

    // Stack state is control-flow state.  Propagate it over the structural
    // instruction CFG, including inter-block branch/fallthrough edges, rather
    // than physical instruction adjacency.  Otherwise every stack access in a
    // branch target loses its frame anchor and may disappear from Mach IR.  A
    // must-state lattice keeps the one exact offset on which all incoming paths
    // agree; disagreement across forward paths converges to the empty set
    // instead of inventing an offset from one arm.  Dominance-proven loop back
    // edges were removed above so a probe cycle cannot poison its own header.
    stack_offset(func_start, curaddr, Dual(shift_stack_offsets(&prev_offsets.0, *delta))) <--
        stack_offset(func_start, prevaddr, prev_offsets),
        cfg_step(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        if curaddr != func_start,
        !stack_offset_back_edge(func_start, prevaddr, curaddr),
        stack_delta(prevaddr, delta);

    stack_offset(func_start, curaddr, Dual(prev_offsets.0.clone())) <--
        stack_offset(func_start, prevaddr, prev_offsets),
        cfg_step(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        if curaddr != func_start,
        !stack_offset_back_edge(func_start, prevaddr, curaddr),
        !stack_delta(prevaddr, _);

    // SP is the coordinate origin every frame slot is named from, and the
    // prologue fixes it for the whole body.  A call that passes arguments on the
    // stack lowers SP transiently, and a frame reference made inside that window
    // carries a displacement measured from the LOWERED SP: it names a cell that
    // many bytes further up the frame than its raw value says, so two distinct
    // cells collapse onto one slot.  That is how touch's -d argument and the
    // struct stat it stats into became the same escaped-region member, and the
    // date pointer came out truncated to that member's width.  Requiring the SP
    // state to be exact, as these rules already did, is not enough on its own:
    // the state inside the window is perfectly exact, and wrong to use raw.
    //
    // The origin is read off the call sites themselves.  A call is made with SP
    // at the origin minus that call's own outgoing stack bytes, so the
    // shallowest call-site delta IS the origin as soon as one call passes
    // everything in registers.  When none does the value is too deep, the shift
    // below clamps to zero, and the function keeps the displacements it has
    // rather than acquiring invented ones: the correction is one-sided by
    // construction and can only move a reference SP was provably below.
    #[local] relation call_site_sp_delta(Address, i64);
    call_site_sp_delta(func, d) <--
        instruction(addr, _, _, "CALL", _, _, _, _, _, _),
        stack_offset(func, addr, rsp_offsets),
        if let Some(d) = exact_stack_offset(&rsp_offsets.0);

    #[local] relation func_frame_sp_origin(Address, i64);
    func_frame_sp_origin(func, d) <--
        call_site_sp_delta(func, _),
        agg d = aggregators::max(x) in call_site_sp_delta(func, x);

    // A function that calls nothing opens no argument window either, so nothing
    // can be below its origin; i64::MIN saturates every shift to zero.
    func_frame_sp_origin(func, i64::MIN) <--
        stack_offset(func, _, _),
        !call_site_sp_delta(func, _);

    // Bytes SP sits below the frame origin here; zero outside a window.  This
    // carries the exact-SP-state gate the frame reference rules used to apply
    // themselves, so joining it neither widens nor narrows which references lift.
    #[local] relation sp_frame_shift(Address, i64);
    sp_frame_shift(addr, depth) <--
        stack_offset(func, addr, rsp_offsets),
        if let Some(d) = exact_stack_offset(&rsp_offsets.0),
        func_frame_sp_origin(func, origin),
        let depth = origin.saturating_sub(d).max(0);

    // The SP-relative LEAs below have no SP-state gate of their own, and adding
    // one would drop every address-of whose state is unknown.  Give them a total
    // shift instead, zero wherever the state cannot be read.
    #[local] relation sp_lea_shift(Address, i64);
    sp_lea_shift(*addr, *depth) <--
        plea(addr, _, _),
        sp_frame_shift(addr, depth);
    sp_lea_shift(*addr, 0) <--
        plea(addr, _, _),
        !sp_frame_shift(*addr, _);

    // Published for the stack def-use analysis, which reports each side of a
    // chain at its own raw displacement and so has to be restated in the same
    // frame coordinates as the references above -- otherwise a def and the use
    // that reads it name different cells and the use's name lands on whatever
    // unrelated object owns that displacement in the settled frame.  Only the
    // nonzero shifts travel: a row per instruction would be a second copy of
    // the whole instruction stream for the handful of windows that exist.
    relation sp_window_depth(Address, i64);
    sp_window_depth(*addr, *depth) <--
        sp_frame_shift(addr, depth),
        if *depth != 0;


    // ireg_hold_type maps sub-registers to Tint (MInt32), so chunk must come from the capstone operand size (msize), not the register family; refine_chunk_with_size narrows and never widens.
    transl_store_inferred(addr, mc, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        !reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, idx_str, _scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    // A movss/movsd store of an XMM register to memory is a FLOAT store, taking its chunk from the mnemonic, not the XMM default Tany64 that would type the field int and truncate every stored float.
    transl_store_inferred(addr, mc, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, idx_str, _scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // Indexed store (non-SP/non-BP base with index register)
    transl_store_inferred(addr, mc, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        !reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*arg, *idx_arg]),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    // movss/movsd INDEXED store of an XMM register (float `out[i] = val`): float chunk from mnemonic.
    transl_store_inferred(addr, mc, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*arg, *idx_arg]),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // Scaled-index store with no base register: mov src, disp(,%idx,scale)
    transl_store_inferred(addr, mc, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, base_str, idx_str, scale, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: None,
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*idx_arg]),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    transl_store(addr, mc, addrmode, regs, src) <--
        transl_store_inferred(addr, mc, addrmode, regs, src);

    transl_store(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(src, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(dst, _, r2, idx_str, _scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        !transl_store_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // Indexed store (mnemonic-based, non-SP/non-BP base with index register)
    transl_store(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(src, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*arg, *idx_arg]),
        !transl_store_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // Scaled-index store with no base register (mnemonic-based): mov src, disp(,%idx,scale)
    transl_store(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(src, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(dst, _, base_str, idx_str, scale, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: None,
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*idx_arg]),
        !transl_store_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    addrmode_needs_resolution(*addr, *am, target_addr) <--
        transl_store(addr, _, am, _, _),
        if let Some(target_addr_i64) = addrmode_needs_symbol_resolution(am),
        let target_addr = target_addr_i64 as Address;

    addrmode_needs_resolution(*addr, *am, target_addr) <--
        transl_load(addr, _, am, _, _),
        if let Some(target_addr_i64) = addrmode_needs_symbol_resolution(am),
        let target_addr = target_addr_i64 as Address;

    addrmode_needs_resolution(*node, *am, target) <--
        bounded_absolute_data_access(_, node, owner, field_offset, _, _, _, _),
        transl_load(node, _, am, _, _),
        if *field_offset >= 0,
        let owner_address = *owner as Address,
        if let Some(target) = owner_address.checked_add(*field_offset as u64);
    addrmode_needs_resolution(*node, *am, target) <--
        bounded_absolute_data_access(_, node, owner, field_offset, _, _, _, _),
        transl_store(node, _, am, _, _),
        if *field_offset >= 0,
        let owner_address = *owner as Address,
        if let Some(target) = owner_address.checked_add(*field_offset as u64);

    site_resolved_addr_to_symbol(*node, *target, *ident, *offset) <--
        addrmode_needs_resolution(node, _, target),
        resolved_addr_to_symbol(target, ident, offset),
        !bounded_absolute_data_access(_, node, _, _, _, _, _, _);
    site_resolved_addr_to_symbol(*node, target, *owner, *field_offset) <--
        bounded_absolute_data_access(_, node, owner, field_offset, _, _, _, _),
        if *field_offset >= 0,
        let owner_address = *owner as Address,
        if let Some(target) = owner_address.checked_add(*field_offset as u64);

    addr_requiring_symbol(target_addr) <--
        addrmode_needs_resolution(_, _, target_addr);

    addr_requiring_symbol(target_addr) <--
        rip_target_addr(_, target_addr);

    addr_requiring_symbol(target_addr) <--
        abs_target_addr(_, target_addr);
    mach_inst(addr, MachInst::Mstore(*memory_chunk, addressing, Arc::new(args), *src)) <--
        transl_store(addr, memory_chunk, addrmode, regs, src),
        addrmode_needs_resolution(addr, *addrmode, target_addr),
        site_resolved_addr_to_symbol(addr, target_addr, ident, offset),
        let resolved = Some((*ident, *offset)),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, resolved);

    mach_inst(addr, MachInst::Mstore(*memory_chunk, addressing, Arc::new(args), *src)) <--
        transl_store(addr, memory_chunk, addrmode, regs, src),
        !addrmode_needs_resolution(addr, *addrmode, _),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, None);

    mach_inst(addr, MachInst::Msetstack(src_reg, disp - depth, *typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        !reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::SP,
        if *idx == "NONE",
        if *msize != 1 && *msize != 2,
        sp_frame_shift(addr, depth),
        ireg_hold_type(srcstr.to_string(), typ);

    mach_inst(addr, MachInst::Msetstack(src_reg, *disp, *typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        !reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx == "NONE",
        if *msize != 1 && *msize != 2,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ);

    // A movss/movsd store of an XMM register to a stack slot is a FLOAT store whose width is the access size, not the 64-bit hold type, so a float param spill is not widened to double.
    mach_inst(addr, MachInst::Msetstack(src_reg, disp - depth, typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::SP,
        if *idx == "NONE",
        if *msize == 4 || *msize == 8,
        sp_frame_shift(addr, depth),
        let typ = if *msize == 4 { Typ::Tsingle } else { Typ::Tfloat };

    mach_inst(addr, MachInst::Msetstack(src_reg, *disp, typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx == "NONE",
        if *msize == 4 || *msize == 8,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        let typ = if *msize == 4 { Typ::Tsingle } else { Typ::Tfloat };

    // A wide XMM/YMM spill (msize 16 or 32) has no float semantics and no 128-bit Typ, so materialize a Tany64 Msetstack to keep the base-offset slot defined and tracked.
    mach_inst(addr, MachInst::Msetstack(src_reg, disp - depth, Typ::Tany64)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::SP,
        if *idx == "NONE",
        if *msize > 8,
        sp_frame_shift(addr, depth);

    mach_inst(addr, MachInst::Msetstack(src_reg, *disp, Typ::Tany64)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx == "NONE",
        if *msize > 8,
        instr_in_function(addr, func),
        func_has_frame_pointer(func);

    // Typ has no 8/16-bit member, so sub-register frame-slot stores use Ainstack Mstore with the true byte width; rtl re-derives the Lsetstack row from Lstore(Ainstack,[]) so slot dataflow is unchanged.
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Ainstack(disp - depth), Arc::new(vec![]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::SP,
        if *idx == "NONE",
        if *msize == 1 || *msize == 2,
        sp_frame_shift(addr, depth),
        ireg_hold_type(srcstr.to_string(), _),
        let mc = if *msize == 1 { MemoryChunk::MInt8Unsigned } else { MemoryChunk::MInt16Unsigned };

    mach_inst(addr, MachInst::Mstore(mc, Addressing::Ainstack(*disp), Arc::new(vec![]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx == "NONE",
        if *msize == 1 || *msize == 2,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), _),
        let mc = if *msize == 1 { MemoryChunk::MInt8Unsigned } else { MemoryChunk::MInt16Unsigned };

    mach_imm_stack_init(addr, disp, imm_int, ty) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, base, idx, _, disp, sz),
        if Mreg::x86(base) == Mreg::BP,
        if *idx == "NONE" || idx.is_empty(),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;

    // Ainstack/Lsetstack and SP-relative LEAs use the raw post-frame-allocation
    // displacement as their local-slot identity.  Keep immediate stores in
    // that same coordinate system so `mov $imm, disp(%rsp)` aliases ordinary
    // stores, reloads, and `lea disp(%rsp)` for an escaped object.  The exact
    // structural SP state remains a validity gate; entry anchoring for outgoing
    // call arguments is derived separately in rtl_pass from the raw operand.
    mach_imm_stack_init(addr, disp - depth, imm_int, ty) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, base, idx, _, disp, sz),
        if Mreg::x86(base) == Mreg::SP,
        if *idx == "NONE" || idx.is_empty(),
        sp_frame_shift(addr, depth),
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;

    // RIP base excluded: Mreg::x86("RIP") is Unknown so the row could never lower; RIP-relative immediate global stores have no lifting route and are silently dropped (FIXPLAN 3.8c).
    mach_imm_indirect_store(addr, imm_int, mc, base_mreg, *disp) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, r2, _, _scale, disp, sz),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *r2 != "NONE" && !r2.is_empty(),
        !reg_ip(r2),
        let base_mreg = Mreg::x86(r2),
        let mc = refine_chunk_with_size(if *sz <= 4 { MemoryChunk::MInt32 } else { MemoryChunk::MInt64 }, *sz),
        let imm_int = *imm_sym as i64;

    mach_inst(addr, MachInst::Mgetstack(disp - depth, *typ, Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx, _, disp, _),
        if Mreg::x86(r2) == Mreg::SP,
        if *idx == "NONE",
        op_register(dst, dststr),
        sp_frame_shift(addr, depth),
        ireg_hold_type(dststr.to_string(), typ);

    mach_inst(addr, MachInst::Mgetstack(*disp, *typ, Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx, _, disp, _),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx == "NONE",
        op_register(dst, dststr),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ);

    // SP-relative indexed load: treat as Mload with Aindexed2scaled addressing
    mach_inst(addr, MachInst::Mload(*mc, addressing, Arc::new(args), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, base_str, idx_str, scale, disp, _),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        op_register(dst, dststr),
        ireg_hold_type(dststr.to_string(), typ),
        type_to_memchunk(typ, mc),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::SP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::SP, *idx_arg])
        };

    // SP-relative indexed register stores are runtime-indexed writes into a
    // frame object, not scalar Msetstack slots.  Preserve both SP and the
    // index in Mach so rtl_pass can rebase SP to Ainstack and keep the dynamic
    // element selection.  The index-free rules above remain the sole scalar
    // frame-slot route.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        !reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, base_str, idx_str, scale, disp, msize),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        ireg_hold_type(srcstr.to_string(), typ),
        type_to_memchunk(typ, chunk),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(*chunk, *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::SP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::SP, *idx_arg])
        };

    // XMM stores take their semantic width from the move mnemonic rather than
    // the register family's generic hold type.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, base_str, idx_str, scale, disp, msize),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::SP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::SP, *idx_arg])
        };

    // Mnemonic fallback for architectures/register spellings without an
    // inferred hold type; it is disjoint from the typed GP rule above.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        !reg_xmm(srcstr),
        !ireg_hold_type(srcstr.to_string(), _),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, base_str, idx_str, scale, disp, msize),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::SP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::SP, *idx_arg])
        };

    // BP-relative indexed load with frame pointer: treat as Mload
    mach_inst(addr, MachInst::Mload(*mc, addressing, Arc::new(args), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, base_str, idx_str, scale, disp, _),
        if Mreg::x86(base_str) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        op_register(dst, dststr),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ),
        type_to_memchunk(typ, mc),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-relative load when BP is not the frame pointer is a regular memory load, INDEX-FREE form only: without the index guard the index was dropped and element[0] read forever.
    mach_inst(addr, MachInst::Mload(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx_str, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ),
        type_to_memchunk(typ, base_chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        // For a sign/zero-extending GP load the accessed memory is the narrower SOURCE, so take the chunk from the mnemonic and operand width, not the 64-bit dst hold-type; float moves excluded.
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if (mnem_upper.contains("MOVZX") || mnem_upper.contains("MOVSX")
            || mnem_upper.contains("MOVZB") || mnem_upper.contains("MOVSB")
            || mnem_upper.contains("MOVZW") || mnem_upper.contains("MOVSW")) {
            refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize)
        } else {
            *base_chunk
        };

    // BP-base INDEXED load, BP not the frame pointer: preserve base+index (mirror the frame-pointer rule).
    mach_inst(addr, MachInst::Mload(mc, addressing, Arc::new(args), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ),
        type_to_memchunk(typ, base_chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        // Sign/zero-extending GP load: width comes from the SOURCE operand, not the 64-bit dst hold-type; float moves have their own XMM width rules.
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if (mnem_upper.contains("MOVZX") || mnem_upper.contains("MOVSX")
            || mnem_upper.contains("MOVZB") || mnem_upper.contains("MOVSB")
            || mnem_upper.contains("MOVZW") || mnem_upper.contains("MOVSW")) {
            refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize)
        } else {
            *base_chunk
        },
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-relative load (mnemonic-based chunk) when BP is NOT the frame pointer
    mach_inst(addr, MachInst::Mload(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx_str, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(dststr.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    // BP-base INDEXED load (mnemonic chunk), BP not the frame pointer: preserve base+index.
    mach_inst(addr, MachInst::Mload(mc, addressing, Arc::new(args), Mreg::x86(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(dststr.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-base INDEXED store with a frame pointer, the mirror of the indexed load: without it a runtime-indexed stack-array write produced no Mstore and DSE collapsed the loop body.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ),
        type_to_memchunk(typ, chunk),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(*chunk, *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-base INDEXED store (mnemonic chunk) WITH frame pointer: src reg has no inferred hold type.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        !ireg_hold_type(srcstr.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-relative store when BP is NOT the frame pointer. INDEX-FREE form only (indexed form below).
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    // BP-base INDEXED store, BP not the frame pointer: preserve base+index (else `out[i]=x` -> `out[0]=x`).
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ),
        type_to_memchunk(typ, chunk),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(*chunk, *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-relative store (mnemonic-based chunk) when BP is NOT the frame pointer. INDEX-FREE form only.
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, _, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(srcstr.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // BP-base INDEXED store (mnemonic chunk), BP not the frame pointer: preserve base+index.
    mach_inst(addr, MachInst::Mstore(mc, addressing, Arc::new(args), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::x86(srcstr),
        op_indirect(dst, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(srcstr.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize),
        let (addressing, args) = if *scale > 1 {
            (Addressing::Aindexed2scaled(*scale, *disp), vec![Mreg::BP, *idx_arg])
        } else {
            (Addressing::Aindexed2(*disp), vec![Mreg::BP, *idx_arg])
        };

    // BP-relative immediate store when BP is NOT the frame pointer
    mach_imm_indirect_store(addr, imm_int, mc, Mreg::BP, *disp) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, r2, _, _scale, disp, sz),
        if Mreg::x86(r2) == Mreg::BP,
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        let mc = refine_chunk_with_size(if *sz <= 4 { MemoryChunk::MInt32 } else { MemoryChunk::MInt64 }, *sz),
        let imm_int = *imm_sym as i64;

    // BP-relative INDEXED immediate store with a frame pointer is a genuine stack-array element write, unlike the index-free scalar slot init; this row only fires the trigger and excludes the no-index case.
    mach_imm_indirect_store(addr, imm_int, mc, Mreg::BP, *disp) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, r2, idx_str, _scale, disp, sz),
        if Mreg::x86(r2) == Mreg::BP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        let mc = refine_chunk_with_size(if *sz <= 4 { MemoryChunk::MInt32 } else { MemoryChunk::MInt64 }, *sz),
        let imm_int = *imm_sym as i64;
    // A call to a function that never returns has no fall-through successor:
    // the instruction physically after it is reached only by some other edge,
    // if at all.  linear_pass already cuts these edges out of the block CFG via
    // known_noreturn_call_site, but the stack-offset lattice below is computed
    // here, before that pass runs, so it has to cut them itself.  The evidence
    // is the same and is already local to this pass: a direct call edge whose
    // target is a PLT entry for one of the ABI's always-noreturn symbols.
    #[local] relation noreturn_call_site(Address);
    noreturn_call_site(*site) <--
        ddisasm_cfg_edge(site, target, "call"),
        plt_entry(target, name),
        is_known_noreturn_function(name);
    noreturn_call_site(*site) <--
        ddisasm_cfg_edge(site, target, "call"),
        plt_block(target, name),
        is_known_noreturn_function(name);
    noreturn_call_site(*site) <--
        ddisasm_cfg_edge(site, target, "call"),
        symbol_resolved_addr(name, target),
        is_known_noreturn_function(name);

    // Instruction-level CFG successor: intra-block sequential adjacency plus
    // real inter-block edges. This is the only execution-order authority used
    // by the flags and reaching-value analyses below.  Keeping the phantom
    // fall-through out matters most for stack_offset: an exit(3) call on the
    // usage path is reached with the callee's stack arguments still pushed, so
    // letting that offset flow past the call disagrees with every other path
    // and the must-state lattice converges to the empty set.  exact_stack_offset
    // then fails for the whole rest of the function and every stack store there
    // silently produces no Mach instruction at all -- which is how a local that
    // C code plainly assigns comes out declared and never written.
    #[local] relation cfg_step(Address, Address);
    cfg_step(a, b) <--
        next(a, b),
        code_in_block(a, blk),
        code_in_block(b, blk),
        !noreturn_call_site(a);
    cfg_step(a, b) <--
        ddisasm_cfg_edge(a, b, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !noreturn_call_site(a);

    // A compiler strength-reduction idiom is straight-line code.  Raw `next`
    // is only physical adjacency and can cross blocks/functions; pairing it
    // with block identity and ownership makes this a structural step without
    // building a pairwise reachability relation.
    #[local] relation owned_straightline_step(Address, Address, Address);
    owned_straightline_step(*func, *a, *b) <--
        cfg_step(a, b),
        next(a, b),
        code_in_block(a, block),
        code_in_block(b, block),
        instr_in_function(a, func),
        instr_in_function(b, func);

    // Preserve each raw memory operand's address-register spelling.  Addrmode
    // canonicalizes EDI/RDI to the same Ireg, but only the pointer-width view
    // is admissible for an LP64 symbolic-storage interpretation.
    #[local] relation raw_memory_operand(Address, &'static str, &'static str, i64, usize);
    raw_memory_operand(*addr, *base, *index, *disp, *width) <--
        instruction(addr, _, _, _, operand, _, _, _, _, _),
        op_indirect(operand, _, base, index, _, disp, width);
    raw_memory_operand(*addr, *base, *index, *disp, *width) <--
        instruction(addr, _, _, _, _, operand, _, _, _, _),
        op_indirect(operand, _, base, index, _, disp, width);
    raw_memory_operand(*addr, *base, *index, *disp, *width) <--
        instruction(addr, _, _, _, _, _, operand, _, _, _),
        op_indirect(operand, _, base, index, _, disp, width);
    raw_memory_operand(*addr, *base, *index, *disp, *width) <--
        instruction(addr, _, _, _, _, _, _, operand, _, _),
        op_indirect(operand, _, base, index, _, disp, width);

    // Candidate sites are deliberately loose: image kind, section membership,
    // raw pointer-width addressing and a lowering-supported load/store are all
    // positive facts.  The lattice below supplies the stricter value proof.
    #[local] relation absolute_data_memory_site(Address, Address, Addrmode, Address, Mreg, usize);
    absolute_data_memory_site(*func, *node, *am, target, base_reg, *access_width) <--
        transl_load(node, _, am, _, _),
        raw_memory_operand(node, base_name, index_name, displacement, access_width),
        if *access_width > 0,
        if let Some((target, base_reg)) = pointer_width_absolute_based_operand(
            am,
            base_name,
            index_name,
            *displacement,
        ),
        raw_image_addresses_are_absolute(raw_absolute),
        if *raw_absolute,
        data_section_range(section_start, section_end),
        if target >= *section_start && target < *section_end,
        instr_in_function(node, func);
    absolute_data_memory_site(*func, *node, *am, target, base_reg, *access_width) <--
        transl_store(node, _, am, _, _),
        raw_memory_operand(node, base_name, index_name, displacement, access_width),
        if *access_width > 0,
        if let Some((target, base_reg)) = pointer_width_absolute_based_operand(
            am,
            base_name,
            index_name,
            *displacement,
        ),
        raw_image_addresses_are_absolute(raw_absolute),
        if *raw_absolute,
        data_section_range(section_start, section_end),
        if target >= *section_start && target < *section_end,
        instr_in_function(node, func);

    #[local] relation bounded_offset_analysis_func(Address);
    bounded_offset_analysis_func(func) <--
        absolute_data_memory_site(func, _, _, _, _, _);

    #[local] relation bounded_offset_tracked(Address, Mreg);
    bounded_offset_tracked(*func, *reg) <--
        bounded_offset_analysis_func(func),
        preg_of(reg, preg),
        ireg_of(preg, _);

    #[local] relation bounded_offset_mask_def(Address, Mreg, BoundedOffsetShape);
    bounded_offset_mask_def(*addr, dst_reg, shape) <--
        pand(addr, dst, immediate),
        op_register(dst, dst_name),
        op_immediate(immediate, value, _),
        if let Some(shape) = contiguous_low_mask_shape(*addr, dst_name, *value),
        let dst_reg = Mreg::x86(dst_name);

    #[local] relation bounded_offset_shift_transfer(Address, Mreg, &'static str, i64);
    bounded_offset_shift_transfer(*addr, dst_reg, *dst_name, *shift) <--
        psal(addr, dst, immediate),
        op_register(dst, dst_name),
        op_immediate(immediate, shift, _),
        if matches!(x86_gpr_view_width(dst_name), Some(4 | 8)),
        let dst_reg = Mreg::x86(dst_name);

    #[local] relation bounded_offset_scale_transfer(Address, Mreg, &'static str, u64);
    bounded_offset_scale_transfer(*addr, dst_reg, *dst_name, factor) <--
        pimul(addr, dst, immediate),
        op_register(dst, dst_name),
        op_immediate(immediate, factor_signed, _),
        if *factor_signed > 0,
        if matches!(x86_gpr_view_width(dst_name), Some(4 | 8)),
        let factor = *factor_signed as u64,
        let dst_reg = Mreg::x86(dst_name);

    #[local] relation bounded_offset_copy_transfer(Address, Mreg, Mreg, &'static str, &'static str, &'static str);
    bounded_offset_copy_transfer(*addr, dst_reg, src_reg, *mnemonic, *dst_name, *src_name) <--
        pmov(addr, dst, src),
        instruction(addr, _, _, mnemonic, _, _, _, _, _, _),
        op_register(dst, dst_name),
        op_register(src, src_name),
        if *mnemonic == "MOV",
        if matches!(x86_gpr_view_width(dst_name), Some(4 | 8)),
        if x86_gpr_view_width(dst_name) == x86_gpr_view_width(src_name),
        let dst_reg = Mreg::x86(dst_name),
        let src_reg = Mreg::x86(src_name);

    #[local] relation bounded_offset_handled_def(Address, Mreg);
    bounded_offset_handled_def(addr, reg) <-- bounded_offset_mask_def(addr, reg, _);
    bounded_offset_handled_def(addr, reg) <-- bounded_offset_shift_transfer(addr, reg, _, _);
    bounded_offset_handled_def(addr, reg) <-- bounded_offset_scale_transfer(addr, reg, _, _);
    bounded_offset_handled_def(addr, reg) <-- bounded_offset_copy_transfer(addr, reg, _, _, _, _);

    // MUST-state dataflow: every `(function,node,register)` key stores Bottom,
    // one finite shape, or Top.  Joins on alternate CFG arms are lattice joins;
    // no pairwise reachability relation or address-order surrogate is used.
    #[local] lattice bounded_offset_in(Address, Address, Mreg, ConstPropagation<BoundedOffsetShape>);
    #[local] lattice bounded_offset_out(Address, Address, Mreg, ConstPropagation<BoundedOffsetShape>);

    bounded_offset_in(*func, *func, *reg, ConstPropagation::Top) <--
        bounded_offset_tracked(func, reg),
        instr_in_function(func, func);

    bounded_offset_in(*func, *succ, *reg, state.clone()) <--
        bounded_offset_out(func, node, reg, state),
        cfg_step(node, succ),
        instr_in_function(succ, func);

    bounded_offset_out(*func, *node, *reg, ConstPropagation::Constant(*shape)) <--
        bounded_offset_in(func, node, reg, _),
        bounded_offset_mask_def(node, reg, shape),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, next_state) <--
        bounded_offset_in(func, node, reg, state),
        bounded_offset_shift_transfer(node, reg, dst_name, shift),
        let next_state = shift_bounded_offset_state(state, dst_name, *shift),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, next_state) <--
        bounded_offset_in(func, node, reg, state),
        bounded_offset_scale_transfer(node, reg, dst_name, factor),
        let next_state = scale_bounded_offset_state(state, dst_name, *factor),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, next_state) <--
        bounded_offset_in(func, node, reg, _),
        bounded_offset_copy_transfer(node, reg, source, mnemonic, dst_name, src_name),
        bounded_offset_in(func, node, source, source_state),
        let next_state = copy_bounded_offset_state(source_state, mnemonic, dst_name, src_name),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, ConstPropagation::Top) <--
        bounded_offset_in(func, node, reg, _),
        decoded_reg_def(node, reg),
        !bounded_offset_handled_def(node, reg),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, state.clone()) <--
        bounded_offset_in(func, node, reg, state),
        !decoded_reg_def(node, reg),
        !raw_gpr_barrier(node);

    bounded_offset_out(*func, *node, *reg, ConstPropagation::Top) <--
        bounded_offset_in(func, node, reg, _),
        raw_gpr_barrier(node);

    #[local] relation bounded_offset_candidate(Address, Address, Mreg, BoundedOffsetShape);
    bounded_offset_candidate(*func, *node, *reg, *shape) <--
        bounded_offset_in(func, node, reg, state),
        if let ConstPropagation::Constant(shape) = state;

    #[local] relation bounded_offset_conflict(Address, Address, Mreg);
    bounded_offset_conflict(*func, *node, *reg) <--
        bounded_offset_in(func, node, reg, state),
        if matches!(state, ConstPropagation::Top);

    #[local] relation bounded_offset_exact(Address, Address, Mreg, BoundedOffsetShape);
    bounded_offset_exact(*func, *node, *reg, *shape) <--
        bounded_offset_candidate(func, node, reg, shape),
        !bounded_offset_conflict(func, node, reg),
        !raw_gpr_unresolved_owner(func);

    // One row per certified access before physical-owner selection.
    #[local] relation bounded_data_access_candidate(Address, Address, Addrmode, Address, usize, Address, u64, usize, u64);
    bounded_data_access_candidate(*func, *node, *am, *target, *access_width,
                                  shape.origin, shape.stride, shape.count, shape.max) <--
        absolute_data_memory_site(func, node, am, target, base_reg, access_width),
        bounded_offset_exact(func, node, base_reg, shape),
        if shape.count > 0 && shape.stride > 0,
        if let Ok(access_width_u64) = u64::try_from(*access_width),
        if let Some(last_start) = target.checked_add(shape.max),
        if let Some(access_end) = last_start.checked_add(access_width_u64),
        data_section_range(section_start, section_end),
        if *target >= *section_start && access_end <= *section_end;

    // A single bounded value may feed several fields of one record.  Admit a
    // family only when all its absolute coordinates fit in one stride window;
    // this safely unifies `{base, base+field}` while refusing to guess a
    // partition when the same index feeds multiple distant tables.
    #[local] relation bounded_family_target(Address, Address, u64, usize, u64, Address);
    bounded_family_target(*func, *origin, *stride, *count, *max, *target) <--
        bounded_data_access_candidate(func, _, _, target, _, origin, stride, count, max);

    #[local] relation bounded_family_min(Address, Address, u64, usize, u64, Address);
    bounded_family_min(func, origin, stride, count, max, minimum) <--
        bounded_family_target(func, origin, stride, count, max, _),
        agg minimum = ascent::aggregators::min(target)
            in bounded_family_target(func, origin, stride, count, max, target);

    #[local] relation bounded_family_max(Address, Address, u64, usize, u64, Address);
    bounded_family_max(func, origin, stride, count, max, maximum) <--
        bounded_family_target(func, origin, stride, count, max, _),
        agg maximum = ascent::aggregators::max(target)
            in bounded_family_target(func, origin, stride, count, max, target);

    #[local] relation bounded_family_coherent(Address, Address, u64, usize, u64, Address);
    bounded_family_coherent(*func, *origin, *stride, *count, *max, *owner) <--
        bounded_family_min(func, origin, stride, count, max, owner),
        bounded_family_max(func, origin, stride, count, max, maximum),
        if let Some(span) = maximum.checked_sub(*owner),
        if span < *stride;

    #[local] relation bounded_family_field_end(Address, Address, u64, usize, u64, u64);
    bounded_family_field_end(*func, *origin, *stride, *count, *max, field_end) <--
        bounded_family_coherent(func, origin, stride, count, max, owner),
        bounded_data_access_candidate(func, _, _, target, access_width, origin, stride, count, max),
        if let Some(field_offset) = target.checked_sub(*owner),
        if let Ok(access_width_u64) = u64::try_from(*access_width),
        if let Some(field_end) = field_offset.checked_add(access_width_u64);

    #[local] relation bounded_family_max_field_end(Address, Address, u64, usize, u64, u64);
    bounded_family_max_field_end(func, origin, stride, count, max, maximum) <--
        bounded_family_field_end(func, origin, stride, count, max, _),
        agg maximum = ascent::aggregators::max(end)
            in bounded_family_field_end(func, origin, stride, count, max, end);

    // (key..., coordinate owner, exclusive accessed end)
    #[local] relation bounded_family_extent(Address, Address, u64, usize, u64, Address, Address);
    bounded_family_extent(*func, *origin, *stride, *count, *max, *owner, family_end) <--
        bounded_family_coherent(func, origin, stride, count, max, owner),
        bounded_family_max_field_end(func, origin, stride, count, max, max_field_end),
        if let Some(extent) = max.checked_add(*max_field_end),
        if let Some(family_end) = owner.checked_add(extent),
        data_section_range(section_start, section_end),
        if *owner >= *section_start && family_end <= *section_end;

    // Real ELF object symbols are authoritative physical boundaries.  A sized
    // object may own the family; partial overlaps and interior object starts
    // reject the anonymous interpretation.
    #[local] relation authoritative_sized_data_object(Address, usize);
    authoritative_sized_data_object(*address, *size) <--
        symbol_table(address, size, symbol_type, _, _, _, _, _, _),
        if *symbol_type == "OBJECT" && *size > 0;

    #[local] relation bounded_family_authoritative_overlap(Address, Address, u64, usize, u64);
    bounded_family_authoritative_overlap(*func, *origin, *stride, *count, *max) <--
        bounded_family_extent(func, origin, stride, count, max, owner, family_end),
        authoritative_sized_data_object(object_start, object_size),
        if let Some(object_end) = object_start.checked_add(*object_size as u64),
        if *object_start < *family_end && object_end > *owner;

    #[local] relation bounded_family_authoritative_owner_candidate(Address, Address, u64, usize, u64, Address);
    bounded_family_authoritative_owner_candidate(*func, *origin, *stride, *count, *max, *object_start) <--
        bounded_family_extent(func, origin, stride, count, max, owner, family_end),
        authoritative_sized_data_object(object_start, object_size),
        if let Some(object_end) = object_start.checked_add(*object_size as u64),
        if *object_start <= *owner && *family_end <= object_end;

    #[local] relation bounded_family_authoritative_owner(Address, Address, u64, usize, u64, Address);
    bounded_family_authoritative_owner(func, origin, stride, count, max, selected) <--
        bounded_family_authoritative_owner_candidate(func, origin, stride, count, max, _),
        agg selected = ascent::aggregators::max(owner)
            in bounded_family_authoritative_owner_candidate(func, origin, stride, count, max, owner);

    #[local] relation bounded_family_owner_candidate(Address, Address, u64, usize, u64, Address);
    bounded_family_owner_candidate(func, origin, stride, count, max, owner) <--
        bounded_family_authoritative_owner(func, origin, stride, count, max, owner);
    bounded_family_owner_candidate(*func, *origin, *stride, *count, *max, *owner) <--
        bounded_family_extent(func, origin, stride, count, max, owner, _),
        !bounded_family_authoritative_overlap(func, origin, stride, count, max);

    #[local] relation bounded_family_internal_object_boundary(Address, Address, u64, usize, u64, Address);
    bounded_family_internal_object_boundary(*func, *origin, *stride, *count, *max, *chosen_owner) <--
        bounded_family_owner_candidate(func, origin, stride, count, max, chosen_owner),
        bounded_family_extent(func, origin, stride, count, max, _, family_end),
        symbol_table(object_start, _, symbol_type, _, _, _, _, _, _),
        if *symbol_type == "OBJECT",
        if *object_start > *chosen_owner && *object_start < *family_end;

    bounded_absolute_data_access(*func, *node, chosen_ident, field_offset,
                                 *stride, *count, *origin, *access_width) <--
        bounded_family_owner_candidate(func, origin, stride, count, max, chosen_owner),
        !bounded_family_internal_object_boundary(func, origin, stride, count, max, chosen_owner),
        bounded_data_access_candidate(func, node, _, target, access_width, origin, stride, count, max),
        if let Some(field_offset_u64) = target.checked_sub(*chosen_owner),
        if let Ok(field_offset) = i64::try_from(field_offset_u64),
        if let Ok(chosen_ident) = Ident::try_from(*chosen_owner);

    // Candidate two-operand unsigned-magic multiplies activate the raw-value
    // analysis before the magic has itself been validated.  This avoids a
    // circular bootstrap while keeping the lattice out of functions which
    // have no relevant multiply at all.
    #[local] relation raw_magic_imul_candidate(Address, Address, Mreg, Mreg);
    raw_magic_imul_candidate(*func, *addr, dst_mreg, src_mreg) <--
        pimul(addr, dst, src),
        op_register(dst, dst_str),
        op_register(src, src_str),
        if x86_gpr_view_width(dst_str) == Some(8),
        if x86_gpr_view_width(src_str) == Some(8),
        let dst_mreg = Mreg::x86(dst_str),
        let src_mreg = Mreg::x86(src_str),
        if dst_mreg != src_mreg,
        instr_in_function(addr, func);

    #[local] relation raw_gpr_analysis_width(Address, i64);
    raw_gpr_analysis_width(*func, 4) <--
        raw_magic_imul_candidate(func, _, _, _);
    raw_gpr_analysis_width(*func, 8) <--
        raw_magic_imul_candidate(func, _, _, _);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_64(magic_load, _, _, _, _, _),
        instr_in_function(magic_load, func);
    raw_gpr_analysis_width(*func, 8) <--
        div_magic_64(magic_load, _, _, _, _, _),
        instr_in_function(magic_load, func);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_32(addr, _, _, _, _, _),
        instr_in_function(addr, func);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_32_compensating_gcc(addr, _, _, _, _, _),
        instr_in_function(addr, func);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_32_compensating(addr, _, _, _, _, _),
        instr_in_function(addr, func);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_32_signbias_partial(addr, _, _, _, _, _),
        instr_in_function(addr, func);
    raw_gpr_analysis_width(*func, 4) <--
        div_magic_32_signbias(addr, _, _, _, _, _),
        instr_in_function(addr, func);

    #[local] relation raw_gpr_tracked(Address, Mreg, i64);
    raw_gpr_tracked(*func, *mreg, *width) <--
        raw_gpr_analysis_width(func, width),
        preg_of(mreg, preg),
        ireg_of(preg, _);

    #[local] relation raw_gpr_barrier(Address);
    raw_gpr_barrier(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("CALL");

    // An unresolved indirect jump has omitted successors by construction.
    // A MUST value proof in such a function cannot silently treat those arms
    // as absent.  Resolved jump tables are ordinary `branch` edges and do not
    // trigger this conservative veto.
    #[local] relation raw_gpr_unresolved_owner(Address);
    raw_gpr_unresolved_owner(*func) <--
        ddisasm_cfg_edge(site, _, "indirect"),
        instr_in_function(site, func);

    #[local] relation raw_gpr_width(i64);
    raw_gpr_width(4);
    raw_gpr_width(8);

    #[local] relation raw_gpr_immediate_def(Address, Mreg, i64, u64);
    raw_gpr_immediate_def(*addr, dst_mreg, *width, value) <--
        pmov(addr, dst, src),
        instruction(addr, _, _, "MOV", _, _, _, _, _, _),
        op_register(dst, dst_str),
        op_immediate(src, immediate, _),
        raw_gpr_width(width),
        if let Some(value) = exact_mov_immediate_value(dst_str, *immediate, *width),
        let dst_mreg = Mreg::x86(dst_str);

    #[local] relation raw_gpr_copy_def(Address, Mreg, i64, Mreg);
    raw_gpr_copy_def(*addr, dst_mreg, *width, src_mreg) <--
        pmov(addr, dst, src),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        op_register(dst, dst_str),
        op_register(src, src_str),
        raw_gpr_width(width),
        if raw_move_preserves_width(mnem, dst_str, src_str, *width),
        let dst_mreg = Mreg::x86(dst_str),
        let src_mreg = Mreg::x86(src_str);

    #[local] relation raw_gpr_exact_def(Address, Mreg, i64);
    raw_gpr_exact_def(addr, dst, width) <--
        raw_gpr_immediate_def(addr, dst, width, _);
    raw_gpr_exact_def(addr, dst, width) <--
        raw_gpr_copy_def(addr, dst, width, _);

    // Flat exact/unknown value state.  Every key stores one constant-sized
    // lattice element: Bottom (unreached), one exact symbolic value, or Top
    // (disagreeing/unknown).  This is O(V * GPRs) per activated width.
    #[local] lattice raw_gpr_value_in(Address, Address, Mreg, i64, ConstPropagation<RawGprValue>);
    #[local] lattice raw_gpr_value_out(Address, Address, Mreg, i64, ConstPropagation<RawGprValue>);

    raw_gpr_value_in(*func, *func, *reg, *width,
                     ConstPropagation::Constant(RawGprValue::LiveIn(*reg, *width))) <--
        raw_gpr_tracked(func, reg, width),
        instr_in_function(func, func);

    raw_gpr_value_in(*func, *succ, *reg, *width, state.clone()) <--
        raw_gpr_value_out(func, addr, reg, width, state),
        cfg_step(addr, succ),
        instr_in_function(succ, func);

    raw_gpr_value_out(*func, *addr, *reg, *width,
                      ConstPropagation::Constant(RawGprValue::Constant(*value))) <--
        raw_gpr_value_in(func, addr, reg, width, _),
        raw_gpr_immediate_def(addr, reg, width, value),
        !raw_gpr_barrier(addr);

    raw_gpr_value_out(*func, *addr, *reg, *width, source_state.clone()) <--
        raw_gpr_value_in(func, addr, reg, width, _),
        raw_gpr_copy_def(addr, reg, width, source),
        raw_gpr_value_in(func, addr, source, width, source_state),
        !raw_gpr_barrier(addr);

    raw_gpr_value_out(*func, *addr, *reg, *width,
                      ConstPropagation::Constant(RawGprValue::Definition(*addr, *reg, *width))) <--
        raw_gpr_value_in(func, addr, reg, width, _),
        reg_def(addr, reg),
        !raw_gpr_exact_def(addr, reg, width),
        !raw_gpr_barrier(addr);

    raw_gpr_value_out(*func, *addr, *reg, *width, state.clone()) <--
        raw_gpr_value_in(func, addr, reg, width, state),
        !reg_def(addr, reg),
        !raw_gpr_barrier(addr);

    raw_gpr_value_out(*func, *addr, *reg, *width, ConstPropagation::Top) <--
        raw_gpr_value_in(func, addr, reg, width, _),
        raw_gpr_barrier(addr);

    // Reading a recursively improving lattice directly can leak an early
    // Constant before a later predecessor joins it to Top.  Project both in a
    // lower stratum, then publish exactness only through negated conflict.
    #[local] relation raw_gpr_value_candidate(Address, Address, Mreg, i64, RawGprValue);
    raw_gpr_value_candidate(*func, *addr, *reg, *width, value) <--
        raw_gpr_value_in(func, addr, reg, width, state),
        if let ConstPropagation::Constant(value) = state;

    #[local] relation raw_gpr_value_conflict(Address, Address, Mreg, i64);
    raw_gpr_value_conflict(*func, *addr, *reg, *width) <--
        raw_gpr_value_in(func, addr, reg, width, state),
        if matches!(state, ConstPropagation::Top);

    #[local] relation raw_gpr_exact_value(Address, Address, Mreg, i64, RawGprValue);
    raw_gpr_exact_value(*func, *addr, *reg, *width, *value) <--
        raw_gpr_value_candidate(func, addr, reg, width, value),
        !raw_gpr_value_conflict(func, addr, reg, width),
        !raw_gpr_unresolved_owner(func);

    // Point-keyed may-state for scalar dwords copied into XMM registers.  This
    // follows only structural CFG edges, and each tuple is killed exactly when
    // its XMM register is redefined.  PSHUFD $0 replaces/extends that state
    // with a four-lane broadcast tied to the original scalar-read node.
    // Only a 16-byte SIMD store to memory consumes this state, so a function
    // without one need not run the dataflow at all; seeding it everywhere
    // propagates a set across every instruction in the binary for nothing.
    #[local] relation func_has_wide_simd_store(Address);
    func_has_wide_simd_store(func) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if matches!(*mnem, "MOVUPS" | "MOVAPS" | "MOVDQU" | "MOVDQA"),
        pmov(addr, mem_sym, src_sym),
        op_register(src_sym, _),
        op_indirect(mem_sym, _, _, _, _, _, mem_size),
        if *mem_size == 16,
        instr_in_function(addr, func);

    #[local] relation simd_scalar_xmm_seed(Address, Mreg, Mreg);
    simd_scalar_xmm_seed(addr, xmm_mreg, value_mreg) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "MOVD" || *mnem == "VMOVD",
        pmov(addr, xmm_sym, value_sym),
        op_register(xmm_sym, xmm_str),
        reg_xmm(xmm_str),
        op_register(value_sym, value_str),
        !reg_xmm(value_str),
        let xmm_mreg = Mreg::x86(xmm_str),
        let value_mreg = Mreg::x86(value_str),
        instr_in_function(addr, func),
        func_has_wide_simd_store(func);

    #[local] lattice simd_broadcast_in(Address, Set<(Mreg, Mreg, Address)>);
    #[local] lattice simd_broadcast_out(Address, Set<(Mreg, Mreg, Address)>);

    simd_broadcast_in(*succ, active.clone()) <--
        simd_broadcast_out(addr, active),
        cfg_step(addr, succ);

    simd_broadcast_out(*addr, Set::singleton((*xmm, *value_mreg, *origin))) <--
        simd_broadcast_in(addr, active),
        for (xmm, value_mreg, origin) in active.0.iter(),
        !reg_def(addr, *xmm);

    simd_broadcast_out(*addr, Set::singleton((*xmm, *value_mreg, *addr))) <--
        simd_scalar_xmm_seed(addr, xmm, value_mreg);

    simd_broadcast_out(*shuffle_addr, Set::singleton((dst_mreg, *value_mreg, *origin))) <--
        instruction(shuffle_addr, _, _, "PSHUFD", src_sym, dst_sym, imm_sym, _, _, _),
        op_register(src_sym, src_str),
        op_register(dst_sym, dst_str),
        op_immediate(imm_sym, imm, _),
        if *imm == 0,
        let src_mreg = Mreg::x86(src_str),
        let dst_mreg = Mreg::x86(dst_str),
        simd_broadcast_in(shuffle_addr, active),
        for (active_xmm, value_mreg, origin) in active.0.iter(),
        if *active_xmm == src_mreg;

    simd_dword_broadcast_store(*store_addr, *origin, base_str, idx_str, *scale, *disp, *value_mreg) <--
        instruction(store_addr, _, _, store_mnem, _, _, _, _, _, _),
        if matches!(*store_mnem, "MOVUPS" | "MOVAPS" | "MOVDQU" | "MOVDQA"),
        pmov(store_addr, mem_sym, store_src_sym),
        op_register(store_src_sym, store_src_str),
        let store_src_mreg = Mreg::x86(store_src_str),
        simd_broadcast_in(store_addr, active),
        for (active_xmm, value_mreg, origin) in active.0.iter(),
        if *active_xmm == store_src_mreg,
        op_indirect(mem_sym, _, base_str, idx_str, scale, disp, mem_size),
        if *mem_size == 16,
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        if (!base_str.ends_with("BP") && !base_str.ends_with("SP")) || (*idx_str != "NONE" && !idx_str.is_empty()),
        let addrmode = Addrmode {
            base: Some(Ireg::from(base_str)),
            index: if *idx_str != "NONE" && !idx_str.is_empty() {
                Some((Ireg::from(idx_str), *scale))
            } else {
                None
            },
            disp: Displacement::from(*disp),
        },
        if transl_addressing_rev(addrmode, None).is_ok();

    // Preserve supported packed-dword values as event provenance.  A previous
    // implementation remembered only the three global addresses and replayed
    // every read at the eventual frame spill.  That changes behavior whenever
    // memory is written, a call occurs, or an externally visible object changes
    // between vector instructions.  Here every definition names the preceding
    // definition event and the memory operand read at this exact CFG point.
    #[local] relation simd_dword_frame_spill_site(Address, Mreg, i64);
    simd_dword_frame_spill_site(*addr, Mreg::x86(src_name), disp - depth) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if is_wide_simd_mov_mnem(mnem),
        op_register(src, src_name),
        reg_xmm(src_name),
        op_indirect(dst, _, base, index, _, disp, width),
        if Mreg::x86(*base) == Mreg::SP,
        if *index == "NONE" || index.is_empty(),
        if *width == 16,
        sp_frame_shift(addr, depth),
        if (*disp - *depth) % 4 == 0;
    simd_dword_frame_spill_site(*addr, Mreg::x86(src_name), *disp) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if is_wide_simd_mov_mnem(mnem),
        op_register(src, src_name),
        reg_xmm(src_name),
        op_indirect(dst, _, base, index, _, disp, width),
        if Mreg::x86(*base) == Mreg::BP,
        if *index == "NONE" || index.is_empty(),
        if *width == 16,
        if *disp % 4 == 0,
        instr_in_function(addr, func),
        func_has_frame_pointer(func);

    #[local] relation func_has_simd_dword_frame_spill(Address);
    func_has_simd_dword_frame_spill(func) <--
        simd_dword_frame_spill_site(addr, _, _),
        instr_in_function(addr, func);

    #[local] relation simd_dword_global_seed(Address, Mreg, Address);
    simd_dword_global_seed(*addr, Mreg::x86(dst_name), *target) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if matches!(*mnem,
            "MOVDQA" | "MOVDQU" | "MOVAPS" | "MOVUPS"
            | "VMOVDQA" | "VMOVDQU" | "VMOVAPS" | "VMOVUPS"),
        op_indirect(src, _, base, index, _, _, width),
        reg_ip(*base),
        if *index == "NONE" || index.is_empty(),
        if *width == 16,
        rip_target_addr(addr, target),
        if simd_dword_load_alignment_ok(mnem, *target),
        op_register(dst, dst_name),
        reg_xmm(dst_name),
        instr_in_function(addr, func),
        func_has_simd_dword_frame_spill(func);

    // (event, operation, input carrier, destination carrier, memory target).
    // Legacy packed operations are two-address; AVX is three-address and must
    // read src1 rather than the previous value of dst.
    #[local] relation simd_dword_mem_binop(Address, i64, Mreg, Mreg, Address);
    simd_dword_mem_binop(
        *addr,
        kind,
        Mreg::x86(dst_name),
        Mreg::x86(dst_name),
        *target,
    ) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        if !mnem.starts_with('V'),
        if let Some(kind) = simd_dword_binop_kind(mnem),
        op_indirect(src, _, base, index, _, _, width),
        reg_ip(*base),
        if *index == "NONE" || index.is_empty(),
        if *width == 16,
        rip_target_addr(addr, target),
        // Legacy SSE packed arithmetic faults on a misaligned m128 operand.
        // Preserve that contract rather than silently scalarizing a load that
        // the original instruction could not perform.
        if *target % 16 == 0,
        op_register(dst, dst_name),
        reg_xmm(dst_name),
        instr_in_function(addr, func),
        func_has_simd_dword_frame_spill(func);

    simd_dword_mem_binop(
        *addr,
        kind,
        Mreg::x86(input_name),
        Mreg::x86(dst_name),
        *target,
    ) <--
        instruction(addr, _, _, mnem, src1, dst, src2, _, _, _),
        if mnem.starts_with('V'),
        !avx_masked_site(addr),
        if let Some(kind) = simd_dword_binop_kind(mnem),
        op_register(src1, input_name),
        reg_xmm(input_name),
        op_indirect(src2, _, base, index, _, _, width),
        reg_ip(*base),
        if *index == "NONE" || index.is_empty(),
        if *width == 16,
        rip_target_addr(addr, target),
        // VEX.128 packed arithmetic permits unaligned m128 operands; dword
        // alignment is enough for the four scalar lane loads we emit.
        if *target % 4 == 0,
        op_register(dst, dst_name),
        reg_xmm(dst_name),
        instr_in_function(addr, func),
        func_has_simd_dword_frame_spill(func);

    // A whole-register copy does not read memory and therefore aliases the
    // same scalar lane definitions.  It changes only which architectural XMM
    // name carries them.
    #[local] relation simd_dword_reg_copy(Address, Mreg, Mreg);
    simd_dword_reg_copy(*addr, Mreg::x86(dst_name), Mreg::x86(src_name)) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if is_wide_simd_mov_mnem(mnem),
        op_register(src, src_name),
        reg_xmm(src_name),
        op_register(dst, dst_name),
        reg_xmm(dst_name);

    #[local] relation simd_dword_call_barrier(Address);
    simd_dword_call_barrier(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("CALL");

    #[local] relation simd_dword_lane_barrier(Address);
    simd_dword_lane_barrier(addr) <-- simd_dword_call_barrier(addr);
    // VZEROALL has no explicit operands and the decoder intentionally omits
    // its implicit XMM definitions.  It still destroys every low 128-bit
    // carrier.  VZEROUPPER is not a barrier because it preserves those bits.
    simd_dword_lane_barrier(*addr) <--
        instruction(addr, _, _, "VZEROALL", _, _, _, _, _, _);
    // Whole-state restores implicitly redefine some or all XMM registers; the
    // selected component depends on architectural state/masks that are not
    // represented as per-register Capstone definitions.
    simd_dword_lane_barrier(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if matches!(*mnem,
            "FXRSTOR" | "FXRSTOR64"
            | "XRSTOR" | "XRSTOR64"
            | "XRSTORS" | "XRSTORS64");

    // A RET does not observe every caller-saved XMM register.  It observes an
    // XMM value only when that register carries the ABI result.  Prove the
    // disjoint integer-result case early and structurally: every reachable
    // return must have some AX definition on every incoming path.  Unknown is
    // explicit, so a branch bypassing all AX definitions keeps the return
    // conservative.  This point-keyed lattice avoids both address-order
    // guesses and a materialized def-to-return relation.
    #[local] lattice simd_gp_return_in(Address, Set<(Address, SimdDwordDefinition)>);
    #[local] lattice simd_gp_return_out(Address, Set<(Address, SimdDwordDefinition)>);

    simd_gp_return_in(*func, Set::singleton((*func, SimdDwordDefinition::Unknown))) <--
        func_has_simd_dword_frame_spill(func),
        instr_in_function(func, func);

    simd_gp_return_in(*succ, Set::singleton((*func, *definition))) <--
        simd_gp_return_out(addr, state),
        for (func, definition) in state.0.iter(),
        cfg_step(addr, succ),
        instr_in_function(succ, func);

    simd_gp_return_out(*addr, Set::singleton((*func, *definition))) <--
        simd_gp_return_in(addr, state),
        for (func, definition) in state.0.iter(),
        !reg_def(addr, Mreg::AX);

    simd_gp_return_out(*addr, Set::singleton((*func, SimdDwordDefinition::Event(*addr)))) <--
        simd_gp_return_in(addr, state),
        for (func, _) in state.0.iter(),
        reg_def(addr, Mreg::AX);

    #[local] relation simd_gp_return_site(Address, Address);
    simd_gp_return_site(*func, *ret) <--
        mach_inst(ret, ?MachInst::Mreturn),
        instr_in_function(ret, func),
        func_has_simd_dword_frame_spill(func);

    #[local] relation simd_gp_return_state_at(Address, Address);
    simd_gp_return_state_at(*func, *ret) <--
        simd_gp_return_site(func, ret),
        simd_gp_return_in(ret, state),
        for (active_func, _) in state.0.iter(),
        if active_func == func;

    #[local] relation simd_gp_return_unproven(Address);
    simd_gp_return_unproven(*func) <--
        simd_gp_return_site(func, ret),
        !simd_gp_return_state_at(func, ret);
    simd_gp_return_unproven(*func) <--
        simd_gp_return_site(func, ret),
        simd_gp_return_in(ret, state),
        for (active_func, definition) in state.0.iter(),
        if active_func == func && matches!(definition, SimdDwordDefinition::Unknown);

    #[local] relation simd_gp_return_proven(Address);
    simd_gp_return_proven(*func) <--
        simd_gp_return_site(func, _),
        !simd_gp_return_unproven(func);

    // ABI exits and architectural state-save instructions can observe live
    // XMM values without Capstone listing every carrier as an explicit read.
    // Keep this separate from barriers: an FXSAVE/XSAVE reads the state but
    // does not destroy it, while a return has no successor to propagate to.
    #[local] relation simd_dword_implicit_observer(Address);
    simd_dword_implicit_observer(addr) <-- simd_dword_call_barrier(addr);
    simd_dword_implicit_observer(*addr) <--
        mach_inst(addr, ?MachInst::Mreturn),
        instr_in_function(addr, func),
        !simd_gp_return_proven(func);
    simd_dword_implicit_observer(*addr) <-- mach_inst(addr, ?MachInst::Mtailcall(_));
    simd_dword_implicit_observer(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if matches!(*mnem,
            "FXSAVE" | "FXSAVE64"
            | "XSAVE" | "XSAVE64"
            | "XSAVEC" | "XSAVEC64"
            | "XSAVEOPT" | "XSAVEOPT64"
            | "XSAVES" | "XSAVES64");

    // Total per-path state for only the XMM names relevant to a candidate
    // chain.  `Unknown` is a real lattice element: omitting it would make a CFG
    // join of {known definition} and {no tracked definition} look spuriously
    // must-known after set union.  Entry, unsupported definitions, and calls
    // therefore publish Unknown explicitly.
    #[local] relation simd_dword_tracked_reg(Address, Mreg);
    simd_dword_tracked_reg(*func, *dst) <--
        simd_dword_global_seed(addr, dst, _),
        instr_in_function(addr, func);
    simd_dword_tracked_reg(*func, *dst) <--
        simd_dword_mem_binop(addr, _, _, dst, _),
        instr_in_function(addr, func);
    simd_dword_tracked_reg(*func, *input) <--
        simd_dword_mem_binop(addr, _, input, _, _),
        instr_in_function(addr, func);
    simd_dword_tracked_reg(*func, *dst) <--
        simd_dword_reg_copy(addr, dst, _),
        instr_in_function(addr, func);
    simd_dword_tracked_reg(*func, *src) <--
        simd_dword_reg_copy(addr, _, src),
        instr_in_function(addr, func);
    simd_dword_tracked_reg(*func, *xmm) <--
        simd_dword_frame_spill_site(store, xmm, _),
        instr_in_function(store, func);

    #[local] relation simd_dword_supported_def(Address, Mreg);
    simd_dword_supported_def(*addr, *dst) <-- simd_dword_global_seed(addr, dst, _);
    simd_dword_supported_def(*addr, *dst) <-- simd_dword_mem_binop(addr, _, _, dst, _);
    simd_dword_supported_def(*addr, *dst) <-- simd_dword_reg_copy(addr, dst, _);

    // Acceptance replaces the ordinary wide definitions with scalar lane
    // values.  Therefore every architectural read of a tracked carrier must
    // also belong to the proved chain; otherwise an intervening MOVD/PTEST,
    // unrelated vector store, or unsupported packed consumer would read a
    // value whose original definition was removed.
    #[local] relation simd_dword_supported_use(Address, Mreg);
    simd_dword_supported_use(*addr, *input) <--
        simd_dword_mem_binop(addr, _, input, _, _);
    simd_dword_supported_use(*addr, *src) <--
        simd_dword_reg_copy(addr, _, src);
    simd_dword_supported_use(*store, *xmm) <--
        simd_dword_frame_spill_site(store, xmm, _);

    #[local] relation simd_dword_unsupported_use(Address, Mreg);
    simd_dword_unsupported_use(*addr, *xmm) <--
        reg_use(addr, xmm),
        instr_in_function(addr, func),
        simd_dword_tracked_reg(func, xmm),
        !simd_dword_supported_use(addr, xmm);

    // Tuple: (function owner, XMM register, definition state).  The lattice is
    // keyed by the current CFG point; joins union possible path states.  No
    // address or node ordering is used.
    #[local] lattice simd_dword_lane_in(Address, Set<(Address, Mreg, SimdDwordDefinition)>);
    #[local] lattice simd_dword_lane_out(Address, Set<(Address, Mreg, SimdDwordDefinition)>);

    simd_dword_lane_in(*func, Set::singleton((*func, *xmm, SimdDwordDefinition::Unknown))) <--
        func_has_simd_dword_frame_spill(func),
        simd_dword_tracked_reg(func, xmm),
        instr_in_function(func, func);

    simd_dword_lane_in(*succ, Set::singleton((*func, *xmm, *definition))) <--
        simd_dword_lane_out(addr, state),
        for (func, xmm, definition) in state.0.iter(),
        cfg_step(addr, succ),
        instr_in_function(succ, func);

    // Every consumer of a concrete event is part of its proof obligation.
    // The imperative finalizer accepts only a component closed over these
    // uses, so a recognized-but-unused branch, rejected spill, raw XMM copy,
    // or unsupported consumer cannot read a definition that scalarization
    // later removes.  Calls are conservative implicit consumers because ABI
    // argument reads are not present in Capstone's explicit reg_use facts.
    #[local] relation simd_dword_event_use(Address, Address);
    simd_dword_event_use(*addr, *event) <--
        reg_use(addr, xmm),
        instr_in_function(addr, func),
        simd_dword_lane_in(addr, state),
        for (active_func, active_xmm, definition) in state.0.iter(),
        if let SimdDwordDefinition::Event(event) = definition,
        if active_func == func && active_xmm == xmm;
    simd_dword_event_use(*addr, *event) <--
        simd_dword_implicit_observer(addr),
        instr_in_function(addr, func),
        simd_dword_lane_in(addr, state),
        for (active_func, _, definition) in state.0.iter(),
        if let SimdDwordDefinition::Event(event) = definition,
        if active_func == func;

    simd_dword_lane_out(*addr, Set::singleton((*func, *xmm, *definition))) <--
        simd_dword_lane_in(addr, state),
        for (func, xmm, definition) in state.0.iter(),
        !reg_def(*addr, *xmm),
        !simd_dword_lane_barrier(addr),
        !simd_dword_unsupported_use(*addr, *xmm);

    simd_dword_lane_out(*addr, Set::singleton((*func, *xmm, SimdDwordDefinition::Unknown))) <--
        simd_dword_lane_in(addr, state),
        for (func, xmm, _) in state.0.iter(),
        simd_dword_unsupported_use(*addr, *xmm);

    simd_dword_lane_out(*addr, Set::singleton((*func, *xmm, SimdDwordDefinition::Unknown))) <--
        reg_def(addr, xmm),
        instr_in_function(addr, func),
        simd_dword_tracked_reg(func, xmm),
        !simd_dword_supported_def(addr, xmm),
        !simd_dword_lane_barrier(addr);

    simd_dword_lane_out(*addr, Set::singleton((*func, *xmm, SimdDwordDefinition::Unknown))) <--
        simd_dword_lane_barrier(addr),
        instr_in_function(addr, func),
        simd_dword_tracked_reg(func, xmm);

    #[local] relation simd_dword_event_candidate(Address, i64, Address, Address);
    simd_dword_lane_out(*addr, Set::singleton((*func, *dst, SimdDwordDefinition::Event(*addr)))),
    simd_dword_event_candidate(*addr, 0, 0, *target) <--
        simd_dword_global_seed(addr, dst, target),
        instr_in_function(addr, func);

    simd_dword_lane_out(*addr, Set::singleton((*func, *dst, SimdDwordDefinition::Event(*addr)))),
    simd_dword_event_candidate(*addr, *kind, *input, *target) <--
        simd_dword_mem_binop(addr, kind, input_xmm, dst, target),
        instr_in_function(addr, func),
        simd_dword_lane_in(addr, state),
        for (active_func, active_xmm, definition) in state.0.iter(),
        if let SimdDwordDefinition::Event(input) = definition,
        if active_func == func && active_xmm == input_xmm;

    #[local] relation simd_dword_event_uncertain(Address);
    simd_dword_lane_out(*addr, Set::singleton((*func, *dst, SimdDwordDefinition::Unknown))),
    simd_dword_event_uncertain(*addr) <--
        simd_dword_mem_binop(addr, _, input_xmm, dst, _),
        instr_in_function(addr, func),
        simd_dword_lane_in(addr, state),
        for (active_func, active_xmm, definition) in state.0.iter(),
        if matches!(definition, SimdDwordDefinition::Unknown),
        if active_func == func && active_xmm == input_xmm;

    simd_dword_lane_out(*addr, Set::singleton((*func, *dst, *definition))) <--
        simd_dword_reg_copy(addr, dst, src),
        instr_in_function(addr, func),
        simd_dword_lane_in(addr, state),
        for (active_func, active_xmm, definition) in state.0.iter(),
        if active_func == func && active_xmm == src;

    #[local] relation simd_dword_frame_store_candidate(Address, i64, Address);
    simd_dword_frame_store_candidate(*store, *frame_ofs, *definition) <--
        simd_dword_frame_spill_site(store, xmm, frame_ofs),
        instr_in_function(store, func),
        simd_dword_lane_in(store, state),
        for (active_func, active_xmm, source) in state.0.iter(),
        if let SimdDwordDefinition::Event(definition) = source,
        if active_func == func && active_xmm == xmm;

    #[local] relation simd_dword_frame_store_uncertain(Address);
    simd_dword_frame_store_uncertain(*store) <--
        simd_dword_frame_spill_site(store, xmm, _),
        instr_in_function(store, func),
        simd_dword_lane_in(store, state),
        for (active_func, active_xmm, definition) in state.0.iter(),
        if matches!(definition, SimdDwordDefinition::Unknown),
        if active_func == func && active_xmm == xmm;

    // These projections make the relations pass outputs; Ascent lattice users
    // can observe improving intermediate values, so AsmPass::run replaces them
    // with the unique, fully linked chains from the settled state below.
    simd_dword_lane_event(event, kind, input, target) <--
        simd_dword_event_candidate(event, kind, input, target);
    simd_dword_lane_frame_store(store, frame_ofs, definition) <--
        simd_dword_frame_store_candidate(store, frame_ofs, definition);

    // XMM high lane (bits 64..127) of a wide frame move.
    //
    // CompCert's memory model has no 128-bit chunk, so a `movaps [rsp+N], xmm`
    // lifts as a single 8-byte Msetstack and the upper half is simply dropped.
    // That is how gcc builds every constant-initialized aggregate that lives in
    // the frame, so half of such an object's words vanish AND the frame is left
    // with an 8-byte hole at each odd cell, which splits one array into
    // unrelated scalars and leaves it undersized.  These rules recover the
    // upper half as a second 64-bit value: a point-keyed may-state says what
    // each XMM's high lane currently holds, and rtl_pass turns the wide store
    // into a second frame-cell move at offset+8.

    // A 16-byte-or-wider frame move, in each direction; the offset is the low
    // cell, exactly as the Msetstack/Mgetstack rules above record it.
    #[local] relation sse_wide_frame_store(Address, Mreg, i64);
    sse_wide_frame_store(*addr, Mreg::x86(srcstr), disp - depth) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        op_indirect(dst, _, base, idx, _, disp, msize),
        if Mreg::x86(base) == Mreg::SP,
        if *idx == "NONE",
        if *msize > 8,
        sp_frame_shift(addr, depth);

    sse_wide_frame_store(*addr, Mreg::x86(srcstr), *disp) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        op_indirect(dst, _, base, idx, _, disp, msize),
        if Mreg::x86(base) == Mreg::BP,
        if *idx == "NONE",
        if *msize > 8,
        instr_in_function(addr, func),
        func_has_frame_pointer(func);

    // The same 16-byte move, but through a general register base rather than a
    // frame slot: a heap object, a struct field, an out-parameter.  The two
    // rules above only reach SP/BP destinations, so this shape dropped its
    // upper 8 bytes with nothing to recover them -- gcc initializes a
    // malloc'd record with one `movups`, and the odd quadword then reads as
    // whatever the allocator left there.  The addressing travels with the fact
    // because rtl_pass has to rebuild it at +8.
    relation sse_wide_mem_store(Address, Mreg, &'static str, &'static str, i64, i64);
    sse_wide_mem_store(*addr, Mreg::x86(srcstr), base, idx, *scale, *disp) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        op_indirect(dst, _, base, idx, scale, disp, msize),
        if *msize > 8,
        if *base != "NONE" && !base.is_empty(),
        !reg_ip(base),
        if (!base.ends_with("BP") && !base.ends_with("SP")) || (*idx != "NONE" && !idx.is_empty()),
        !simd_dword_broadcast_store(addr, _, _, _, _, _, _);

    // The same 16-byte move again, to a RIP-relative destination: a global
    // aggregate.  The general-base rule above excludes an IP base because the
    // +8 addressing has to be rebuilt through a symbol, not a register: carry
    // the resolved absolute target and let rtl_pass restate it as
    // Aglobal(ident, ofs + 8) -- the same resolution seed kind 3 already uses
    // for its RIP-relative source, applied to the destination side.  The
    // broadcast-store exclusion the register form needs is structural here:
    // simd_dword_broadcast_store itself rejects an IP base.
    relation sse_wide_global_store(Address, Mreg, Address);
    sse_wide_global_store(*addr, Mreg::x86(srcstr), *target) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        op_indirect(dst, _, base, idx, _, _, msize),
        if *msize > 8,
        reg_ip(*base),
        if *idx == "NONE" || idx.is_empty(),
        rip_target_addr(addr, target);

    relation sse_wide_frame_load(Address, Mreg, i64);
    sse_wide_frame_load(*addr, Mreg::x86(dststr), disp - depth) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_indirect(src, _, base, idx, _, disp, msize),
        if Mreg::x86(base) == Mreg::SP,
        if *idx == "NONE",
        if *msize > 8,
        sp_frame_shift(addr, depth);

    sse_wide_frame_load(*addr, Mreg::x86(dststr), *disp) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_indirect(src, _, base, idx, _, disp, msize),
        if Mreg::x86(base) == Mreg::BP,
        if *idx == "NONE",
        if *msize > 8,
        instr_in_function(addr, func),
        func_has_frame_pointer(func);

    // MOVHPS is a partial register write: its low 64 bits are unchanged while
    // the memory operand replaces bits 64..127. A low-lane Omove preserves the
    // part represented by ordinary Mach registers; movhps_hi_load carries the
    // other effect to RTL. Frame displacements use the same canonical SP
    // coordinate as every other stack reference.
    #[local] relation movhps_mem_operand(Address, Mreg, &'static str, &'static str, i64, i64);
    movhps_mem_operand(*addr, Mreg::x86(dststr), base, idx, *scale, *disp) <--
        instruction(addr, _, _, "MOVHPS", src, dst, _, _, _, _),
        op_indirect(src, _, base, idx, scale, disp, msize),
        if *msize == 8,
        op_register(dst, dststr),
        reg_xmm(dststr);

    movhps_hi_load(*addr, *dst, base, idx, *scale, disp - depth, true) <--
        movhps_mem_operand(addr, dst, base, idx, scale, disp),
        if Mreg::x86(base) == Mreg::SP,
        sp_frame_shift(addr, depth);

    movhps_hi_load(*addr, *dst, base, idx, *scale, *disp, true) <--
        movhps_mem_operand(addr, dst, base, idx, scale, disp),
        if Mreg::x86(base) == Mreg::BP,
        instr_in_function(addr, func),
        func_has_frame_pointer(func);

    movhps_hi_load(*addr, *dst, base, idx, *scale, *disp, false) <--
        movhps_mem_operand(addr, dst, base, idx, scale, disp),
        if Mreg::x86(base) != Mreg::SP && Mreg::x86(base) != Mreg::BP;

    movhps_hi_load(*addr, *dst, base, idx, *scale, *disp, false) <--
        movhps_mem_operand(addr, dst, base, idx, scale, disp),
        if Mreg::x86(base) == Mreg::BP,
        instr_in_function(addr, func),
        !func_has_frame_pointer(func);

    mach_inst(addr, MachInst::Mop(Operation::Omove, Arc::new(vec![*dst]), *dst)) <--
        movhps_hi_load(addr, dst, _, _, _, _, _);

    // The high-lane state is a per-instruction dataflow, so seeding it in a
    // function that never performs a wide store propagates a set through that
    // whole function for nothing.  Only a wide store consumes the state, so
    // confine the analysis to the functions that contain one -- either
    // destination form, since both consume the same seeds.
    #[local] relation func_has_wide_xmm_store(Address);
    func_has_wide_xmm_store(func) <--
        sse_wide_frame_store(addr, _, _),
        instr_in_function(addr, func);
    func_has_wide_xmm_store(func) <--
        sse_wide_mem_store(addr, _, _, _, _, _),
        instr_in_function(addr, func);
    func_has_wide_xmm_store(func) <--
        sse_wide_global_store(addr, _, _),
        instr_in_function(addr, func);

    // The primitive high-lane sources.  Kind 0: zeroed by a GP-to-XMM
    // transfer or a self-XOR.  Kind 1: the low lane of another register, from
    // the quadword interleave gcc uses to pair two pointers.  Kind 2: a frame
    // cell, from a wide frame load; the load address travels with it so the
    // value is read where it is defined.
    #[local] relation xmm_hi_seed(Address, Mreg, i64, Mreg, i64, Address);
    xmm_hi_seed(*addr, Mreg::x86(dststr), 0, Mreg::Unknown, 0, *addr) <--
        instruction(addr, _, _, mnem, _, dst, _, _, _, _),
        !avx_masked_site(addr),
        if simd_zeroes_high_lane_mnem(mnem),
        op_register(dst, dststr),
        reg_xmm(dststr),
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    xmm_hi_seed(*addr, Mreg::x86(dststr), 0, Mreg::Unknown, 0, *addr) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if simd_self_zero_mnem(mnem),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_register(src, srcstr),
        if srcstr == dststr,
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // Kind 5: a self packed-equality compare materializes the exact 128-bit
    // constant -1.  Kind 0 remains zero, so the two constants can never be
    // silently conflated at a CFG join.
    xmm_hi_seed(*addr, Mreg::x86(dststr), 5, Mreg::Unknown, 0, *addr) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if simd_self_all_ones_mnem(mnem),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_register(src, srcstr),
        if srcstr == dststr,
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // The interleave records the site that READ the source, not just the
    // register: the register is free to be reused before the store lands, so
    // rtl_pass resolves the value through the def reaching this instruction.
    xmm_hi_seed(*addr, Mreg::x86(dststr), 1, Mreg::x86(srcstr), 0, *addr) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if simd_hi_from_low_mnem(mnem),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_register(src, srcstr),
        reg_xmm(srcstr),
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // Kind 3: a 16-byte constant in .rodata, reached RIP-relative.  This is how gcc
    // initializes a constant-valued aggregate that lives in the frame -- load the whole
    // constant, store it once -- so the high lane's source is a GLOBAL, which none of the
    // three seeds above can express.  With no seed the wide store's upper half stayed
    // unmodelled and the aggregate's odd cell was never written at all: recovered cp read
    // cp_options.sparse_mode as 0 rather than SPARSE_AUTO and refused every copy with
    // "--reflink can be used only with --sparse=auto".
    //
    // The i64 payload carries the constant's ADDRESS, the same slot in which kind 2 carries
    // a frame offset; rtl_pass loads the high quadword from address+8.
    xmm_hi_seed(*addr, Mreg::x86(dststr), 3, Mreg::Unknown, *target as i64, *addr) <--
        pmov(addr, dst, src),
        !avx_masked_site(addr),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_indirect(src, _, base, idx, _, _, msize),
        reg_ip(*base),
        if *idx == "NONE" || idx.is_empty(),
        if *msize > 8,
        rip_target_addr(addr, target),
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // Kind 4: the explicit high-quadword load emitted for MOVHPS. Encode the
    // site in the scalar payload as well, so distinct loads meeting at a CFG
    // join are ambiguous rather than selecting either memory value.
    xmm_hi_seed(*addr, *dst, 4, Mreg::Unknown, *addr as i64, *addr) <--
        movhps_hi_load(addr, dst, _, _, _, _, _),
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // A whole-register move carries the source's high lane to the destination,
    // so it neither defines a primitive source nor kills what it copies.
    #[local] relation xmm_hi_reg_copy(Address, Mreg, Mreg);
    xmm_hi_reg_copy(*addr, Mreg::x86(dststr), Mreg::x86(srcstr)) <--
        instruction(addr, _, _, mnem, src, dst, _, _, _, _),
        !avx_masked_site(addr),
        if is_wide_simd_mov_mnem(mnem),
        op_register(dst, dststr),
        reg_xmm(dststr),
        op_register(src, srcstr),
        reg_xmm(srcstr);

    // A call clobbers every caller-saved XMM, so no high lane survives it.
    #[local] relation xmm_hi_barrier(Address);
    xmm_hi_barrier(*addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("CALL");

    #[local] lattice xmm_hi_in(Address, Set<(Mreg, i64, Mreg, i64, Address)>);
    #[local] lattice xmm_hi_out(Address, Set<(Mreg, i64, Mreg, i64, Address)>);

    // A wide spill/reload must preserve the high lane just as exactly as the
    // ordinary low-lane Msetstack/Mgetstack pair.  stack_def_used is produced
    // by the downstream stack-analysis pass, so using it here observes an
    // empty relation in the real scheduled pipeline.  Track the upper frame
    // cells in this pass instead, as a point-keyed may lattice over structural
    // CFG edges.  This is O(V * live frame cells), not a pairwise reachability
    // relation.
    #[local] relation xmm_hi_tracked_frame_cell(Address, i64);
    xmm_hi_tracked_frame_cell(*func, *ofs + 8) <--
        sse_wide_frame_load(addr, _, ofs),
        instr_in_function(addr, func),
        func_has_wide_xmm_store(func);

    // Normalize every write to a tracked cell into the same settled-frame
    // coordinate used by sse_wide_frame_{load,store}.  Any such write kills
    // the old cell state; a non-wide write replaces it with an opaque marker.
    #[local] relation xmm_hi_frame_cell_def(Address, i64);
    xmm_hi_frame_cell_def(*addr, cell) <--
        stack_def(addr, base, raw_ofs),
        if Mreg::x86(base) == Mreg::SP,
        sp_frame_shift(addr, depth),
        instr_in_function(addr, func),
        let cell = *raw_ofs - *depth,
        xmm_hi_tracked_frame_cell(func, cell);
    xmm_hi_frame_cell_def(*addr, *raw_ofs) <--
        stack_def(addr, base, raw_ofs),
        if Mreg::x86(base) == Mreg::BP,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        xmm_hi_tracked_frame_cell(func, raw_ofs);

    #[local] relation xmm_hi_known_frame_def(Address, i64, Mreg);
    xmm_hi_known_frame_def(*addr, *ofs + 8, *xmm) <--
        sse_wide_frame_store(addr, xmm, ofs),
        instr_in_function(addr, func),
        xmm_hi_tracked_frame_cell(func, *ofs + 8);

    // Tuple: (settled frame cell, source kind, source register, source payload,
    // source site).  Kind -1 is internal only and denotes a value whose bits
    // are present in the frame but whose producer is not one of the exact high-
    // lane forms.  A reload turns that marker into the public kind-2 cell load.
    #[local] lattice xmm_hi_frame_in(Address, Set<(i64, i64, Mreg, i64, Address)>);
    #[local] lattice xmm_hi_frame_out(Address, Set<(i64, i64, Mreg, i64, Address)>);

    // Every tracked cell exists with unknown provenance at function entry.
    // A definition at the entry instruction kills this marker before it leaves
    // that point, exactly like any later definition.
    xmm_hi_frame_in(*func, Set::singleton((*cell, -1, Mreg::Unknown, 0, *func))) <--
        xmm_hi_tracked_frame_cell(func, cell);

    xmm_hi_frame_in(*succ, state.clone()) <--
        xmm_hi_frame_out(addr, state),
        cfg_step(addr, succ);

    xmm_hi_frame_out(*addr, Set::singleton((*cell, *kind, *src, *ofs, *site))) <--
        xmm_hi_frame_in(addr, state),
        for (cell, kind, src, ofs, site) in state.0.iter(),
        !xmm_hi_frame_cell_def(*addr, *cell);

    xmm_hi_frame_out(*addr, Set::singleton((*cell, -1, Mreg::Unknown, 0, *addr))) <--
        xmm_hi_frame_cell_def(addr, cell),
        !xmm_hi_known_frame_def(addr, cell, _);

    xmm_hi_frame_out(*addr, Set::singleton((*cell, *kind, *src, *ofs, *site))) <--
        xmm_hi_known_frame_def(addr, cell, xmm),
        xmm_hi_in(addr, state),
        for (active_xmm, kind, src, ofs, site) in state.0.iter(),
        if active_xmm == xmm;

    // A reload of a precisely tracked cell restores the producer provenance;
    // an opaque cell still becomes kind 2 so RTL reads its actual frame value.
    xmm_hi_seed(*addr, *xmm, *kind, *src, *source_ofs, *site) <--
        sse_wide_frame_load(addr, xmm, load_ofs),
        xmm_hi_frame_in(addr, frame_state),
        for (cell, kind, src, source_ofs, site) in frame_state.0.iter(),
        if *cell == *load_ofs + 8,
        if *kind >= 0;
    xmm_hi_seed(*addr, *xmm, 2, Mreg::Unknown, *load_ofs, *addr) <--
        sse_wide_frame_load(addr, xmm, load_ofs),
        xmm_hi_frame_in(addr, frame_state),
        for (cell, kind, _, _, _) in frame_state.0.iter(),
        if *cell == *load_ofs + 8,
        if *kind == -1;

    xmm_hi_in(*succ, state.clone()) <--
        xmm_hi_out(addr, state),
        cfg_step(addr, succ);

    xmm_hi_out(*addr, Set::singleton((*xmm, *kind, *src, *ofs, *site))) <--
        xmm_hi_seed(addr, xmm, kind, src, ofs, site);

    // One carry rule for every kind: the entry tuple travels through unchanged as long as
    // the register is neither redefined nor clobbered.  This was three near-identical
    // per-kind rules, each re-stating the payload its own kind uses; that shape is exactly
    // how a kind can end up with a seed and no propagation, so it stays generic.
    xmm_hi_out(*addr, Set::singleton((*xmm, *kind, *src, *ofs, *site))) <--
        xmm_hi_in(addr, state),
        for (xmm, kind, src, ofs, site) in state.0.iter(),
        !reg_def(*addr, *xmm),
        !xmm_hi_barrier(*addr);

    xmm_hi_out(*addr, Set::singleton((*dst, *kind, *src, *ofs, *site))) <--
        xmm_hi_reg_copy(addr, dst, copied),
        xmm_hi_in(addr, state),
        for (xmm, kind, src, ofs, site) in state.0.iter(),
        if xmm == copied;

    // Two different sources reaching one high lane would need a phi the frame
    // cell cannot express, so those stores keep only their recovered low half.
    #[local] relation xmm_hi_ambiguous(Address, Mreg);
    xmm_hi_ambiguous(*addr, *xmm) <--
        xmm_hi_in(addr, state),
        for (xmm, kind, src, ofs, _site) in state.0.iter(),
        for (xmm2, kind2, src2, ofs2, _site2) in state.0.iter(),
        if xmm == xmm2,
        if kind != kind2 || src != src2 || ofs != ofs2;

    // The upper half of a wide frame store, resolved to one source.  Exported
    // for rtl_pass, which materializes it as a frame-cell move at hi_ofs.
    relation xmm_hi_frame_store(Address, i64, i64, Mreg, i64, Address);
    xmm_hi_frame_store(*addr, *disp + 8, *kind, *src, *ofs, *site) <--
        sse_wide_frame_store(addr, xmm, disp),
        !xmm_hi_ambiguous(*addr, *xmm),
        xmm_hi_in(addr, state),
        for (sxmm, kind, src, ofs, site) in state.0.iter(),
        if sxmm == xmm;

    // The same resolution for a general-base destination.  The store's own
    // addressing stays in sse_wide_mem_store, so this carries only the source
    // of the lane, in the same (kind, reg, cell, site) encoding: every seed
    // kind therefore reaches both destination forms with no per-kind work here.
    relation xmm_hi_mem_store(Address, i64, Mreg, i64, Address);
    xmm_hi_mem_store(*addr, *kind, *src, *ofs, *site) <--
        sse_wide_mem_store(addr, xmm, _, _, _, _),
        !xmm_hi_ambiguous(*addr, *xmm),
        xmm_hi_in(addr, state),
        for (sxmm, kind, src, ofs, site) in state.0.iter(),
        if sxmm == xmm;

    // A RIP-relative destination consumes the same resolved state; its own
    // addressing stays in sse_wide_global_store.  One store address can only
    // carry one destination form, so the two rules never claim the same row.
    xmm_hi_mem_store(*addr, *kind, *src, *ofs, *site) <--
        sse_wide_global_store(addr, xmm, _),
        !xmm_hi_ambiguous(*addr, *xmm),
        xmm_hi_in(addr, state),
        for (sxmm, kind, src, ofs, site) in state.0.iter(),
        if sxmm == xmm;

    #[local] relation cmp_jcc_link(Address, Address);
    cmp_jcc_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    cmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _);

    #[local] relation test_jcc_link(Address, Address);
    test_jcc_link(addr0, addr1) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    test_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        ptest(addr0, _, _);

    // Jcc and SETcc read flags without changing them. The conservative
    // is_flag_setting helper intentionally classifies unknown instructions as
    // clobbers, so admit these two recognized flag consumers explicitly. Read
    // the raw instruction stream: trimming emitted IR must not fabricate a
    // flags kill in the physical CFG.
    #[local] relation flags_flow_transparent(Address);
    flags_flow_transparent(addr) <--
        unrefinedinstruction(addr, _, _, mnem, _, _, _, _, _, _),
        if !is_flag_setting(mnem);
    flags_flow_transparent(addr) <-- pjcc(addr, _, _);
    flags_flow_transparent(addr) <-- overflow_jcc(addr, _, _);
    flags_flow_transparent(addr) <-- psetcc(addr, _, _);

    // Point-keyed may-state: at each instruction, which compare/test origins
    // have already had a jcc consume their flags on some incoming CFG path.
    // Union at a branch merge is conservative: if any path consumed the flags,
    // a later shared consumer is secondary and must carry its own condition.
    #[local] lattice flags_consumed_in(Address, Set<Address>);
    #[local] lattice flags_consumed_out(Address, Set<Address>);

    flags_consumed_out(*jcc, Set::singleton(*origin)) <--
        cmp_jcc_link(origin, jcc);
    flags_consumed_out(*jcc, Set::singleton(*origin)) <--
        test_jcc_link(origin, jcc);
    flags_consumed_in(*succ, consumed.clone()) <--
        flags_consumed_out(addr, consumed),
        cfg_step(addr, succ);
    flags_consumed_out(*addr, consumed.clone()) <--
        flags_consumed_in(addr, consumed),
        flags_flow_transparent(addr);

    // Secondary flags consumer: several jccs can consume one compare's flags,
    // so each structurally downstream consumer carries its own Mcond at its OWN
    // address, independent of numeric instruction IDs.
    #[local] relation secondary_flags_consumer(Address, Address);
    secondary_flags_consumer(*origin, *jcc) <--
        cmp_jcc_link(origin, jcc),
        flags_consumed_in(jcc, consumed),
        if consumed.0.contains(origin);
    secondary_flags_consumer(*origin, *jcc) <--
        test_jcc_link(origin, jcc),
        flags_consumed_in(jcc, consumed),
        if consumed.0.contains(origin);

    // Registers whose original values a compare/test condition re-reads.
    #[local] relation flags_arg(Address, Mreg);
    flags_arg(addr, mreg) <--
        pcmp(addr, r1, _),
        op_register(r1, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        pcmp(addr, _, r2),
        op_register(r2, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        ptest(addr, r1, _),
        op_register(r1, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);

    // Exact JO/JNO recovery re-reads the post-operation destination and, for
    // register forms, the source whose bits were consumed by the arithmetic.
    // Register definitions in the flag-transparent shadow invalidate that
    // reconstruction, so feed those operands through the same point-keyed
    // redefinition lattice used by relocated compare conditions.
    flags_arg(addr, mreg) <--
        padd(addr, dst, _),
        op_register(dst, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        padd(addr, _, src),
        op_register(src, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        psub(addr, dst, _),
        op_register(dst, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        psub(addr, _, src),
        op_register(src, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        pneg(addr, dst),
        op_register(dst, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    flags_arg(addr, mreg) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "INC" || *mnem == "DEC",
        op_register(dst, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);

    // A SETcc result is a full logical boolean in the recovered IR even though
    // the machine writes only its low-byte lane. Two such results can therefore
    // be combined by a byte OR/AND/XOR without the stale upper parent-register
    // bits affecting a subsequent ZF branch. Prove that property as CFG-keyed
    // must-state: joins intersect, and every normalized parent write kills.
    // This is O(nodes * register depth), never pairwise reachability.
    #[local] lattice low_byte_boolean_def_set(Address, Set<Mreg>);
    low_byte_boolean_def_set(*node, Set::default()) <--
        instr_in_function(node, _);
    low_byte_boolean_def_set(*node, Set::singleton(*reg)) <--
        reg_def(node, reg);

    #[local] lattice low_byte_boolean_gen_set(Address, Set<Mreg>);
    low_byte_boolean_gen_set(*node, Set::default()) <--
        instr_in_function(node, _);
    low_byte_boolean_gen_set(*addr, Set::singleton(Mreg::x86(*dst_name))) <--
        psetcc(addr, _, dst_symbol),
        op_register(dst_symbol, dst_name),
        if is_reg_8(dst_name),
        if !is_reg_high8(dst_name);

    #[local] lattice low_byte_boolean_in(Address, Address, Dual<Set<Mreg>>);
    low_byte_boolean_in(*func, *func, Dual(Set::default())) <--
        func_span(_, func, _),
        instr_in_function(func, func);

    low_byte_boolean_in(*func, *dst, Dual(low_byte_boolean_transfer(
        &incoming.0,
        definitions,
        generated,
    ))) <--
        low_byte_boolean_in(func, src, incoming),
        cfg_step(src, dst),
        instr_in_function(dst, func),
        low_byte_boolean_def_set(src, definitions),
        low_byte_boolean_gen_set(src, generated);

    #[local] relation low_byte_boolean_logical_operands(Address, Symbol, Symbol);
    low_byte_boolean_logical_operands(addr, dst, src) <-- por(addr, dst, src);
    low_byte_boolean_logical_operands(addr, dst, src) <-- pand(addr, dst, src);
    low_byte_boolean_logical_operands(addr, dst, src) <-- pxor(addr, dst, src);

    #[local] relation low_byte_boolean_logical_result(Address, Symbol);
    low_byte_boolean_logical_result(*addr, *dst_symbol) <--
        low_byte_boolean_logical_operands(addr, dst_symbol, src_symbol),
        op_register(dst_symbol, dst_name),
        op_register(src_symbol, src_name),
        if is_reg_8(dst_name),
        if !is_reg_high8(dst_name),
        if is_reg_8(src_name),
        if !is_reg_high8(src_name),
        instr_in_function(addr, func),
        low_byte_boolean_in(func, addr, boolean_regs),
        if boolean_regs.0.contains(&Mreg::x86(*dst_name)),
        if boolean_regs.0.contains(&Mreg::x86(*src_name));

    // Point-keyed active-origin state, killed by every flags-clobbering point.
    // Seed every flags producer that can describe a Jcc/CMOV condition.  This
    // is also the structural authority for linking a CMOV to its flags origin:
    // arbitrary flag-neutral instructions (including SETcc) may intervene, so
    // a fixed number of `next` hops is neither complete nor necessary.
    #[local] relation linked_flags_origin(Address);
    linked_flags_origin(origin) <-- pcmp(origin, _, _);
    linked_flags_origin(origin) <-- ptest(origin, _, _);
    linked_flags_origin(origin) <-- pneg(origin, _);
    linked_flags_origin(origin) <-- pand(origin, _, _);
    linked_flags_origin(origin) <-- padd(origin, _, _);
    linked_flags_origin(origin) <-- por(origin, _, _);
    linked_flags_origin(origin) <-- pxor(origin, _, _);
    linked_flags_origin(origin) <-- psub(origin, _, _);
    linked_flags_origin(origin) <-- psar(origin, _, _);
    linked_flags_origin(origin) <-- pshr(origin, _, _);
    linked_flags_origin(addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "INC" || *mnem == "DEC";

    // `None` is an explicit unknown-flags predecessor.  Without it an
    // unmodeled clobber arm disappears at a merge and a sibling producer can
    // masquerade as the unique MUST origin.
    #[local] lattice active_flags_in(Address, Set<Option<Address>>);
    #[local] lattice active_flags_out(Address, Set<Option<Address>>);
    active_flags_in(*func, Set::singleton(None)) <--
        func_span(_, func, _),
        instr_in_function(func, func);
    active_flags_out(*origin, Set::singleton(Some(*origin))) <--
        linked_flags_origin(origin);
    active_flags_in(*succ, active.clone()) <--
        active_flags_out(addr, active),
        cfg_step(addr, succ);
    active_flags_out(*addr, active.clone()) <--
        active_flags_in(addr, active),
        flags_flow_transparent(addr);
    active_flags_out(*addr, Set::singleton(None)) <--
        active_flags_in(addr, _),
        !flags_flow_transparent(addr),
        !linked_flags_origin(addr);

    // A CMOV is usable only when every incoming CFG path agrees on one flags
    // origin.  A may-set with more than one origin represents path-dependent
    // flags and must not be collapsed into one invented condition.
    #[local] relation cmov_flags_origin(Address, Address);
    cmov_flags_origin(*origin, *cmov) <--
        pcmov(cmov, _, _, _),
        active_flags_in(cmov, active),
        if active.0.len() == 1,
        for member in active.0.iter(),
        if let Some(origin) = member;

    #[local] relation jcc_flags_origin(Address, Address);
    jcc_flags_origin(*origin, *jcc) <--
        pjcc(jcc, _, _),
        active_flags_in(jcc, active),
        if active.0.len() == 1,
        for member in active.0.iter(),
        if let Some(origin) = member;

    #[local] relation overflow_jcc_flags_origin(Address, Address);
    overflow_jcc_flags_origin(*origin, *jcc) <--
        overflow_jcc(jcc, _, _),
        active_flags_in(jcc, active),
        if active.0.len() == 1,
        for member in active.0.iter(),
        if let Some(origin) = member;

    // Point-keyed may-state of (flags origin, compared register) pairs that
    // were redefined on an incoming path. Union at merges makes a secondary
    // safe only when every incoming path preserves every compared value.
    #[local] lattice redefined_flags_args_in(Address, Set<(Address, Mreg)>);
    #[local] lattice redefined_flags_args_out(Address, Set<(Address, Mreg)>);
    redefined_flags_args_in(*succ, redefined.clone()) <--
        redefined_flags_args_out(addr, redefined),
        cfg_step(addr, succ);
    redefined_flags_args_out(*addr, redefined.clone()) <--
        redefined_flags_args_in(addr, redefined),
        flags_flow_transparent(addr);
    redefined_flags_args_out(*addr, Set::singleton((*origin, *mreg))) <--
        active_flags_in(addr, active),
        for member in active.0.iter(),
        if let Some(origin) = member,
        flags_arg(origin, mreg),
        reg_def(addr, mreg),
        flags_flow_transparent(addr);

    // Signed x86 overflow after ADD/SUB can be reconstructed exactly from the
    // wrapped result and the unchanged source: the old destination is
    // `result - source` for ADD and `result + source` for SUB.  Keeping the
    // branch at the real JCC preserves the arithmetic write and every
    // flag-transparent instruction in between.  Only full 32/64-bit register
    // writes participate; partial-register and memory forms retain the opaque
    // fallback below.
    #[local] relation overflow_flags_arg_redefined(Address, Address);
    overflow_flags_arg_redefined(*origin, *jcc) <--
        overflow_jcc_flags_origin(origin, jcc),
        redefined_flags_args_in(jcc, redefined),
        for (redefined_origin, _) in redefined.0.iter(),
        if redefined_origin == origin;

    #[local] relation exact_overflow_shape_owner(Address, Address, ExactOverflowShape);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation: OverflowArithmetic::Add,
        width: *width,
        result: *result,
        source: Some(*source),
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        padd(origin, dst, src),
        op_register(dst, dst_str),
        op_register(src, src_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        if x86_gpr_view_width(src_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        ireg_of(src_preg, Ireg::from(*src_str)),
        preg_of(source, src_preg),
        if result != source,
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation: OverflowArithmetic::Sub,
        width: *width,
        result: *result,
        source: Some(*source),
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        psub(origin, dst, src),
        op_register(dst, dst_str),
        op_register(src, src_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        if x86_gpr_view_width(src_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        ireg_of(src_preg, Ireg::from(*src_str)),
        preg_of(source, src_preg),
        if result != source,
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation: OverflowArithmetic::AddImmediate(*immediate),
        width: *width,
        result: *result,
        source: None,
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        padd(origin, dst, src),
        op_register(dst, dst_str),
        op_immediate(src, immediate, _),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation: OverflowArithmetic::SubImmediate(*immediate),
        width: *width,
        result: *result,
        source: None,
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        psub(origin, dst, src),
        op_register(dst, dst_str),
        op_immediate(src, immediate, _),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation: OverflowArithmetic::Neg,
        width: *width,
        result: *result,
        source: None,
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        pneg(origin, dst),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc);

    exact_overflow_shape_owner(*func, *jcc, ExactOverflowShape {
        operation,
        width: *width,
        result: *result,
        source: None,
    }) <--
        overflow_jcc_flags_origin(origin, jcc),
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        instruction(origin, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "INC" || *mnem == "DEC",
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        ireg_of(dst_preg, Ireg::from(*dst_str)),
        preg_of(result, dst_preg),
        instr_in_function(origin, func),
        instr_in_function(jcc, func),
        !raw_gpr_unresolved_owner(func),
        !overflow_flags_arg_redefined(origin, jcc),
        let operation = if *mnem == "INC" {
            OverflowArithmetic::AddImmediate(1)
        } else {
            OverflowArithmetic::SubImmediate(1)
        };

    #[local] relation exact_overflow_owner_proved(Address, Address);
    exact_overflow_owner_proved(func, jcc) <--
        exact_overflow_shape_owner(func, jcc, _);

    // Addresses may belong to more than one inferred function.  An
    // address-global condition is exact only if every owner proves one shape
    // and all proven shapes agree.
    #[local] relation exact_overflow_owner_missing(Address);
    exact_overflow_owner_missing(*jcc) <--
        overflow_jcc(jcc, test, _),
        if matches!(*test, TestCond::CondO | TestCond::CondNo),
        instr_in_function(jcc, func),
        !exact_overflow_owner_proved(func, jcc);

    #[local] relation exact_overflow_shape_conflict(Address);
    exact_overflow_shape_conflict(*jcc) <--
        exact_overflow_shape_owner(_, jcc, left),
        exact_overflow_shape_owner(_, jcc, right),
        if left != right;

    #[local] relation exact_overflow_shape(Address, ExactOverflowShape);
    exact_overflow_shape(*jcc, *shape) <--
        exact_overflow_shape_owner(_, jcc, shape),
        !exact_overflow_owner_missing(jcc),
        !exact_overflow_shape_conflict(jcc);

    #[local] relation exact_overflow_condition(Address, Condition, Arc<Vec<Mreg>>, Symbol);
    exact_overflow_condition(*jcc, condition, args, label) <--
        exact_overflow_shape(jcc, shape),
        overflow_jcc(jcc, test, label),
        if let Some((condition, args)) = lower_exact_overflow_condition(*shape, *test);

    #[local] relation exact_overflow_jcc(Address);
    exact_overflow_jcc(jcc) <-- exact_overflow_condition(jcc, _, _, _);

    mach_inst(jcc, MachInst::Mcond(condition.clone(), args.clone(), label)) <--
        exact_overflow_condition(jcc, condition, args, label);

    reg_use(jcc, *arg) <--
        exact_overflow_condition(jcc, _, args, _),
        for arg in args.iter();

    // When a compared register is redefined on any CFG path to a secondary
    // jcc, re-reading it would test the wrong value. Keep that consumer keyed
    // at the original compare rather than fabricating a condition at the jcc.
    #[local] relation secondary_flags_arg_redefined(Address, Address);
    secondary_flags_arg_redefined(*origin, *jcc) <--
        secondary_flags_consumer(origin, jcc),
        redefined_flags_args_in(jcc, redefined),
        for (redefined_origin, _) in redefined.0.iter(),
        if redefined_origin == origin;

    #[local] relation secondary_safe(Address, Address);
    secondary_safe(addr0, addr1) <--
        secondary_flags_consumer(addr0, addr1),
        !secondary_flags_arg_redefined(addr0, addr1);

    // A primary pair with instructions scheduled in the flag shadow: cmp/test,
    // then flag-neutral instructions, then the jcc.  Keying the Mcond at the
    // compare runs the branch BEFORE the shadow, so the lifted CFG bypasses
    // those instructions on both arms and their statements become unreachable
    // islands that selection silently drops (their effect is lost on every
    // path).  When the jcc has exactly one flags origin and every compared
    // register survives the shadow, emit the Mcond at the JCC itself -- the
    // same shape as a safe secondary consumer: the shadow keeps its position
    // on the fallthrough chain and the condition re-reads the compare's
    // registers at the jump.  A memory-operand compare keeps compare-site
    // keying: its RTL load is materialized at the flag-setting point and the
    // linked-consumer split owns that case.
    #[local] relation flags_pair_arg_redefined(Address, Address);
    flags_pair_arg_redefined(*origin, *jcc) <--
        cmp_jcc_link(origin, jcc),
        redefined_flags_args_in(jcc, redefined),
        for (redefined_origin, _) in redefined.0.iter(),
        if redefined_origin == origin;
    flags_pair_arg_redefined(*origin, *jcc) <--
        test_jcc_link(origin, jcc),
        redefined_flags_args_in(jcc, redefined),
        for (redefined_origin, _) in redefined.0.iter(),
        if redefined_origin == origin;

    #[local] relation flags_origin_mem_operand(Address);
    flags_origin_mem_operand(addr) <-- pcmp(addr, m, _), op_indirect(m, _, _, _, _, _, _);
    flags_origin_mem_operand(addr) <-- pcmp(addr, _, m), op_indirect(m, _, _, _, _, _, _);
    flags_origin_mem_operand(addr) <-- ptest(addr, m, _), op_indirect(m, _, _, _, _, _, _);
    flags_origin_mem_operand(addr) <-- ptest(addr, _, m), op_indirect(m, _, _, _, _, _, _);

    #[local] relation shadowed_primary(Address, Address);
    shadowed_primary(addr0, addr1) <--
        cmp_jcc_link(addr0, addr1),
        next(addr0, mid),
        if mid != addr1;
    shadowed_primary(addr0, addr1) <--
        test_jcc_link(addr0, addr1),
        next(addr0, mid),
        if mid != addr1;

    #[local] relation shadowed_safe(Address, Address);
    shadowed_safe(addr0, addr1) <--
        shadowed_primary(addr0, addr1),
        jcc_flags_origin(addr0, addr1),
        !secondary_flags_consumer(addr0, addr1),
        !flags_pair_arg_redefined(addr0, addr1),
        !flags_origin_mem_operand(addr0);

    // A compare that delegated its Mcond to the jcc has no instruction of its
    // own; linear threads it as a plain fallthrough so its physical
    // predecessors still reach the shadow.
    cond_delegated_origin(addr0) <-- shadowed_safe(addr0, _);

    // Where each (compare, jcc) pair's Mcond is keyed: primary (and unsafe secondary) -> the compare's address; safe secondary and shadowed-safe primary -> the jcc's own address.
    #[local] relation mcond_emit_addr(Address, Address, Address);
    mcond_emit_addr(addr0, addr1, addr0) <--
        cmp_jcc_link(addr0, addr1),
        !secondary_safe(addr0, addr1),
        !shadowed_safe(addr0, addr1);
    mcond_emit_addr(addr0, addr1, addr0) <--
        test_jcc_link(addr0, addr1),
        !secondary_safe(addr0, addr1),
        !shadowed_safe(addr0, addr1);
    mcond_emit_addr(addr0, addr1, addr1) <--
        cond_reads_at_jcc(addr0, addr1);

    #[local] relation cond_reads_at_jcc(Address, Address);
    cond_reads_at_jcc(addr0, addr1) <-- secondary_safe(addr0, addr1);
    cond_reads_at_jcc(addr0, addr1) <-- shadowed_safe(addr0, addr1);

    relation mcond_at_jcc(Address);
    mcond_at_jcc(addr1) <-- cond_reads_at_jcc(_, addr1);

    relation cond_delegated_origin(Address);

    // An Mcond keyed at the JCC reads its compare's registers there, where the raw jcc has no operands, so bind the uses here or liveness never connects the compare's def.
    reg_use(addr1, mreg) <--
        cond_reads_at_jcc(addr0, addr1),
        pcmp(addr0, r, _),
        op_register(r, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    reg_use(addr1, mreg) <--
        cond_reads_at_jcc(addr0, addr1),
        pcmp(addr0, _, r),
        op_register(r, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);
    reg_use(addr1, mreg) <--
        cond_reads_at_jcc(addr0, addr1),
        ptest(addr0, r, _),
        op_register(r, reg_str),
        ireg_of(preg_of_r, Ireg::from(reg_str)),
        preg_of(mreg, preg_of_r);

    #[local] relation cmp_cmov_link(Address, Address);
    cmp_cmov_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        cmov_flags_origin(addr0, addr1);

    // NEG -> CMOV link: NEG sets flags (SF based on result), enabling CMOVS/CMOVNS.
    #[local] relation neg_cmov_link(Address, Address);
    neg_cmov_link(addr0, addr1) <--
        pneg(addr0, _),
        cmov_flags_origin(addr0, addr1);

    #[local] relation fcmp_jcc_link(Address, Address);
    fcmp_jcc_link(addr0, addr1) <--
        pucomisd(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        pucomiss(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pucomisd(addr0, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pucomiss(addr0, _, _);

    // TestCond -> Condition divergence: CondE/CondNe are ZF-based (signedness-agnostic), so they map to both signed and unsigned comparison conditions.
    #[local] relation testcond_to_cond(TestCond, Condition);
    #[local] relation testcond_to_cond_64(TestCond, Condition);

    testcond_to_cond(test_cond.clone(), condition_for_testcond_sized(*test_cond, false)) <--
        pjcc(_, test_cond, _);
    testcond_to_cond_64(test_cond.clone(), condition_for_testcond_sized(*test_cond, true)) <--
        pjcc(_, test_cond, _);

    testcond_to_cond(TestCond::CondE, Condition::Ccompu(Comparison::Ceq)) <--
        pjcc(_, test_cond, _), if let TestCond::CondE = test_cond;
    testcond_to_cond_64(TestCond::CondE, Condition::Ccomplu(Comparison::Ceq)) <--
        pjcc(_, test_cond, _), if let TestCond::CondE = test_cond;

    testcond_to_cond(TestCond::CondNe, Condition::Ccompu(Comparison::Cne)) <--
        pjcc(_, test_cond, _), if let TestCond::CondNe = test_cond;
    testcond_to_cond_64(TestCond::CondNe, Condition::Ccomplu(Comparison::Cne)) <--
        pjcc(_, test_cond, _), if let TestCond::CondNe = test_cond;


    mach_inst(emit_addr, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        testcond_to_cond_64(*test_cond, base_cond),
        let condition = match base_cond {
            Condition::Ccomp(cmp) | Condition::Ccompl(cmp) => Condition::Ccomplimm(*cmp, *imm_val),
            Condition::Ccompu(cmp) | Condition::Ccomplu(cmp) => Condition::Ccompluimm(*cmp, *imm_val),
            other => other.clone(),
        };

    mach_inst(emit_addr, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        testcond_to_cond(*test_cond, base_cond),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(*cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(*cmp, *imm_val),
            other => other.clone(),
        };

    mach_inst(emit_addr, MachInst::Mcond(condition.clone(), Arc::new(vec![*arg1, *arg2]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        testcond_to_cond_64(*test_cond, condition);

    mach_inst(emit_addr, MachInst::Mcond(condition.clone(), Arc::new(vec![*arg1, *arg2]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        testcond_to_cond(*test_cond, condition);


    mach_inst(emit_addr, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, true),
        let condition = match base_cond {
            Condition::Ccomp(cmp) | Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccompu(cmp) | Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        };

    mach_inst(emit_addr, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, false),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            other => other,
        };


    // A value-producing ALU operation followed by a flags-reading jcc tests
    // the arithmetic RESULT
    // against zero, so emit the Mcond at the jcc's own address.  Keeping the
    // value-producing operation at its instruction is essential when that
    // result remains live after the branch; otherwise candidate selection
    // would retain the condition and silently discard the register write.
    // Restricted to ZF/signed conditions, since carry after arithmetic is not
    // a comparison against zero.
    #[local] relation arith_result_reg(Address, Symbol, bool);
    arith_result_reg(addr, dst, is_64) <--
        padd(addr, dst, _),
        op_register(dst, dst_str),
        reg_is_64(dst_str, is_64);

    arith_result_reg(addr, dst, is_64) <--
        pand(addr, dst, _),
        op_register(dst, dst_str),
        reg_is_64(dst_str, is_64);

    // OR/XOR are the same result-vs-zero shape for full 32/64-bit writes. A
    // byte/word write preserves upper parent-register bits, so it is admitted
    // only through the proven SETcc-boolean reduction below.
    arith_result_reg(addr, dst, is_64) <--
        por(addr, dst, _),
        op_register(dst, dst_str),
        if !is_reg_8(dst_str),
        if !is_reg_16(dst_str),
        reg_is_64(dst_str, is_64);

    arith_result_reg(addr, dst, is_64) <--
        pxor(addr, dst, _),
        op_register(dst, dst_str),
        if !is_reg_8(dst_str),
        if !is_reg_16(dst_str),
        reg_is_64(dst_str, is_64);

    arith_result_reg(addr, dst, false) <--
        low_byte_boolean_logical_result(addr, dst);

    // A byte/word OR/XOR followed by JE/JNE has an exact result-vs-zero
    // interpretation too, even when the operands are not proven booleans: ZF
    // observes only the written lane. Keep this separate from arith_result_reg,
    // whose Ccompimm(0) tests the whole normalized parent register.
    #[local] relation partial_logical_result(Address, Symbol, i64);
    partial_logical_result(*addr, *dst, mask) <--
        por(addr, dst, _),
        op_register(dst, dst_name),
        if let Some(mask) = partial_logical_result_mask(dst_name);
    partial_logical_result(*addr, *dst, mask) <--
        pxor(addr, dst, _),
        op_register(dst, dst_name),
        if let Some(mask) = partial_logical_result_mask(dst_name);

    // SAR/SHR then a flags-reading jcc is the divide-by-power-of-2 loop latch; ZF/signed conditions only, since after a shift CF is the last bit shifted out, not a comparison.
    arith_result_reg(addr, dst, is_64) <--
        psar(addr, dst, _),
        op_register(dst, dst_str),
        reg_is_64(dst_str, is_64);
    arith_result_reg(addr, dst, is_64) <--
        pshr(addr, dst, _),
        op_register(dst, dst_str),
        reg_is_64(dst_str, is_64);

    arith_result_reg(addr, dst, is_64) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "INC" || *mnem == "DEC",
        op_register(dst, dst_str),
        reg_is_64(dst_str, is_64);

    // A SUB-immediate before a flags-reading jcc is decrement-and-branch: when the decremented value is live, keep the SUB's value op and emit the Mcond at the jcc, or the -1 is dropped.
    arith_result_reg(addr, dst, is_64) <--
        sub_result_live(addr, dst_mreg),
        psub(addr, dst, n),
        op_immediate(n, _, _),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(dst_str, is_64);

    // Point-keyed may-reaching-def lattice for immediate-SUB destinations.
    // Each (point, register) stores the set of SUB definitions reaching that
    // point; joins union at branch merges, and a local redefinition kills the
    // incoming set after its own reads have observed it.
    #[local] lattice sub_defs_in(Address, Mreg, Set<Address>);
    #[local] lattice sub_defs_out(Address, Mreg, Set<Address>);
    sub_defs_out(*sub_addr, *dst_mreg, Set::singleton(*sub_addr)) <--
        psub(sub_addr, dst, n),
        op_immediate(n, _, _),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst);
    sub_defs_in(*succ, *dst_mreg, reaching.clone()) <--
        sub_defs_out(addr, dst_mreg, reaching),
        cfg_step(addr, succ);
    sub_defs_out(*addr, *dst_mreg, reaching.clone()) <--
        sub_defs_in(addr, dst_mreg, reaching),
        !reg_def(addr, dst_mreg);

    // sub_result_live: the decremented value is genuinely read downstream by a real value instruction, excluding the consuming jcc whose only reg_use is the synthetic relocated-condition row.
    #[local] relation sub_result_live(Address, Mreg);
    sub_result_live(*sub_addr, *dst_mreg) <--
        sub_defs_in(u, dst_mreg, reaching),
        for sub_addr in reaching.0.iter(),
        !pjcc(u, _, _),
        reg_use(u, dst_mreg);

    // arith_result_jcc(arith_addr, jcc_addr, dst_sym, is_64, test_cond): the arith result feeds the jcc.
    #[local] relation arith_result_jcc(Address, Address, Symbol, bool, TestCond);
    arith_result_jcc(addr0, addr1, dst, *is_64, *test_cond) <--
        arith_result_reg(addr0, dst, is_64),
        jcc_flags_origin(addr0, addr1),
        pjcc(addr1, test_cond, _),
        if arith_result_testcond_ok(*test_cond);

    // Mcond at the jcc's OWN address: `if (R <cmp> 0) goto target`.
    mach_inst(addr1, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        arith_result_jcc(_, addr1, dst, is_64, test_cond),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(arg1, preg_of_dst),
        pjcc(addr1, _, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            other => other,
        };

    // The Mcond lives at the jcc address, so linear computes its fall-through as next(jcc).
    mcond_at_jcc(addr1) <-- arith_result_jcc(_, addr1, _, _, _);

    // The raw jcc has no register operands, so bind the result register's use at the jcc to connect the arith def to the relocated condition.
    reg_use(addr1, mreg) <--
        arith_result_jcc(_, addr1, dst, _, _),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(mreg, preg_of_dst);

    // Partial-width logical ZF branch. The mask preserves low/high-byte lane
    // position after subregister normalization (AH/BH/CH/DH use mask<<8).
    // The full-boolean rule above is preferred when available so one JCC does
    // not receive two equivalent condition candidates.
    mach_inst(*addr1, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)),
    mcond_at_jcc(*addr1),
    reg_use(*addr1, *arg1) <--
        partial_logical_result(addr0, dst, mask),
        !low_byte_boolean_logical_result(addr0, _),
        jcc_flags_origin(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        if matches!(test_cond, TestCond::CondE | TestCond::CondNe),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(arg1, preg_of_dst),
        let condition = match test_cond {
            TestCond::CondE => Condition::Cmaskzero(*mask),
            TestCond::CondNe => Condition::Cmasknotzero(*mask),
            _ => unreachable!("guarded to ZF conditions"),
        };


    // osel_compare_site(cmov_addr, compare_addr): the compare/test whose flags this cmov consumes. rtl_pass resolves the cmov condition operands at compare_addr, since clang may reuse the compared register as a value holder between the compare and the cmov.
    relation osel_compare_site(Address, Address);

    // osel_flags_result_site(cmov_addr, arithmetic_addr): unlike a CMP, a
    // flags-producing arithmetic instruction's predicate observes its RESULT.
    // The same architectural register may be overwritten by a flag-neutral
    // instruction before CMOV and then serve as the selected source, so RTL
    // must keep the post-arithmetic condition value distinct from that later
    // CMOV-time value.
    relation osel_flags_result_site(Address, Address);

    // CMP-imm + CMOV -> Osel: anchored at CMOV address so dst_mreg def is visible to downstream uses (avoids DSE when there is a gap).
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *cmp_arg1]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pcmp(addr0, cmp_r1, cmp_r2),
        op_register(cmp_r1, cmp_reg_str),
        op_immediate(cmp_r2, imm_val, _),
        ireg_of(preg_of_cmp1, Ireg::from(cmp_reg_str)),
        preg_of(cmp_arg1, preg_of_cmp1),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(cmp_reg_str, cmp_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *cmp_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // CMP-mem + CMOV -> Osel: the compare's first operand is a memory deref, so use its base register as the Osel condition operand; gated on cmp_cmov_link and a base-register form.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *cmp_arg1]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pcmp(addr0, cmp_r1, cmp_r2),
        op_indirect(cmp_r1, _, cmp_base_str, _, _, _, _),
        if *cmp_base_str != "NONE" && *cmp_base_str != "RIP" && !cmp_base_str.is_empty(),
        op_immediate(cmp_r2, imm_val, _),
        ireg_of(preg_of_cmp1, Ireg::from(cmp_base_str)),
        preg_of(cmp_arg1, preg_of_cmp1),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(cmp_base_str, cmp_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *cmp_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // A RIP-relative compare has no address GPR to carry as Mach's condition
    // operand.  Keep the two-value Osel backstop so the CMOV definition
    // survives, but also export the exact compare site: rtl_pass materializes
    // the global load there and completes the Osel with that loaded value.
    // Restrict this rule to the RIP/no-index form instead of using a negated
    // osel_compare_site guard; the latter suppressed the very provenance the
    // downstream completion requires.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pcmp(addr0, cmp_r1, _),
        op_indirect(cmp_r1, _, cmp_base, cmp_index, _, _, _),
        if *cmp_base == "RIP",
        if *cmp_index == "NONE" || cmp_index.is_empty(),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(dst_str, dst_is_64),
        let condition = condition_for_testcond_sized(neg_cond, *dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // CMP-reg + CMOV -> Osel: anchored at CMOV address.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *cmp_arg1, *cmp_arg2]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pcmp(addr0, cmp_r1, cmp_r2),
        op_register(cmp_r1, cmp_str1),
        op_register(cmp_r2, cmp_str2),
        ireg_of(preg_of_cmp1, Ireg::from(cmp_str1)),
        ireg_of(preg_of_cmp2, Ireg::from(cmp_str2)),
        preg_of(cmp_arg1, preg_of_cmp1),
        preg_of(cmp_arg2, preg_of_cmp2),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(cmp_str1, cmp_is_64),
        let condition = condition_for_testcond_sized(neg_cond, *cmp_is_64),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // NEG + CMOV -> Osel: anchored at CMOV address; NEG sets flags as `0 - operand`, condition compares NEG operand against 0; NEG reg is both input and negated output.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *neg_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pneg(addr0, neg_r),
        op_register(neg_r, neg_reg_str),
        ireg_of(preg_of_neg, Ireg::from(neg_reg_str)),
        preg_of(neg_arg, preg_of_neg),
        neg_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(neg_reg_str, neg_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *neg_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // SUB result + CMOV of that same result: the flags and selected source are
    // both the post-SUB value (the usual branchless absolute-difference form).
    // Leave osel_compare_site unset so RTL resolves the condition operand at
    // the CMOV, not before the SUB definition.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *src_mreg]),
        *dst_mreg
    )),
    osel_flags_result_site(*addr1, *addr0) <--
        psub(addr0, sub_dst, _),
        op_register(sub_dst, sub_dst_str),
        cmov_flags_origin(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        if arith_result_testcond_ok(*cmov_cond),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        if Mreg::x86(sub_dst_str) == Mreg::x86(src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(src_str, result_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *result_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // TEST/AND $mask + CMOVE/CMOVNE -> Osel with a mask condition; the Osel condition selects the PRESERVE value, so it is the NEGATION of the cmov predicate (CMOVE gives Cmasknotzero).
    #[local] relation test_cmov_link(Address, Address);
    test_cmov_link(addr0, addr1) <--
        ptest(addr0, _, _),
        cmov_flags_origin(addr0, addr1);

    #[local] relation and_cmov_link(Address, Address);
    and_cmov_link(addr0, addr1) <--
        pand(addr0, _, _),
        cmov_flags_origin(addr0, addr1);

    // TEST reg,reg + CMOV -> a general select against zero.  SETcc commonly
    // sits between these instructions and consumes the same flags, so this is
    // deliberately driven by the CFG flags lattice rather than adjacency.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *test_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        ptest(addr0, test_r1, test_r2),
        op_register(test_r1, test_str1),
        op_register(test_r2, test_str2),
        if Mreg::x86(test_str1) == Mreg::x86(test_str2),
        ireg_of(preg_of_test, Ireg::from(test_str1)),
        preg_of(test_arg, preg_of_test),
        test_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(test_str1, test_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *test_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // TEST $mask + CMOVE: Osel(Cmasknotzero(mask), dst, src, masked_reg).
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmasknotzero(high8_mask_adjust(test_str, *mask_val)), typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *test_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        ptest(addr0, test_r, mask_op),
        op_register(test_r, test_str),
        op_immediate(mask_op, mask_val, _),
        ireg_of(preg_of_test, Ireg::from(test_str)),
        preg_of(test_arg, preg_of_test),
        test_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondE, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // TEST $mask + CMOVNE: Osel(Cmaskzero(mask), dst, src, masked_reg).
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmaskzero(high8_mask_adjust(test_str, *mask_val)), typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *test_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        ptest(addr0, test_r, mask_op),
        op_register(test_r, test_str),
        op_immediate(mask_op, mask_val, _),
        ireg_of(preg_of_test, Ireg::from(test_str)),
        preg_of(test_arg, preg_of_test),
        test_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondNe, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // TEST $mask,[mem] + CMOVE/CMOVNE has the same select predicate as the
    // register form, but the tested value must be loaded before RTL can name
    // it.  Keep a two-value Osel here (preserve/source) and export the exact
    // TEST origin; rtl_pass materializes the memory read and appends that
    // loaded value as the condition operand.  Using the address base itself
    // would test pointer bits rather than the byte/word in memory.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmasknotzero(*mask_val), typ),
        Arc::new(vec![*dst_mreg, *src_mreg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        ptest(addr0, test_mem, mask_op),
        op_indirect(test_mem, _, _, _, _, _, _),
        op_immediate(mask_op, mask_val, _),
        test_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondE, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmaskzero(*mask_val), typ),
        Arc::new(vec![*dst_mreg, *src_mreg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        ptest(addr0, test_mem, mask_op),
        op_indirect(test_mem, _, _, _, _, _, _),
        op_immediate(mask_op, mask_val, _),
        test_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondNe, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // AND $mask + CMOVE: same as the TEST case, since masking is idempotent so resolving the post-AND value under Cmask* is still correct.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmasknotzero(high8_mask_adjust(test_str, *mask_val)), typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *test_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pand(addr0, test_r, mask_op),
        op_register(test_r, test_str),
        op_immediate(mask_op, mask_val, _),
        ireg_of(preg_of_test, Ireg::from(test_str)),
        preg_of(test_arg, preg_of_test),
        and_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondE, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    // AND $mask + CMOVNE.
    mach_inst(addr1, MachInst::Mop(
        Operation::Osel(Condition::Cmaskzero(high8_mask_adjust(test_str, *mask_val)), typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *test_arg]),
        *dst_mreg
    )),
    osel_compare_site(*addr1, *addr0) <--
        pand(addr0, test_r, mask_op),
        op_register(test_r, test_str),
        op_immediate(mask_op, mask_val, _),
        ireg_of(preg_of_test, Ireg::from(test_str)),
        preg_of(test_arg, preg_of_test),
        and_cmov_link(addr0, addr1),
        pcmov(addr1, TestCond::CondNe, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };


    mach_inst(emit_addr, MachInst::Mcond(Condition::Cmaskzero(adj_mask), Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, TestCond::CondE, lbl),
        let adj_mask = high8_mask_adjust(reg_str1, *mask_val);

    mach_inst(emit_addr, MachInst::Mcond(Condition::Cmasknotzero(adj_mask), Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        mcond_emit_addr(addr0, addr1, emit_addr),
        pjcc(addr1, TestCond::CondNe, lbl),
        let adj_mask = high8_mask_adjust(reg_str1, *mask_val);


    #[local] relation sub_jcc_link(Address, Address);
    sub_jcc_link(addr0, addr1) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    sub_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        psub(addr0, _, _);

    // SUB -> 1 non-flag-clobbering instruction -> JCC (e.g. SUB + MOV mem + JCC)
    sub_jcc_link(addr0, addr2) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        pjcc(addr2, _, _);

    // SUB -> 2 non-flag-clobbering instructions -> JCC
    sub_jcc_link(addr0, addr3) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, addr3),
        pjcc(addr3, _, _);

    // Suppressed when arith_result_jcc covers this SUB: the branch is then emitted at the jcc's address and the SUB keeps its value op, so the decrement is not lost and the taken edge survives.
    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        !arith_result_jcc(addr0, _, _, _, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        sub_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1, *arg2]), lbl)) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        sub_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        reg_is_64(reg_str1, is_64),
        let condition = condition_for_testcond_sized(*test_cond, *is_64);


    #[local] relation and_jcc_link(Address, Address);
    and_jcc_link(addr0, addr1) <--
        pand(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    and_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pand(addr0, _, _);

    // AND -> 1 non-flag-clobbering instruction -> JCC (e.g. AND + MOV mem + JCC)
    and_jcc_link(addr0, addr2) <--
        pand(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        pjcc(addr2, _, _);

    // AND -> 2 non-flag-clobbering instructions -> JCC
    and_jcc_link(addr0, addr3) <--
        pand(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, addr3),
        pjcc(addr3, _, _);

    mach_inst(addr0, MachInst::Mcond(Condition::Cmaskzero(adj_mask), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        !arith_result_jcc(addr0, _, _, _, _),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl),
        let adj_mask = high8_mask_adjust(reg_str1, *mask_val);

    mach_inst(addr0, MachInst::Mcond(Condition::Cmasknotzero(adj_mask), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        !arith_result_jcc(addr0, _, _, _, _),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl),
        let adj_mask = high8_mask_adjust(reg_str1, *mask_val);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompimm(Comparison::Ceq, 0), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        !arith_result_jcc(addr0, _, _, _, _),
        op_register(r1, reg_str1),
        op_register(r2, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompimm(Comparison::Cne, 0), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        !arith_result_jcc(addr0, _, _, _, _),
        op_register(r1, reg_str1),
        op_register(r2, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);

    // JCXZ/JECXZ/JRCXZ test (E/R)CX==0 directly with no preceding compare, so lift each as a self-contained Mcond at its own address; the CFG already creates both edges.
    mach_inst(addr, MachInst::Mcond(Condition::Ccompimm(Comparison::Ceq, 0), Arc::new(vec![Mreg::CX]), dst)) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "JCXZ" || *mnem == "JECXZ";

    mach_inst(addr, MachInst::Mcond(Condition::Ccomplimm(Comparison::Ceq, 0), Arc::new(vec![Mreg::CX]), dst)) <--
        instruction(addr, _, _, "JRCXZ", dst, _, _, _, _, _);

    // Unsupported JO/JNO producers retain an opaque condition, preserving both
    // CFG edges without inventing arithmetic semantics.  A proved arithmetic
    // shape above owns the JCC exclusively so selection cannot choose this
    // weaker fallback instead.
    mach_inst(addr, MachInst::Mcond(Condition::Coverflow, Arc::new(vec![]), dst)) <--
        instruction(addr, _, _, "JO", dst, _, _, _, _, _),
        !exact_overflow_jcc(addr);
    mach_inst(addr, MachInst::Mcond(Condition::Cnotoverflow, Arc::new(vec![]), dst)) <--
        instruction(addr, _, _, "JNO", dst, _, _, _, _, _),
        !exact_overflow_jcc(addr);

    // ASM-5: LOOP/LOOPE/LOOPNE branch iff the decremented RCX != 0, which as a function of RCX at the instruction is exactly Ccomplimm(Cne, 1); the RCX write-back and ZF refinement are not modelled.
    mach_inst(addr, MachInst::Mcond(Condition::Ccomplimm(Comparison::Cne, 1), Arc::new(vec![Mreg::CX]), dst)) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "LOOP" || *mnem == "LOOPE" || *mnem == "LOOPNE";

    // Every single-instruction conditional jump keys its Mcond at its OWN address, so mcond_at_jcc switches linear to the fall-through = next(addr) rule instead of the paired-compare skip.
    relation single_inst_cond_jump(Address);
    single_inst_cond_jump(addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if matches!(*mnem,
            "JCXZ" | "JECXZ" | "JRCXZ" | "JO" | "JNO" | "LOOP" | "LOOPE" | "LOOPNE");
    mcond_at_jcc(addr) <-- single_inst_cond_jump(addr);


    // SETcc fuses with the nearest preceding flag-setting compare, tolerating scheduled non-flag-clobbering instructions; the walk stops at any flag setter so a stale compare is never bound.
    #[local] relation setcc_flag_origin(Address);
    setcc_flag_origin(addr) <-- pcmp(addr, _, _);
    setcc_flag_origin(addr) <-- ptest(addr, _, _);
    setcc_flag_origin(addr) <-- psub(addr, _, _);

    // Same-block structural walk from a flag producer to every subsequent
    // instruction that can still observe those flags.  Fixed two-instruction
    // windows missed ordinary scheduling such as TEST; MOV; MOV; CMOV; SETcc.
    // The recursion stops before crossing a flag-setting instruction, and the
    // block guard prevents a guessed cross-merge origin.
    #[local] relation setcc_flag_walk(Address, Address);
    setcc_flag_walk(origin, *successor) <--
        setcc_flag_origin(origin),
        next(origin, successor),
        code_in_block(origin, block),
        code_in_block(successor, block);
    setcc_flag_walk(origin, *successor) <--
        setcc_flag_walk(origin, current),
        flags_flow_transparent(current),
        next(current, successor),
        code_in_block(origin, block),
        code_in_block(successor, block);

    #[local] relation cmp_setcc_link(Address, Address);
    cmp_setcc_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    cmp_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _),
        psetcc(addr1, _, _);
    cmp_setcc_link(addr0, addr2) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        psetcc(addr2, _, _);
    cmp_setcc_link(addr0, addr3) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, addr3),
        psetcc(addr3, _, _);
    cmp_setcc_link(addr0, addr_set) <--
        pcmp(addr0, _, _),
        setcc_flag_walk(addr0, addr_set),
        psetcc(addr_set, _, _);

    #[local] relation test_setcc_link(Address, Address);
    test_setcc_link(addr0, addr1) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    test_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        ptest(addr0, _, _),
        psetcc(addr1, _, _);
    test_setcc_link(addr0, addr2) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        psetcc(addr2, _, _);
    test_setcc_link(addr0, addr3) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, addr3),
        psetcc(addr3, _, _);
    test_setcc_link(addr0, addr_set) <--
        ptest(addr0, _, _),
        setcc_flag_walk(addr0, addr_set),
        psetcc(addr_set, _, _);

    #[local] relation sub_setcc_link(Address, Address);
    sub_setcc_link(addr0, addr1) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    sub_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        psub(addr0, _, _),
        psetcc(addr1, _, _);
    sub_setcc_link(addr0, addr2) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        psetcc(addr2, _, _);
    sub_setcc_link(addr0, addr_set) <--
        psub(addr0, _, _),
        setcc_flag_walk(addr0, addr_set),
        psetcc(addr_set, _, _);

    setcc_compare_site(addr_set, addr0) <-- cmp_setcc_link(addr0, addr_set);
    setcc_compare_site(addr_set, addr0) <-- test_setcc_link(addr0, addr_set);

    // The boolean value materialized by a SETcc, independent of where that
    // byte is written.  Register destinations consume the equivalent Mop
    // rules below.  Frame-memory destinations consume this normalized fact so
    // they do not disappear merely because op_register cannot match them.
    // Keeping the flags origin explicit is essential when flag-transparent
    // instructions overwrite one of the compared registers before SETcc.
    #[local] relation setcc_materialized_value(Address, Address, Operation, Arc<Vec<Mreg>>);

    setcc_materialized_value(addr_set, addr0, Operation::Ocmp(condition), Arc::new(vec![*arg1])) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    setcc_materialized_value(addr_set, addr0, Operation::Ocmp(condition), Arc::new(vec![*arg1, *arg2])) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        reg_is_64(reg_str1, is_64),
        let condition = condition_for_testcond_sized(*test_cond, *is_64);

    setcc_materialized_value(addr_set, addr0, Operation::Ocmp(condition), Arc::new(vec![*arg1])) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        };

    setcc_materialized_value(
        addr_set,
        addr0,
        Operation::Ocmp(Condition::Cmaskzero(high8_mask_adjust(reg_str1, *mask_val))),
        Arc::new(vec![*arg1])
    ) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondE, _);

    setcc_materialized_value(
        addr_set,
        addr0,
        Operation::Ocmp(Condition::Cmasknotzero(high8_mask_adjust(reg_str1, *mask_val))),
        Arc::new(vec![*arg1])
    ) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondNe, _);

    // Scalar BP/SP destinations name frame cells.  The physical byte width is
    // checked rather than inferred from Typ (which has no byte variant), and
    // SP displacements use the same frame coordinate as every other stack
    // access relation.
    mach_stack_setcc(addr_set, *disp, addr0, op.clone(), args.clone()) <--
        setcc_materialized_value(addr_set, addr0, op, args),
        psetcc(addr_set, _, dst_sym),
        op_indirect(dst_sym, _, base, idx, _, disp, sz),
        if Mreg::x86(*base) == Mreg::BP,
        if *idx == "NONE" || idx.is_empty(),
        if *sz == 1,
        instr_in_function(addr_set, func),
        func_has_frame_pointer(func);

    mach_stack_setcc(addr_set, disp - depth, addr0, op.clone(), args.clone()) <--
        setcc_materialized_value(addr_set, addr0, op, args),
        psetcc(addr_set, _, dst_sym),
        op_indirect(dst_sym, _, base, idx, _, disp, sz),
        if Mreg::x86(*base) == Mreg::SP,
        if *idx == "NONE" || idx.is_empty(),
        if *sz == 1,
        sp_frame_shift(addr_set, depth);

    mach_inst(addr_set, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr_set, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1, *arg2]),
        *dst_mreg
    )) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let condition = condition_for_testcond_sized(*test_cond, *is_64);

    mach_inst(addr_set, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        };

    mach_inst(addr_set, MachInst::Mop(
        Operation::Ocmp(Condition::Cmaskzero(high8_mask_adjust(reg_str1, *mask_val))),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondE, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst);

    mach_inst(addr_set, MachInst::Mop(
        Operation::Ocmp(Condition::Cmasknotzero(high8_mask_adjust(reg_str1, *mask_val))),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondNe, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst);

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        sub_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mop(
        Operation::Oshrximm(*shift_n),
        Arc::new(args.clone()),
        *arg_mreg
    )) <--
        ptest(addr0, test_r1, test_r2),
        op_register(test_r1, test_reg1),
        op_register(test_r2, test_reg2),
        if test_reg1 == test_reg2,
        next(addr0, addr1),
        plea(addr1, lea_dst_sym, lea_src_sym),
        op_register(lea_dst_sym, lea_dst_str),
        op_indirect(lea_src_sym, _, base_reg, _, _, disp, _),
        if base_reg == test_reg1,
        if lea_dst_str != test_reg1,
        next(addr1, addr2),
        pcmov(addr2, TestCond::CondL, cmov_dst_sym, cmov_src_sym),
        op_register(cmov_dst_sym, cmov_dst_str),
        op_register(cmov_src_sym, cmov_src_str),
        if cmov_dst_str == test_reg1,
        if cmov_src_str == lea_dst_str,
        next(addr2, addr3),
        psar(addr3, sar_dst_sym, sar_src_sym),
        op_register(sar_dst_sym, sar_dst_str),
        op_immediate(sar_src_sym, shift_n, _),
        if sar_dst_str == test_reg1,
        if *disp == (1i64 << *shift_n) - 1,
        ireg_of(preg_of_arg, Ireg::from(test_reg1)),
        preg_of(arg_mreg, preg_of_arg),
        let args = vec![*arg_mreg];

    mach_inst(addr0, MachInst::Mop(
        Operation::Oshrxlimm(*shift_n),
        Arc::new(args.clone()),
        *arg_mreg
    )) <--
        pcast(addr0, _, _),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "CQO",
        next(addr0, addr1),
        pshr(addr1, shr_dst_sym, shr_src_sym),
        op_register(shr_dst_sym, shr_dst_str),
        op_immediate(shr_src_sym, shr_amount, _),
        next(addr1, addr2),
        plea(addr2, lea_dst_sym, lea_src_sym),
        op_register(lea_dst_sym, lea_dst_str),
        op_indirect(lea_src_sym, _, lea_base, lea_index, _scale, lea_disp, _),
        if *lea_disp == 0,
        if lea_base == lea_dst_str,
        if lea_index == shr_dst_str,
        next(addr2, addr3),
        psar(addr3, sar_dst_sym, sar_src_sym),
        op_register(sar_dst_sym, sar_dst_str),
        op_immediate(sar_src_sym, shift_n, _),
        if sar_dst_str == lea_dst_str,
        if *shr_amount == 64 - *shift_n,
        ireg_of(preg_of_arg, Ireg::from(lea_dst_str)),
        preg_of(arg_mreg, preg_of_arg),
        let args = vec![*arg_mreg];

    // Reusable sub-relations for multi-instruction idiom detection

    // Unify SAR and SHR
    relation pshift_right(Address, Symbol, Symbol);
    pshift_right(addr, dst, src) <-- psar(addr, dst, src);
    pshift_right(addr, dst, src) <-- pshr(addr, dst, src);

    // 32-bit magic multiply: MOVSXD -> IMUL3 $MAGIC -> SAR/SHR
    #[local] relation div_magic_32(Address, Address, i64, i64, Ireg, Ireg);
    div_magic_32(addr0, addr2, *magic, *shift_n, Ireg::from(input_str), Ireg::from(imul_dst_str)) <--
        pmov(addr0, movsxd_dst, movsxd_src),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "MOVSXD",
        op_register(movsxd_dst, temp_str),
        op_register(movsxd_src, input_str),
        next(addr0, addr1),
        pimul3(addr1, imul_dst, imul_src, imul_imm),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_src_str) == Ireg::from(temp_str),
        op_immediate(imul_imm, magic, _),
        next(addr1, addr2),
        pshift_right(addr2, sar_dst, sar_src),
        op_register(sar_dst, sar_dst_str),
        if Ireg::from(sar_dst_str) == Ireg::from(imul_dst_str),
        op_immediate(sar_src, shift_n, _),
        if *shift_n >= 32;

    // GCC signed-div with COMPENSATING magic (e.g. -O1 n/7, n/11): movsxd; imul3 NEG_MAGIC; shr 0x20; add result,input; sar K; sar input,0x1f; sub result,input. Tuple: (movsxd_addr, imul_addr, magic_low32, total_shift, input_ireg, result_ireg).
    #[local] relation div_magic_32_compensating_gcc(Address, Address, i64, i64, Ireg, Ireg);
    div_magic_32_compensating_gcc(addr0, addr1, *magic, 32 + *post_shift, Ireg::from(input_str), Ireg::from(result_str)) <--
        pmov(addr0, movsxd_dst, movsxd_src),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "MOVSXD",
        op_register(movsxd_dst, result_str),
        op_register(movsxd_src, input_str),
        next(addr0, addr1),
        // imul3 result, result, NEG_MAGIC (in-place)
        pimul3(addr1, imul_dst, imul_src, imul_imm),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_dst_str) == Ireg::from(result_str),
        if Ireg::from(imul_src_str) == Ireg::from(result_str),
        op_immediate(imul_imm, magic, _),
        if (*magic as i32) < 0,
        next(addr1, addr2),
        // SHR result, 0x20 (logical)
        pshr(addr2, shr1_dst, shr1_src),
        op_register(shr1_dst, shr1_dst_str),
        if Ireg::from(shr1_dst_str) == Ireg::from(result_str),
        op_immediate(shr1_src, shr1_n, _),
        if *shr1_n == 32,
        next(addr2, addr3),
        // ADD result, input (compensation with ORIGINAL input register)
        padd(addr3, add1_dst, add1_src),
        op_register(add1_dst, add1_dst_str),
        op_register(add1_src, add1_src_str),
        if Ireg::from(add1_dst_str) == Ireg::from(result_str),
        if Ireg::from(add1_src_str) == Ireg::from(input_str),
        next(addr3, addr4),
        // SAR result, K (arithmetic post-shift)
        psar(addr4, sar_dst, sar_src),
        op_register(sar_dst, sar_dst_str),
        if Ireg::from(sar_dst_str) == Ireg::from(result_str),
        op_immediate(sar_src, post_shift, _),
        if *post_shift > 0 && *post_shift <= 31,
        next(addr4, addr5),
        // SAR input, 0x1f (sign extraction via arithmetic shift, clobbers input)
        psar(addr5, sarsign_dst, sarsign_src),
        op_register(sarsign_dst, sarsign_dst_str),
        if Ireg::from(sarsign_dst_str) == Ireg::from(input_str),
        op_immediate(sarsign_src, sign_shift, _),
        if *sign_shift == 31,
        next(addr5, addr6),
        // SUB result, input
        psub(addr6, sub_dst, sub_src),
        op_register(sub_dst, sub_dst_str),
        op_register(sub_src, sub_src_str),
        if Ireg::from(sub_dst_str) == Ireg::from(result_str),
        if Ireg::from(sub_src_str) == Ireg::from(input_str);

    mach_inst(movsxd_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)) <--
        div_magic_32_compensating_gcc(movsxd_addr, _imul_addr, magic, total_shift, input_ireg, result_ireg),
        let divisor_opt = recover_signed_divisor_compensating(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, result_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        let addr = movsxd_addr;
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, addr);
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, addr);
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, addr);
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, addr);
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, addr);
    div_consumed(addr) <--
        div_magic_32_compensating_gcc(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, a5),
        next(a5, addr);

    // Clang signed-div with COMPENSATING magic (neg i32, e.g. n/7, n/11): movsxd; imul3 NEG_MAGIC; shr 0x20; add result,partial; mov sign,result; shr sign,0x1f; sar K; add result,sign. Tuple: (movsxd_addr, imul_addr, magic_low32_signed, total_shift, input_ireg, result_ireg).
    #[local] relation div_magic_32_compensating(Address, Address, i64, i64, Ireg, Ireg);
    div_magic_32_compensating(addr0, addr1, *magic, 32 + *post_shift, Ireg::from(input_str), Ireg::from(result_str)) <--
        pmov(addr0, movsxd_dst, movsxd_src),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "MOVSXD",
        op_register(movsxd_dst, result_str),
        op_register(movsxd_src, input_str),
        next(addr0, addr1),
        // imul3 partial, result, NEG_MAGIC
        pimul3(addr1, imul_dst, imul_src, imul_imm),
        op_register(imul_dst, partial_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_src_str) == Ireg::from(result_str),
        if Ireg::from(partial_str) != Ireg::from(result_str),
        op_immediate(imul_imm, magic, _),
        if (*magic as i32) < 0,
        next(addr1, addr2),
        // SHR partial, 0x20 (logical)
        pshr(addr2, shr1_dst, shr1_src),
        op_register(shr1_dst, shr1_dst_str),
        if Ireg::from(shr1_dst_str) == Ireg::from(partial_str),
        op_immediate(shr1_src, shr1_n, _),
        if *shr1_n == 32,
        next(addr2, addr3),
        // ADD result, partial (compensation)
        padd(addr3, add1_dst, add1_src),
        op_register(add1_dst, add1_dst_str),
        op_register(add1_src, add1_src_str),
        if Ireg::from(add1_dst_str) == Ireg::from(result_str),
        if Ireg::from(add1_src_str) == Ireg::from(partial_str),
        next(addr3, addr4),
        // MOV sign_reg, result
        pmov(addr4, mov_dst, mov_src),
        op_register(mov_dst, sign_reg_str),
        op_register(mov_src, mov_src_str),
        if Ireg::from(mov_src_str) == Ireg::from(result_str),
        if Ireg::from(sign_reg_str) != Ireg::from(result_str),
        next(addr4, addr5),
        // SHR sign_reg, 0x1f (logical)
        pshr(addr5, shrsign_dst, shrsign_src),
        op_register(shrsign_dst, shrsign_dst_str),
        if Ireg::from(shrsign_dst_str) == Ireg::from(sign_reg_str),
        op_immediate(shrsign_src, sign_shift, _),
        if *sign_shift == 31,
        next(addr5, addr6),
        // SAR result, K (arithmetic)
        psar(addr6, sar_dst, sar_src),
        op_register(sar_dst, sar_dst_str),
        if Ireg::from(sar_dst_str) == Ireg::from(result_str),
        op_immediate(sar_src, post_shift, _),
        if *post_shift > 0 && *post_shift <= 31,
        next(addr6, addr7),
        // ADD result, sign_reg
        padd(addr7, add2_dst, add2_src),
        op_register(add2_dst, add2_dst_str),
        op_register(add2_src, add2_src_str),
        if Ireg::from(add2_dst_str) == Ireg::from(result_str),
        if Ireg::from(add2_src_str) == Ireg::from(sign_reg_str);

    // Emit divide at the MOVSXD address: capstone reports reg_use=[input] and reg_def=[result] there, which exactly matches our Lop's I/O.
    mach_inst(movsxd_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)) <--
        div_magic_32_compensating(movsxd_addr, _imul_addr, magic, total_shift, input_ireg, result_ireg),
        let divisor_opt = recover_signed_divisor_compensating(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, result_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    // Mark all 8 instructions of the compensating idiom as div-consumed.
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        let addr = movsxd_addr;
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, a5),
        next(a5, addr);
    div_consumed(addr) <--
        div_magic_32_compensating(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, a5),
        next(a5, a6),
        next(a6, addr);

    // Clang signed-div with separate partial reg (e.g. n/10): movsxd; imul3 POS_MAGIC partial!=result; mov sign,partial; shr sign,0x3f; sar partial,K; add partial,sign. Tuple: (movsxd_addr, imul_addr, magic, total_shift, result_ireg=movsxd dst, partial_ireg=imul dst).
    #[local] relation div_magic_32_signbias_partial(Address, Address, i64, i64, Ireg, Ireg);
    div_magic_32_signbias_partial(addr0, addr1, *magic, *post_shift, Ireg::from(result_str), Ireg::from(partial_str)) <--
        pmov(addr0, movsxd_dst, _movsxd_src),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "MOVSXD",
        op_register(movsxd_dst, result_str),
        next(addr0, addr1),
        // imul3 partial, result, POS_MAGIC
        pimul3(addr1, imul_dst, imul_src, imul_imm),
        op_register(imul_dst, partial_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_src_str) == Ireg::from(result_str),
        if Ireg::from(partial_str) != Ireg::from(result_str),
        op_immediate(imul_imm, magic, _),
        if *magic > 0 && *magic <= i32::MAX as i64,
        next(addr1, addr2),
        // MOV sign_reg, partial
        pmov(addr2, mov_dst, mov_src),
        op_register(mov_dst, sign_reg_str),
        op_register(mov_src, mov_src_str),
        if Ireg::from(mov_src_str) == Ireg::from(partial_str),
        if Ireg::from(sign_reg_str) != Ireg::from(partial_str),
        next(addr2, addr3),
        // SHR sign_reg, 0x3f
        pshr(addr3, shrsign_dst, shrsign_src),
        op_register(shrsign_dst, shrsign_dst_str),
        if Ireg::from(shrsign_dst_str) == Ireg::from(sign_reg_str),
        op_immediate(shrsign_src, sign_shift, _),
        if *sign_shift == 63,
        next(addr3, addr4),
        // SAR partial, K (arithmetic; total_shift = K)
        psar(addr4, sar_dst, sar_src),
        op_register(sar_dst, sar_dst_str),
        if Ireg::from(sar_dst_str) == Ireg::from(partial_str),
        op_immediate(sar_src, post_shift, _),
        if *post_shift >= 32 && *post_shift <= 63,
        next(addr4, addr5),
        // ADD partial, sign_reg
        padd(addr5, add_dst, add_src),
        op_register(add_dst, add_dst_str),
        op_register(add_src, add_src_str),
        if Ireg::from(add_dst_str) == Ireg::from(partial_str),
        if Ireg::from(add_src_str) == Ireg::from(sign_reg_str);

    // Emit divide at IMUL address: capstone reg_use=[result]/reg_def=[partial] matches Lop I/O; movsxd's Ocast32signed stays live.
    mach_inst(imul_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *partial_mreg)) <--
        div_magic_32_signbias_partial(_movsxd_addr, imul_addr, magic, total_shift, input_ireg, partial_ireg),
        let divisor_opt = recover_signed_divisor(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_partial, partial_ireg),
        preg_of(partial_mreg, preg_of_partial),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    // Consume IMUL through final ADD (imul, mov, shr, sar, add); MOVSXD's Ocast32signed Mop is preserved.
    div_consumed(addr) <--
        div_magic_32_signbias_partial(_, addr, _, _, _, _);
    div_consumed(addr) <--
        div_magic_32_signbias_partial(_, imul_addr, _, _, _, _),
        next(imul_addr, addr);
    div_consumed(addr) <--
        div_magic_32_signbias_partial(_, imul_addr, _, _, _, _),
        next(imul_addr, a1),
        next(a1, addr);
    div_consumed(addr) <--
        div_magic_32_signbias_partial(_, imul_addr, _, _, _, _),
        next(imul_addr, a1),
        next(a1, a2),
        next(a2, addr);
    div_consumed(addr) <--
        div_magic_32_signbias_partial(_, imul_addr, _, _, _, _),
        next(imul_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, addr);

    // Clang signed-div (small pos magic, e.g. n/3, n/5): movsxd; imul3 MAGIC; mov sign,result; shr sign,0x3f; shr result,0x20; add result,sign. Tuple: (movsxd_addr, imul_addr, magic, total_shift=32, input_ireg, result_ireg).
    #[local] relation div_magic_32_signbias(Address, Address, i64, i64, Ireg, Ireg);
    div_magic_32_signbias(addr0, addr1, *magic, 32, Ireg::from(input_str), Ireg::from(result_str)) <--
        pmov(addr0, movsxd_dst, movsxd_src),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "MOVSXD",
        op_register(movsxd_dst, result_str),
        op_register(movsxd_src, input_str),
        next(addr0, addr1),
        pimul3(addr1, imul_dst, imul_src, imul_imm),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_dst_str) == Ireg::from(result_str),
        if Ireg::from(imul_src_str) == Ireg::from(result_str),
        op_immediate(imul_imm, magic, _),
        if *magic > 0 && *magic <= i32::MAX as i64,
        next(addr1, addr2),
        // MOV sign_reg, result
        pmov(addr2, mov_dst, mov_src),
        op_register(mov_dst, sign_reg_str),
        op_register(mov_src, mov_src_str),
        if Ireg::from(mov_src_str) == Ireg::from(result_str),
        if Ireg::from(sign_reg_str) != Ireg::from(result_str),
        next(addr2, addr3),
        // SHR sign_reg, 0x3f (logical, must be SHR)
        pshr(addr3, shrsign_dst, shrsign_src),
        op_register(shrsign_dst, shrsign_dst_str),
        if Ireg::from(shrsign_dst_str) == Ireg::from(sign_reg_str),
        op_immediate(shrsign_src, sign_shift, _),
        if *sign_shift == 63,
        next(addr3, addr4),
        // SHR result, 0x20 (logical, must be SHR)
        pshr(addr4, shrres_dst, shrres_src),
        op_register(shrres_dst, shrres_dst_str),
        if Ireg::from(shrres_dst_str) == Ireg::from(result_str),
        op_immediate(shrres_src, res_shift, _),
        if *res_shift == 32,
        next(addr4, addr5),
        // ADD result_lo, sign_reg_lo
        padd(addr5, add_dst, add_src),
        op_register(add_dst, add_dst_str),
        op_register(add_src, add_src_str),
        if Ireg::from(add_dst_str) == Ireg::from(result_str),
        if Ireg::from(add_src_str) == Ireg::from(sign_reg_str);

    // Emit the divide Mop at the MOVSXD address (capstone reg_use covers the input).
    mach_inst(movsxd_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)) <--
        div_magic_32_signbias(movsxd_addr, _imul_addr, magic, total_shift, input_ireg, result_ireg),
        let divisor_opt = recover_signed_divisor(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, result_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    // Mark the entire idiom as div-consumed so the raw instructions are suppressed.
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        let addr = movsxd_addr;
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, addr);
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, addr);
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, addr);
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, addr);
    div_consumed(addr) <--
        div_magic_32_signbias(movsxd_addr, _, _, _, _, _),
        next(movsxd_addr, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, addr);

    // Magic multiply via MOV + 2-operand IMUL: `mov $MAGIC, tmp; imul reg, tmp`. Tuple: (mov_addr, shift_addr, magic, shift_n, input_ireg dividend src, result_ireg IMUL/SHR dst). IMUL is operand-symmetric: magic reg may be src or dst.
    #[local] relation div_magic_64(Address, Address, i64, i64, Ireg, Ireg);

    // Variant A: magic is the IMUL's src; magic-holding reg IS the IMUL's dst (and SHR target), i.e. it held the input before being clobbered.
    div_magic_64(addr0, addr2, *magic, *shift_n, Ireg::from(imul_dst_str), Ireg::from(imul_dst_str)) <--
        pmov(addr0, mov_dst, mov_src),
        op_register(mov_dst, temp_str),
        op_immediate(mov_src, magic, _),
        if *magic != 0,
        next(addr0, addr1),
        pimul(addr1, imul_dst, imul_src),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_src_str) == Ireg::from(temp_str),
        next(addr1, addr2),
        pshift_right(addr2, shr_dst, shr_src),
        op_register(shr_dst, shr_dst_str),
        if Ireg::from(shr_dst_str) == Ireg::from(imul_dst_str),
        op_immediate(shr_src, shift_n, _),
        if *shift_n >= 32;

    // Variant B (clang udiv): magic loaded into IMUL dst, input held in IMUL src. `mov ecx,edi; mov eax,MAGIC; imul rax,rcx; shr rax,k`.
    div_magic_64(addr0, addr2, *magic, *shift_n, Ireg::from(imul_src_str), Ireg::from(imul_dst_str)) <--
        pmov(addr0, mov_dst, mov_src),
        op_register(mov_dst, temp_str),
        op_immediate(mov_src, magic, _),
        if *magic != 0,
        next(addr0, addr1),
        pimul(addr1, imul_dst, imul_src),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if Ireg::from(imul_dst_str) == Ireg::from(temp_str),
        if Ireg::from(imul_src_str) != Ireg::from(temp_str),
        next(addr1, addr2),
        pshift_right(addr2, shr_dst, shr_src),
        op_register(shr_dst, shr_dst_str),
        if Ireg::from(shr_dst_str) == Ireg::from(imul_dst_str),
        op_immediate(shr_src, shift_n, _),
        if *shift_n >= 32;

    // Unsigned magic-divide with the magic pre-loaded in a register.  Query
    // the exact owner-keyed value reaching the IMUL; projecting a global
    // `(register, constant)` fact allowed overwritten and cross-function loads
    // to certify unrelated multiplies.
    #[local] relation imul2_magic(Address, Address, Ireg, Ireg, i64);
    imul2_magic(*func, *imul_addr, dst_ireg, src_ireg, magic) <--
        raw_magic_imul_candidate(func, imul_addr, dst_mreg, src_mreg),
        raw_gpr_exact_value(func, imul_addr, src_mreg, 8, value),
        if let RawGprValue::Constant(magic_u64) = value,
        if *magic_u64 <= u32::MAX as u64,
        let magic = *magic_u64 as i64,
        preg_of(dst_mreg, dst_preg),
        ireg_of(dst_preg, dst_ireg),
        preg_of(src_mreg, src_preg),
        ireg_of(src_preg, src_ireg);

    // Depth-bounded (<=4 hops): the SHR is at most a couple of interleaved ops past the IMUL.
    #[local] relation imul2_dst_unwritten(Address, Address, Address, Ireg, usize);
    imul2_dst_unwritten(*func, *imul_addr, *next_addr, *dst_ireg, 1) <--
        imul2_magic(func, imul_addr, dst_ireg, _, _),
        owned_straightline_step(func, imul_addr, next_addr);
    imul2_dst_unwritten(*func, *imul_addr, *next_addr, *dst_ireg, h+1) <--
        imul2_dst_unwritten(func, imul_addr, cur_addr, dst_ireg, h),
        if *h < 4,
        ireg_of(preg, dst_ireg),
        preg_of(dst_mreg, preg),
        !reg_def(cur_addr, dst_mreg),
        owned_straightline_step(func, cur_addr, next_addr);

    // div_magic_2op: a recovered unsigned magic divide, where quot_ireg is the IMUL/SHR dst and dividend_ireg is the value the IMUL read.
    #[local] relation div_magic_2op(Address, Address, i64, Ireg, Ireg);

    // The SHR of the IMUL dst, k>=32, reached without an intervening overwrite of that register.
    #[local] relation imul2_shr(Address, Address, Address, Ireg, i64);
    imul2_shr(*func, *imul_addr, *shr_addr, *dst_ireg, *shift_n) <--
        imul2_magic(func, imul_addr, dst_ireg, _, _),
        owned_straightline_step(func, imul_addr, shr_addr),
        pshr(shr_addr, shr_dst, shr_src),
        op_register(shr_dst, shr_dst_str),
        if Ireg::from(shr_dst_str) == *dst_ireg,
        if x86_gpr_view_width(shr_dst_str) == Some(8),
        op_immediate(shr_src, shift_n, _),
        if *shift_n >= 32;
    imul2_shr(*func, *imul_addr, *shr_addr, *dst_ireg, *shift_n) <--
        imul2_dst_unwritten(func, imul_addr, cur_addr, dst_ireg, _),
        owned_straightline_step(func, cur_addr, shr_addr),
        ireg_of(preg, dst_ireg),
        preg_of(dst_mreg, preg),
        !reg_def(cur_addr, dst_mreg),
        pshr(shr_addr, shr_dst, shr_src),
        op_register(shr_dst, shr_dst_str),
        if Ireg::from(shr_dst_str) == *dst_ireg,
        if x86_gpr_view_width(shr_dst_str) == Some(8),
        op_immediate(shr_src, shift_n, _),
        if *shift_n >= 32;

    // Dividend feeding the IMUL: SRC when the preceding instruction is a reg-to-reg copy into the IMUL dst, otherwise the IMUL dst already held it.
    #[local] relation imul2_dividend(Address, Address, Ireg, Ireg);
    imul2_dividend(*func, *imul_addr, Ireg::from(src_str), *quot_ireg) <--
        imul2_magic(func, imul_addr, quot_ireg, _, _),
        owned_straightline_step(func, prev_addr, imul_addr),
        pmov(prev_addr, mov_dst, mov_src),
        instruction(prev_addr, _, _, "MOV", _, _, _, _, _, _),
        op_register(mov_dst, mov_dst_str),
        if Ireg::from(mov_dst_str) == *quot_ireg,
        if x86_gpr_view_width(mov_dst_str) == Some(8),
        op_register(mov_src, src_str),
        if x86_gpr_view_width(src_str) == Some(8),
        if Ireg::from(src_str) != *quot_ireg;
    imul2_dividend(*func, *imul_addr, *quot_ireg, *quot_ireg) <--
        imul2_magic(func, imul_addr, quot_ireg, _, _),
        !magic_prev_mov_into_dst(func, imul_addr, _);

    // Helper: the instruction before the IMUL is a reg-to-reg `mov IMUL_DST, SRC`.
    #[local] relation magic_prev_mov_into_dst(Address, Address, Address);
    magic_prev_mov_into_dst(*func, *imul_addr, *prev_addr) <--
        imul2_magic(func, imul_addr, quot_ireg, _, _),
        owned_straightline_step(func, prev_addr, imul_addr),
        pmov(prev_addr, mov_dst, mov_src),
        instruction(prev_addr, _, _, "MOV", _, _, _, _, _, _),
        op_register(mov_dst, mov_dst_str),
        if Ireg::from(mov_dst_str) == *quot_ireg,
        if x86_gpr_view_width(mov_dst_str) == Some(8),
        op_register(mov_src, src_str),
        if x86_gpr_view_width(src_str) == Some(8),
        if Ireg::from(src_str) != *quot_ireg;

    #[local] relation div_magic_2op_owner(Address, Address, Address, i64, Ireg, Ireg);
    div_magic_2op_owner(*func, *imul_addr, *shr_addr, divisor, *dividend_ireg, *quot_ireg) <--
        imul2_magic(func, imul_addr, quot_ireg, _magic_reg, magic),
        imul2_shr(func, imul_addr, shr_addr, _, shift_n),
        imul2_dividend(func, imul_addr, dividend_ireg, _),
        let divisor_opt = recover_unsigned_divisor(*magic, *shift_n, 32),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        if divisor >= 2 && divisor <= 1_000_000_000;

    // Mach instructions are address-global.  A shared instruction is safe to
    // rewrite only when every inferred owner proves the same division.
    #[local] relation div_magic_2op_owner_missing(Address, Address, i64, Ireg, Ireg);
    div_magic_2op_owner_missing(*imul_addr, *shr_addr, *divisor, *dividend, *quotient) <--
        div_magic_2op_owner(_, imul_addr, shr_addr, divisor, dividend, quotient),
        instr_in_function(imul_addr, other_func),
        !div_magic_2op_owner(other_func, imul_addr, shr_addr, divisor, dividend, quotient);

    div_magic_2op(*imul_addr, *shr_addr, *divisor, *dividend, *quotient) <--
        div_magic_2op_owner(_, imul_addr, shr_addr, divisor, dividend, quotient),
        !div_magic_2op_owner_missing(imul_addr, shr_addr, divisor, dividend, quotient);

    // Emit Odivuimm at the IMUL address (capstone reg_use there covers the dividend register).
    mach_inst(imul_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *quot_mreg)) <--
        div_magic_2op(imul_addr, _shr_addr, divisor, dividend_ireg, quot_ireg),
        ireg_of(preg_of_input, dividend_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_quot, quot_ireg),
        preg_of(quot_mreg, preg_of_quot),
        let args = vec![*input_mreg],
        let op = Operation::Odivuimm(*divisor);

    // The dividend register is not necessarily a capstone operand of the IMUL, so register its use here for reaching-defs to bind the divide's input to its defining value.
    reg_use(imul_addr, *input_mreg) <--
        div_magic_2op(imul_addr, _shr_addr, _divisor, dividend_ireg, _quot_ireg),
        ireg_of(preg_of_input, dividend_ireg),
        preg_of(input_mreg, preg_of_input);

    // Suppress the raw IMUL and SHR; any intervening unrelated instruction stays, since it does not touch the dividend/quotient register.
    div_consumed(imul_addr) <-- div_magic_2op(imul_addr, _, _, _, _);
    div_consumed(shr_addr) <-- div_magic_2op(_, shr_addr, _, _, _);

    // Sign correction: SAR/SHR $31/$63 + SUB (signed division fixup)
    #[local] relation sign_correction(Address, Address, Ireg, Ireg, i64);
    sign_correction(shift_addr, sub_addr, Ireg::from(sign_str), Ireg::from(sub_dst_str), *sign_shift) <--
        pshift_right(shift_addr, sign_dst, sign_src),
        op_register(sign_dst, sign_str),
        op_immediate(sign_src, sign_shift, _),
        if *sign_shift == 31 || *sign_shift == 63,
        next(shift_addr, sub_addr),
        psub(sub_addr, sub_dst, sub_src),
        op_register(sub_dst, sub_dst_str),
        op_register(sub_src, sub_src_str),
        if Ireg::from(sub_src_str) == Ireg::from(sign_str);

    // Marks a div_magic_32 chain whose quotient WAS lowered, gating the raw-instruction suppression so a shape the consumers do not fully match keeps its correct magic arithmetic.
    #[local] relation div_magic_32_lowered(Address);

    // Signed div (32-bit): MOVSXD -> IMUL3 -> SHR/SAR -> sign_correction
    mach_inst(addr0, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)),
    div_magic_32_lowered(addr0) <--
        div_magic_32(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        next(shift_addr, sign_addr),
        sign_correction(sign_addr, _sub_addr, sign_ireg, sub_dst_ireg, sign_shift),
        if *sign_shift == 31,
        if sign_ireg == input_ireg,
        if sub_dst_ireg == result_ireg,
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, sub_dst_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    // Signed div (32-bit): MOVSXD -> IMUL3 -> SAR -> MOV copy,input -> SAR copy,31 -> SUB result,copy. GCC -O1 sign-extracts via a *copy* of the input (scheduling places copy inside sign-correction).
    mach_inst(addr0, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)),
    div_magic_32_lowered(addr0) <--
        div_magic_32(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        // input_copy = input
        next(shift_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        op_register(mov_dst, copy_str),
        op_register(mov_src, copy_src_str),
        if Ireg::from(copy_src_str) == *input_ireg,
        if Ireg::from(copy_str) != *input_ireg,
        next(mov_addr, sar_addr),
        sign_correction(sar_addr, _sub_addr, sign_ireg, sub_dst_ireg, 31),
        if *sign_ireg == Ireg::from(copy_str),
        if sub_dst_ireg == result_ireg,
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, sub_dst_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivimm(divisor);

    // Mark the input-copy MOV and the SAR after it as div_consumed too, so the raw mov/sar emissions are suppressed.
    div_consumed(mov_addr) <--
        div_magic_32(_, shift_addr, _, _, in_ireg, _),
        next(shift_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        op_register(mov_dst, copy_str),
        op_register(mov_src, copy_src_str),
        if Ireg::from(copy_src_str) == *in_ireg,
        if Ireg::from(copy_str) != *in_ireg,
        next(mov_addr, sar_addr),
        sign_correction(sar_addr, _, sign_ireg, _, 31),
        if *sign_ireg == Ireg::from(copy_str);
    div_consumed(sar_addr) <--
        div_magic_32(_, shift_addr, _, _, in_ireg, _),
        next(shift_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        op_register(mov_dst, copy_str),
        op_register(mov_src, copy_src_str),
        if Ireg::from(copy_src_str) == *in_ireg,
        if Ireg::from(copy_str) != *in_ireg,
        next(mov_addr, sar_addr),
        sign_correction(sar_addr, _, sign_ireg, _, 31),
        if *sign_ireg == Ireg::from(copy_str);
    div_consumed(sub_addr) <--
        div_magic_32(_, shift_addr, _, _, in_ireg, _),
        next(shift_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        op_register(mov_dst, copy_str),
        op_register(mov_src, copy_src_str),
        if Ireg::from(copy_src_str) == *in_ireg,
        if Ireg::from(copy_str) != *in_ireg,
        next(mov_addr, sar_addr),
        sign_correction(sar_addr, sub_addr, sign_ireg, _, 31),
        if *sign_ireg == Ireg::from(copy_str);

    // Signed div (64-bit): MOV $MAGIC -> IMUL -> SAR -> sign_correction. Emit Mop at IMUL address (capstone reports reg_use of both IMUL operands there).
    mach_inst(imul_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)) <--
        div_magic_64(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        next(addr0, imul_addr),
        next(shift_addr, sign_addr),
        sign_correction(sign_addr, _sub_addr, _sign_ireg, _sub_dst_ireg, 63),
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, result_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivlimm(divisor);

    // Unsigned div: MOV $MAGIC -> IMUL -> SHR (no sign correction).
    mach_inst(imul_addr, MachInst::Mop(op.clone(), Arc::new(args.clone()), *result_mreg)) <--
        div_magic_64(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        next(addr0, imul_addr),
        // div_magic_64 deliberately recognizes both SAR and SHR for the signed
        // family; unsigned division requires the logical form explicitly.
        pshr(shift_addr, _, _),
        let divisor_opt = recover_unsigned_divisor(*magic, *shift_n, 32),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        ireg_of(preg_of_input, input_ireg),
        preg_of(input_mreg, preg_of_input),
        ireg_of(preg_of_result, result_ireg),
        preg_of(result_mreg, preg_of_result),
        let args = vec![*input_mreg],
        let op = Operation::Odivuimm(divisor);


    // Mark div-magic-consumed instructions so generic rules skip them.
    #[local] relation div_consumed(Address);

    // 32-bit: MOVSXD(addr0) -> IMUL(addr1) -> SHIFT(addr2) -> SAR(addr3) -> SUB(addr4); MOVSXD also marked consumed since the Odivimm Mop is re-emitted there (suppress its raw Ocast32signed). Gated on div_magic_32_lowered so an unmatched magic shape (no Odivimm emitted) keeps its raw instructions.
    div_consumed(movsxd_addr) <--
        div_magic_32(movsxd_addr, _, _, _, _, _),
        div_magic_32_lowered(movsxd_addr);
    div_consumed(imul_addr) <--
        div_magic_32(movsxd_addr, _, _, _, _, _),
        div_magic_32_lowered(movsxd_addr),
        next(movsxd_addr, imul_addr);
    div_consumed(shift_addr) <--
        div_magic_32(movsxd_addr, shift_addr, _, _, _, _),
        div_magic_32_lowered(movsxd_addr);
    div_consumed(sar_addr) <--
        div_magic_32(movsxd_addr, shift_addr, _, _, _, _),
        div_magic_32_lowered(movsxd_addr),
        next(shift_addr, sar_addr);
    div_consumed(sub_addr) <--
        div_magic_32(movsxd_addr, shift_addr, _, _, _, _),
        div_magic_32_lowered(movsxd_addr),
        next(shift_addr, sar_addr),
        next(sar_addr, sub_addr);

    // 64-bit: MOV(addr0) -> IMUL(addr1) -> SHIFT(addr2) [-> SAR(addr3) -> SUB(addr4)]
    div_consumed(mov_addr) <--
        div_magic_64(mov_addr, _, _, _, _, _);
    div_consumed(imul_addr) <--
        div_magic_64(mov_addr, _, _, _, _, _),
        next(mov_addr, imul_addr);
    div_consumed(shift_addr) <--
        div_magic_64(_, shift_addr, _, _, _, _);
    div_consumed(sar_addr) <--
        div_magic_64(_, shift_addr, _, _, _, _),
        next(shift_addr, sar_addr);
    div_consumed(sub_addr) <--
        div_magic_64(_, shift_addr, _, _, _, _),
        next(shift_addr, sar_addr),
        next(sar_addr, sub_addr);

    // Magic-modulo recognition: x86-64 lowers `n % K` as q = magic-divide(n, K); t = q * K (1-3 LEA/ADD/IMUL); r = n - t. Synthesize one Omodimm/Omodlimm Mop at the SUB; upstream Odivimm/Odivlimm stays for sources using both q and r.

    // Owner and the exact point which reads the dividend remain attached to
    // every quotient fact.  Downstream modulo recovery compares the value at
    // that point with the value reaching the final SUB; a register name alone
    // is not provenance.
    // (owner, input point, endpoint, quotient, divisor, dividend, width,
    // unsigned).
    #[local] relation divide_q(Address, Address, Address, Ireg, i64, Ireg, i64, bool);

    // One provenance shape for every exact unsigned magic divide accepted by
    // this pass.  GCC commonly uses a preloaded magic register and reaches the
    // newer div_magic_2op matcher; Clang commonly loads the magic immediately
    // before IMUL and reaches the older div_magic_64 matcher.  Both produce the
    // same quotient identity, and downstream remainder recovery must not
    // depend on which syntactic recognizer happened to find it.
    // Tuple: (IMUL/use site, quotient endpoint, quotient, divisor, dividend,
    // result width).
    #[local] relation unsigned_divide_origin(Address, Address, Address, Ireg, i64, Ireg, bool);
    unsigned_divide_origin(*func, *imul_addr, *shr_addr, *quotient, *divisor, *dividend, false) <--
        div_magic_2op_owner(func, imul_addr, shr_addr, divisor, dividend, quotient),
        !div_magic_2op_owner_missing(imul_addr, shr_addr, divisor, dividend, quotient);

    unsigned_divide_origin(*func, *imul_addr, *shift_addr, *result, divisor, *input, false) <--
        div_magic_64(magic_load, shift_addr, magic, shift_n, input, result),
        owned_straightline_step(func, magic_load, imul_addr),
        owned_straightline_step(func, imul_addr, shift_addr),
        pimul(imul_addr, imul_dst, imul_src),
        op_register(imul_dst, imul_dst_str),
        op_register(imul_src, imul_src_str),
        if x86_gpr_view_width(imul_dst_str) == Some(8),
        if x86_gpr_view_width(imul_src_str) == Some(8),
        pshr(shift_addr, shift_dst, _),
        op_register(shift_dst, shift_dst_str),
        if x86_gpr_view_width(shift_dst_str) == Some(8),
        let divisor_opt = recover_unsigned_divisor(*magic, *shift_n, 32),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        if divisor >= 2 && divisor <= 1_000_000_000;

    divide_q(*func, *imul_addr, *endpoint, *quotient, *divisor, *input, width, true) <--
        unsigned_divide_origin(func, imul_addr, endpoint, quotient, divisor, input, is_long),
        let width = if *is_long { 8 } else { 4 };

    // div_magic_32 variant 1: MOVSXD->IMUL3->SAR->sign_correction(SAR31, SUB).
    divide_q(*func, *addr0, *sub_addr, *result_ireg, divisor, *input_ireg, 4, false) <--
        div_magic_32(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        instr_in_function(addr0, func),
        instr_in_function(sub_addr, func),
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(shift_addr, sign_addr),
        sign_correction(sign_addr, sub_addr, sign_ireg, sub_dst_ireg, 31),
        if sign_ireg == input_ireg,
        if sub_dst_ireg == result_ireg;

    // div_magic_32 variant 2: MOVSXD->IMUL3->SAR->MOV(copy)->SAR->SUB.
    divide_q(*func, *addr0, *sub_addr, *result_ireg, divisor, *input_ireg, 4, false) <--
        div_magic_32(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        instr_in_function(addr0, func),
        instr_in_function(sub_addr, func),
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(shift_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        op_register(mov_dst, copy_str),
        op_register(mov_src, copy_src_str),
        if Ireg::from(*copy_src_str) == *input_ireg,
        if Ireg::from(*copy_str) != *input_ireg,
        next(mov_addr, sar_addr),
        sign_correction(sar_addr, sub_addr, sign_ireg, sub_dst_ireg, 31),
        if *sign_ireg == Ireg::from(*copy_str),
        if sub_dst_ireg == result_ireg;

    // div_magic_32_compensating_gcc: 7 instructions ending at the SUB.
    divide_q(*func, *addr0, addr6, *result_ireg, divisor, *input_ireg, 4, false) <--
        div_magic_32_compensating_gcc(addr0, _, magic, total_shift, input_ireg, result_ireg),
        instr_in_function(addr0, func),
        instr_in_function(addr6, func),
        let divisor_opt = recover_signed_divisor_compensating(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(addr0, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, a5),
        next(a5, addr6);

    // div_magic_32_compensating (clang): 8 instructions ending at the final ADD.
    divide_q(*func, *addr0, addr7, *result_ireg, divisor, *input_ireg, 4, false) <--
        div_magic_32_compensating(addr0, _, magic, total_shift, input_ireg, result_ireg),
        instr_in_function(addr0, func),
        instr_in_function(addr7, func),
        let divisor_opt = recover_signed_divisor_compensating(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(addr0, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, a5),
        next(a5, a6),
        next(a6, addr7);

    // div_magic_32_signbias_partial (clang n/10 partial-reg): 6 instrs (movsxd + 5), end at ADD; q in partial_ireg. The relation's 5th field is MOVSXD's dst; use MOVSXD's src for divide_q so the mod Mop's input is the original param, not the suppressed cast dst.
    divide_q(*func, *movsxd_addr, addr5, *partial_ireg, divisor, Ireg::from(*movsxd_src_str), 4, false) <--
        div_magic_32_signbias_partial(movsxd_addr, imul_addr, magic, total_shift, _result_ireg, partial_ireg),
        instr_in_function(movsxd_addr, func),
        instr_in_function(addr5, func),
        let divisor_opt = recover_signed_divisor(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        pmov(movsxd_addr, _movsxd_dst, movsxd_src),
        op_register(movsxd_src, movsxd_src_str),
        next(imul_addr, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, addr5);

    // div_magic_32_signbias (clang small magic, n/3 etc.): 6 instrs ending at ADD.
    divide_q(*func, *addr0, addr5, *result_ireg, divisor, *input_ireg, 4, false) <--
        div_magic_32_signbias(addr0, _, magic, total_shift, input_ireg, result_ireg),
        instr_in_function(addr0, func),
        instr_in_function(addr5, func),
        let divisor_opt = recover_signed_divisor(*magic, *total_shift),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(addr0, a1),
        next(a1, a2),
        next(a2, a3),
        next(a3, a4),
        next(a4, addr5);

    // div_magic_64 (signed): MOV->IMUL->SHR/SAR->sign_correction(SAR63, SUB).
    divide_q(*func, *imul_addr, *sub_addr, *result_ireg, divisor, *input_ireg, 8, false) <--
        div_magic_64(addr0, shift_addr, magic, shift_n, input_ireg, result_ireg),
        owned_straightline_step(func, addr0, imul_addr),
        instr_in_function(sub_addr, func),
        let divisor_opt = recover_signed_divisor(*magic, *shift_n),
        if divisor_opt.is_some(),
        let divisor = divisor_opt.unwrap(),
        next(shift_addr, sign_addr),
        sign_correction(sign_addr, sub_addr, _, _, 63);

    // q_factor(owner, divide endpoint, point, register, factor, input,
    // divisor, exact value width, unsigned, semantic participants).  Every
    // transition stays inside one owned basic block.  The small participant
    // set records only instructions which compute q*K; transparent interleaved
    // instructions are never deleted when the idiom is replaced.
    #[local] relation q_factor(Address, Address, Address, Ireg, i64, Ireg, i64, i64, bool, Set<Address>);

    q_factor(*func, *end_addr, *end_addr, *q_ireg, 1, *input_ireg, *divisor,
             *width, *is_unsigned, Set::default()) <--
        divide_q(func, _, end_addr, q_ireg, divisor, input_ireg, width, is_unsigned);

    q_factor(*func, *origin, *lea_addr, dst_ireg, new_factor, *input, *divisor,
             *width, *is_unsigned, new_participants) <--
        q_factor(func, origin, prev_addr, base_ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, lea_addr),
        plea(lea_addr, lea_dst, lea_src),
        op_indirect(lea_src, _, base_str, idx_str, scale, 0, _),
        if Ireg::from(*base_str) == *base_ireg,
        if Ireg::from(*idx_str) == *base_ireg,
        if *scale >= 1 && *scale <= 8,
        let new_factor = factor.checked_mul(scale + 1).unwrap_or(0),
        if new_factor != 0,
        op_register(lea_dst, dst_str),
        if x86_gpr_view_width(dst_str) == Some(*width),
        let dst_ireg = Ireg::from(*dst_str),
        if let Some(new_participants) = q_participants_with(participants, *lea_addr);

    q_factor(*func, *origin, *add_addr, dst_ireg, new_factor, *input, *divisor,
             *width, *is_unsigned, new_participants) <--
        q_factor(func, origin, prev_addr, dst_ireg, f_dst, input, divisor, width, is_unsigned, dst_participants),
        q_factor(func, origin, prev_addr, src_ireg, f_src, input, divisor, width, is_unsigned, src_participants),
        owned_straightline_step(func, prev_addr, add_addr),
        padd(add_addr, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        if x86_gpr_view_width(dst_str) == Some(*width),
        if x86_gpr_view_width(src_str) == Some(*width),
        if Ireg::from(*dst_str) == *dst_ireg,
        if Ireg::from(*src_str) == *src_ireg,
        let new_factor = f_dst.checked_add(*f_src).unwrap_or(0),
        if new_factor != 0,
        if let Some(new_participants) = q_participants_merge(dst_participants, src_participants, *add_addr);

    q_factor(*func, *origin, *imul_addr, dst_ireg, new_factor, *input, *divisor,
             *width, *is_unsigned, new_participants) <--
        q_factor(func, origin, prev_addr, src_ireg, f_src, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, imul_addr),
        pimul3(imul_addr, imul_dst, imul_src, imul_imm),
        op_register(imul_src, src_str),
        op_register(imul_dst, dst_str),
        if x86_gpr_view_width(src_str) == Some(*width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        if Ireg::from(*src_str) == *src_ireg,
        op_immediate(imul_imm, imm, _),
        let new_factor = f_src.checked_mul(*imm).unwrap_or(0),
        if new_factor != 0,
        let dst_ireg = Ireg::from(*dst_str),
        if let Some(new_participants) = q_participants_with(participants, *imul_addr);

    q_factor(*func, *origin, *mov_addr, dst_ireg, *factor, *input, *divisor,
             *width, *is_unsigned, new_participants) <--
        q_factor(func, origin, prev_addr, src_ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, mov_addr),
        pmov(mov_addr, mov_dst, mov_src),
        instruction(mov_addr, _, _, "MOV", _, _, _, _, _, _),
        op_register(mov_src, src_str),
        op_register(mov_dst, dst_str),
        if x86_gpr_view_width(src_str) == Some(*width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        if Ireg::from(*src_str) == *src_ireg,
        let dst_ireg = Ireg::from(*dst_str),
        if dst_ireg != *src_ireg,
        if let Some(new_participants) = q_participants_with(participants, *mov_addr);

    // The recognized instruction alphabet may contain unrelated operations.
    // They preserve a q fact only when their destination is a different
    // physical register, and are deliberately absent from participants.
    q_factor(*func, *origin, *lea_addr, *ireg, *factor, *input, *divisor,
             *width, *is_unsigned, participants.clone()) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, lea_addr),
        plea(lea_addr, lea_dst, _),
        op_register(lea_dst, dst_str),
        if Ireg::from(*dst_str) != *ireg;

    q_factor(*func, *origin, *add_addr, *ireg, *factor, *input, *divisor,
             *width, *is_unsigned, participants.clone()) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, add_addr),
        padd(add_addr, add_dst, _),
        op_register(add_dst, dst_str),
        if Ireg::from(*dst_str) != *ireg;

    q_factor(*func, *origin, *imul_addr, *ireg, *factor, *input, *divisor,
             *width, *is_unsigned, participants.clone()) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, imul_addr),
        pimul3(imul_addr, imul_dst, _, _),
        op_register(imul_dst, dst_str),
        if Ireg::from(*dst_str) != *ireg;

    q_factor(*func, *origin, *mov_addr, *ireg, *factor, *input, *divisor,
             *width, *is_unsigned, participants.clone()) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, mov_addr),
        pmov(mov_addr, mov_dst, _),
        op_register(mov_dst, dst_str),
        if Ireg::from(*dst_str) != *ireg;

    q_factor(*func, *origin, *mov_addr, *ireg, *factor, *input, *divisor,
             *width, *is_unsigned, participants.clone()) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor, width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, mov_addr),
        pmov(mov_addr, mov_dst, _),
        !op_register(mov_dst, _);

    // SUB n,qK is a remainder only when the exact value read by the divide is
    // also the exact value reaching the SUB destination.  The raw-value
    // lattice proves this across copies, joins, and definitions; no arbitrary
    // MOV elsewhere in the binary can lend provenance.
    #[local] relation mod_synth_owner(Address, Address, Mreg, i64, i64, bool, Set<Address>);
    mod_synth_owner(*func, *sub_addr, *result_mreg, *divisor, *width,
                    *is_unsigned, participants.clone()) <--
        psub(sub_addr, sub_dst_sym, sub_src_sym),
        op_register(sub_src_sym, sub_src_str),
        op_register(sub_dst_sym, sub_dst_str),
        let sub_src_ireg = Ireg::from(*sub_src_str),
        let sub_dst_ireg = Ireg::from(*sub_dst_str),
        owned_straightline_step(func, prev_addr, sub_addr),
        q_factor(func, origin, prev_addr, sub_src_ireg, divisor, input_ireg,
                 divisor_q, width, is_unsigned, participants),
        if x86_gpr_view_width(sub_src_str) == Some(*width),
        if x86_gpr_view_width(sub_dst_str) == Some(*width),
        if *divisor == *divisor_q,
        divide_q(func, input_point, origin, _, divisor, input_ireg, width, is_unsigned),
        ireg_of(input_preg, input_ireg),
        preg_of(input_mreg, input_preg),
        ireg_of(result_preg, &sub_dst_ireg),
        preg_of(result_mreg, result_preg),
        raw_gpr_exact_value(func, input_point, input_mreg, width, value),
        raw_gpr_exact_value(func, sub_addr, result_mreg, width, value);

    #[local] relation mod_synth_owner_missing(Address, Mreg, i64, i64, bool, Set<Address>);
    mod_synth_owner_missing(*sub_addr, *result, *divisor, *width,
                            *is_unsigned, participants.clone()) <--
        mod_synth_owner(_, sub_addr, result, divisor, width, is_unsigned, participants),
        instr_in_function(sub_addr, other_func),
        !mod_synth_owner(other_func, sub_addr, result, divisor, width, is_unsigned, participants);

    #[local] relation mod_synth(Address, Mreg, i64, i64, bool, Set<Address>);
    mod_synth(*sub_addr, *result, *divisor, *width, *is_unsigned, participants.clone()) <--
        mod_synth_owner(_, sub_addr, result, divisor, width, is_unsigned, participants),
        !mod_synth_owner_missing(sub_addr, result, divisor, width, is_unsigned, participants);

    // Emit the modulus Mop at the SUB address.
    mach_inst(sub_addr, MachInst::Mop(op, Arc::new(args.clone()), *result_mreg)) <--
        mod_synth(sub_addr, result_mreg, divisor, width, is_unsigned, _),
        let args = vec![*result_mreg],
        let op = match (*width, *is_unsigned) {
            (4, false) => Operation::Omodimm(*divisor),
            (4, true) => Operation::Omoduimm(*divisor),
            (8, false) => Operation::Omodlimm(*divisor),
            (8, true) => Operation::Omodluimm(*divisor),
            _ => unreachable!("modulo proof admits only exact 32/64-bit views"),
        };

    // The synthesized Omod reads a dividend register that is not a capstone operand of the SUB, so register the use here or RTL fabricates an undefined dividend (0 % K).
    reg_use(sub_addr, *result_mreg) <--
        mod_synth(sub_addr, result_mreg, _, _, _, _);

    // Clang also spells an unsigned remainder as
    //
    //   input = holder + C
    //   q = input / K
    //   qk = q * K
    //   qk = -qk
    //   qk += holder
    //   qk += C
    //
    // (DEC is the common final adjustment for C=-1).  This is the same exact
    // quotient/remainder identity as the SUB form above, but the old matcher
    // stopped at NEG and emitted the whole strength-reduced expression.  Keep
    // the divide endpoint in every fact so register reuse by another magic
    // division cannot cross-pollinate the proof.
    // The specialized affine proof is another flat lattice: one exact
    // holder+C description or Top.  Its payload is constant-sized, and the
    // holder's raw symbolic value is captured at the LEA so the same value can
    // be required both at the IMUL and at the later ADD.
    #[local] relation unsigned_affine_tracked_reg(Address, Mreg, i64);
    unsigned_affine_tracked_reg(*func, *input_mreg, width) <--
        unsigned_divide_origin(func, imul_addr, _, _, _, input, is_long),
        let width = if *is_long { 8 } else { 4 },
        ireg_of(input_preg, input),
        preg_of(input_mreg, input_preg);

    #[local] relation unsigned_affine_seed(Address, Mreg, i64, Mreg, i64);
    unsigned_affine_seed(*addr, dst_mreg, *width, *holder_mreg, *disp) <--
        plea(addr, dst, src),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        let dst_mreg = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, index_str, scale, disp, _),
        if (*index_str == "NONE" || index_str.is_empty()) && *scale == 1,
        if *width == 4 || x86_gpr_view_width(base_str) == Some(8),
        let holder_ireg = Ireg::from(*base_str),
        if holder_ireg != Ireg::Unknown,
        ireg_of(holder_preg, holder_ireg),
        preg_of(holder_mreg, holder_preg),
        if dst_mreg != *holder_mreg;

    #[local] relation unsigned_affine_seed_value(Address, Address, Mreg, i64, UnsignedAffineValue);
    unsigned_affine_seed_value(*func, *addr, *tracked, *width,
                               UnsignedAffineValue { holder: *holder,
                                                     displacement: *disp,
                                                     holder_value: *holder_value }) <--
        unsigned_affine_seed(addr, tracked, width, holder, disp),
        raw_gpr_exact_value(func, addr, holder, width, holder_value);

    #[local] lattice unsigned_affine_in(Address, Address, Mreg, i64, ConstPropagation<UnsignedAffineValue>);
    #[local] lattice unsigned_affine_out(Address, Address, Mreg, i64, ConstPropagation<UnsignedAffineValue>);

    unsigned_affine_in(*func, *func, *tracked, *width,
                       ConstPropagation::Constant(UnsignedAffineValue {
                           holder: *tracked,
                           displacement: 0,
                           holder_value: RawGprValue::LiveIn(*tracked, *width),
                       })) <--
        unsigned_affine_tracked_reg(func, tracked, width),
        instr_in_function(func, func);

    unsigned_affine_in(*func, *succ, *tracked, *width, state.clone()) <--
        unsigned_affine_out(func, addr, tracked, width, state),
        cfg_step(addr, succ),
        instr_in_function(succ, func);

    unsigned_affine_out(*func, *addr, *tracked, *width,
                        ConstPropagation::Constant(*value)) <--
        unsigned_affine_in(func, addr, tracked, width, _),
        unsigned_affine_seed_value(func, addr, tracked, width, value),
        !raw_gpr_barrier(addr);

    unsigned_affine_out(*func, *addr, *tracked, *width, ConstPropagation::Top) <--
        unsigned_affine_in(func, addr, tracked, width, _),
        reg_def(addr, tracked),
        !unsigned_affine_seed_value(func, addr, tracked, width, _),
        !raw_gpr_barrier(addr);

    unsigned_affine_out(*func, *addr, *tracked, *width, state.clone()) <--
        unsigned_affine_in(func, addr, tracked, width, state),
        !reg_def(addr, tracked),
        !raw_gpr_barrier(addr);

    unsigned_affine_out(*func, *addr, *tracked, *width, ConstPropagation::Top) <--
        unsigned_affine_in(func, addr, tracked, width, _),
        raw_gpr_barrier(addr);

    #[local] relation unsigned_affine_candidate(Address, Address, Mreg, i64, UnsignedAffineValue);
    unsigned_affine_candidate(*func, *addr, *tracked, *width, value) <--
        unsigned_affine_in(func, addr, tracked, width, state),
        if let ConstPropagation::Constant(value) = state;

    #[local] relation unsigned_affine_conflict(Address, Address, Mreg, i64);
    unsigned_affine_conflict(*func, *addr, *tracked, *width) <--
        unsigned_affine_in(func, addr, tracked, width, state),
        if matches!(state, ConstPropagation::Top);

    #[local] relation unsigned_affine_exact(Address, Address, Mreg, i64, UnsignedAffineValue);
    unsigned_affine_exact(*func, *addr, *tracked, *width, *value) <--
        unsigned_affine_candidate(func, addr, tracked, width, value),
        !unsigned_affine_conflict(func, addr, tracked, width),
        !raw_gpr_unresolved_owner(func);

    #[local] relation unsigned_dividend_affine_owner(Address, Address, Address, Ireg, Ireg, i64, i64, UnsignedAffineValue);
    unsigned_dividend_affine_owner(*func, *imul_addr, *endpoint, *quotient,
                                   *input, *divisor, width, *value) <--
        unsigned_divide_origin(func, imul_addr, endpoint, quotient, divisor, input, is_long),
        let width = if *is_long { 8 } else { 4 },
        ireg_of(input_preg, input),
        preg_of(input_mreg, input_preg),
        unsigned_affine_exact(func, imul_addr, input_mreg, width, value),
        raw_gpr_exact_value(func, imul_addr, &value.holder, width, holder_value),
        if *holder_value == value.holder_value;

    #[local] relation negated_q_factor(Address, Address, Address, Ireg, i64, Ireg, i64, i64, bool, Set<Address>);
    negated_q_factor(*func, *origin, *neg_addr, *ireg, *factor, *input,
                     *divisor, *width, *is_unsigned, new_participants) <--
        q_factor(func, origin, prev_addr, ireg, factor, input, divisor,
                 width, is_unsigned, participants),
        owned_straightline_step(func, prev_addr, neg_addr),
        pneg(neg_addr, neg_dst),
        op_register(neg_dst, neg_dst_str),
        if x86_gpr_view_width(neg_dst_str) == Some(*width),
        if Ireg::from(*neg_dst_str) == *ireg,
        let new_participants = participants_with(participants, *neg_addr);

    // Exact immediate change made by one raw integer instruction.  This is
    // value algebra only; no address/order comparison is used for dataflow.
    #[local] relation integer_reg_adjust(Address, Ireg, i64, i64);
    integer_reg_adjust(addr, Ireg::from(*dst_str), *delta, *width) <--
        padd(addr, dst, src),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        op_immediate(src, delta, _);
    integer_reg_adjust(addr, Ireg::from(*dst_str), delta, *width) <--
        psub(addr, dst, src),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width),
        op_immediate(src, amount, _),
        if let Some(delta) = amount.checked_neg();
    integer_reg_adjust(addr, Ireg::from(*dst_str), 1, *width) <--
        instruction(addr, _, _, "INC", dst, _, _, _, _, _),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width);
    integer_reg_adjust(addr, Ireg::from(*dst_str), -1, *width) <--
        instruction(addr, _, _, "DEC", dst, _, _, _, _, _),
        op_register(dst, dst_str),
        raw_gpr_width(width),
        if x86_gpr_view_width(dst_str) == Some(*width);

    // After the ADD, result = input - K*q - affine_disp.  Therefore the raw
    // trailing adjustment must equal affine_disp for the chain to be exactly
    // input % K.
    #[local] relation negated_q_dividend_sum_owner(Address, Address, Address, Ireg, Ireg, i64, i64, i64, Set<Address>);
    negated_q_dividend_sum_owner(*func, *origin, *add_addr, *result,
                                 holder, affine_disp, *divisor, *width,
                                 new_participants) <--
        negated_q_factor(func, origin, prev_addr, result, factor, input,
                         divisor, width, true, participants),
        if factor == divisor,
        owned_straightline_step(func, prev_addr, add_addr),
        padd(add_addr, add_dst, add_src),
        op_register(add_dst, add_dst_str),
        op_register(add_src, add_src_str),
        if x86_gpr_view_width(add_dst_str) == Some(*width),
        if x86_gpr_view_width(add_src_str) == Some(*width),
        if Ireg::from(*add_dst_str) == *result,
        let holder = Ireg::from(*add_src_str),
        if holder != *result,
        let holder_mreg = Mreg::x86(add_src_str),
        unsigned_dividend_affine_owner(func, _, origin, _, input, divisor,
                                       width, affine),
        if holder_mreg == affine.holder,
        raw_gpr_exact_value(func, add_addr, &holder_mreg, width, holder_value),
        if *holder_value == affine.holder_value,
        let affine_disp = affine.displacement,
        let new_participants = participants_with(participants, *add_addr);

    // (add node, final modulo node, result register, affine holder,
    // affine displacement, divisor, width).  With a nonzero displacement the
    // ADD node first reconstructs the original dividend from the still-live
    // holder, and the raw adjustment node becomes the modulo.  Both semantic
    // definitions therefore remain at real machine definition sites.
    #[local] relation neg_add_mod_synth_owner(Address, Address, Address, Mreg, Mreg, i64, i64, i64, Set<Address>);
    neg_add_mod_synth_owner(*func, *add_addr, *add_addr, *result_mreg,
                            *holder_mreg, 0, *divisor, *width,
                            participants.clone()) <--
        negated_q_dividend_sum_owner(func, _, add_addr, result, holder,
                                     affine_disp, divisor, width, participants),
        if *affine_disp == 0,
        ireg_of(result_preg, result),
        preg_of(result_mreg, result_preg),
        ireg_of(holder_preg, holder),
        preg_of(holder_mreg, holder_preg);
    neg_add_mod_synth_owner(*func, *add_addr, *final_addr, *result_mreg,
                            *holder_mreg, *affine_disp, *divisor, *width,
                            final_participants) <--
        negated_q_dividend_sum_owner(func, _, add_addr, result, holder,
                                     affine_disp, divisor, width, participants),
        if *affine_disp != 0,
        owned_straightline_step(func, add_addr, final_addr),
        integer_reg_adjust(final_addr, final_reg, correction, width),
        if final_reg == result && correction == affine_disp,
        ireg_of(result_preg, result),
        preg_of(result_mreg, result_preg),
        ireg_of(holder_preg, holder),
        preg_of(holder_mreg, holder_preg),
        let final_participants = participants_with(participants, *final_addr);

    #[local] relation neg_add_mod_synth_owner_missing(Address, Address, Mreg, Mreg, i64, i64, i64, Set<Address>);
    neg_add_mod_synth_owner_missing(*add_addr, *final_addr, *result,
                                    *holder, *disp, *divisor, *width,
                                    participants.clone()) <--
        neg_add_mod_synth_owner(_, add_addr, final_addr, result, holder, disp,
                                divisor, width, participants),
        instr_in_function(final_addr, other_func),
        !neg_add_mod_synth_owner(other_func, add_addr, final_addr, result,
                                 holder, disp, divisor, width, participants);

    #[local] relation neg_add_mod_synth(Address, Address, Mreg, Mreg, i64, i64, i64, Set<Address>);
    neg_add_mod_synth(*add_addr, *final_addr, *result, *holder, *disp,
                      *divisor, *width, participants.clone()) <--
        neg_add_mod_synth_owner(_, add_addr, final_addr, result, holder, disp,
                                divisor, width, participants),
        !neg_add_mod_synth_owner_missing(add_addr, final_addr, result, holder,
                                         disp, divisor, width, participants);

    // Zero-displacement form: the still-live holder is already the dividend,
    // so the ADD's real definition site can directly carry the remainder.
    mach_inst(add_addr, MachInst::Mop(op, Arc::new(vec![*holder_mreg]), *result_mreg)) <--
        neg_add_mod_synth(add_addr, final_addr, result_mreg, holder_mreg,
                          affine_disp, divisor, width, _),
        if add_addr == final_addr && *affine_disp == 0,
        let op = if *width == 8 { Operation::Omodluimm(*divisor) } else { Operation::Omoduimm(*divisor) };

    // Nonzero-displacement form: rebuild input=holder+C at the ADD, then use
    // the following real result definition for the bounded unsigned modulus.
    mach_inst(add_addr, MachInst::Mop(op, Arc::new(vec![*holder_mreg]), *result_mreg)) <--
        neg_add_mod_synth(add_addr, final_addr, result_mreg, holder_mreg,
                          affine_disp, _, width, _),
        if add_addr != final_addr && *affine_disp != 0,
        let op = if *width == 8 { Operation::Oaddlimm(*affine_disp) } else { Operation::Oaddimm(*affine_disp) };
    mach_inst(final_addr, MachInst::Mop(op, Arc::new(vec![*result_mreg]), *result_mreg)) <--
        neg_add_mod_synth(add_addr, final_addr, result_mreg, _, affine_disp,
                          divisor, width, _),
        if add_addr != final_addr && *affine_disp != 0,
        let op = if *width == 8 { Operation::Omodluimm(*divisor) } else { Operation::Omoduimm(*divisor) };

    reg_use(add_addr, *holder_mreg) <--
        neg_add_mod_synth(add_addr, _, _, holder_mreg, _, _, _, _);
    reg_use(final_addr, *result_mreg) <--
        neg_add_mod_synth(add_addr, final_addr, result_mreg, _, affine_disp, _, _, _),
        if add_addr != final_addr && *affine_disp != 0;

    // Suppress exactly the semantic participants selected above.  Transparent
    // MOV/LEA/ADD/IMUL instructions crossed by q propagation remain intact.
    div_consumed(sub_addr) <-- mod_synth(sub_addr, _, _, _, _, _);
    div_consumed(*addr) <--
        mod_synth(_, _, _, _, _, participants),
        for addr in participants.0.iter();
    div_consumed(final_addr) <--
        neg_add_mod_synth(_, final_addr, _, _, _, _, _, _);
    div_consumed(*addr) <--
        neg_add_mod_synth(_, _, _, _, _, _, _, participants),
        for addr in participants.0.iter();

    // Two-branch JP+JNE float != on registers: match the pair on a shared resolved TARGET ADDRESS via direct_jump, since the disassembler may give the same target distinct operand symbol strings.
    mach_inst(addr0, MachInst::Mcond(
        Condition::Cnotcompf(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        lbl
    )) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, _lbl_p),
        direct_jump(addr1, tgt),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl),
        direct_jump(addr2, tgt);

    mach_inst(addr0, MachInst::Mcond(
        Condition::Cnotcompfs(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        lbl
    )) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, _lbl_p),
        direct_jump(addr1, tgt),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl),
        direct_jump(addr2, tgt);

    // Ordered float equality with a success-value MOV between JP and JE:
    // ucomis*; jp false; mov $1,result; je success. MOV preserves flags, so
    // the JE still consumes the compare and exactly means ordered equality.
    mach_inst(eq_jcc, MachInst::Mcond(
        Condition::Ccompfs(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        success
    )),
    mcond_at_jcc(*eq_jcc),
    reg_use(*eq_jcc, arg1),
    reg_use(*eq_jcc, arg2) <--
        pucomiss(cmp, r1, r2),
        op_register(r1, r1_name),
        op_register(r2, r2_name),
        reg_xmm(r1_name),
        reg_xmm(r2_name),
        let arg1 = Mreg::x86(r1_name),
        let arg2 = Mreg::x86(r2_name),
        next(cmp, parity_jcc),
        pjcc(parity_jcc, TestCond::CondP, _),
        direct_jump(parity_jcc, false_target),
        next(parity_jcc, set_true),
        instruction(set_true, _, _, "MOV", one, true_dst, _, _, _, _),
        op_immediate(one, one_value, _),
        if *one_value == 1,
        op_register(true_dst, _),
        next(set_true, eq_jcc),
        pjcc(eq_jcc, TestCond::CondE, success),
        next(eq_jcc, false_fallthrough),
        if false_fallthrough == false_target;

    mach_inst(eq_jcc, MachInst::Mcond(
        Condition::Ccompf(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        success
    )),
    mcond_at_jcc(*eq_jcc),
    reg_use(*eq_jcc, arg1),
    reg_use(*eq_jcc, arg2) <--
        pucomisd(cmp, r1, r2),
        op_register(r1, r1_name),
        op_register(r2, r2_name),
        reg_xmm(r1_name),
        reg_xmm(r2_name),
        let arg1 = Mreg::x86(r1_name),
        let arg2 = Mreg::x86(r2_name),
        next(cmp, parity_jcc),
        pjcc(parity_jcc, TestCond::CondP, _),
        direct_jump(parity_jcc, false_target),
        next(parity_jcc, set_true),
        instruction(set_true, _, _, "MOV", one, true_dst, _, _, _, _),
        op_immediate(one, one_value, _),
        if *one_value == 1,
        op_register(true_dst, _),
        next(set_true, eq_jcc),
        pjcc(eq_jcc, TestCond::CondE, success),
        next(eq_jcc, false_fallthrough),
        if false_fallthrough == false_target;


    transl_load_inferred(addr, *chunk, addrmode, regs.clone(), dst) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, r2, idx_str, _scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        if !mnem_upper.contains("MOVZ") && !mnem_upper.contains("MOVS");

    // Indexed load (non-SP/non-BP base with index register)
    transl_load_inferred(addr, *chunk, addrmode, regs.clone(), dst) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, r2, idx_str, scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*arg, *idx_arg]),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        if !mnem_upper.contains("MOVZ") && !mnem_upper.contains("MOVS");

    // Scaled-index load with no base register: mov disp(,%idx,scale), dst.
    transl_load_inferred(addr, *chunk, addrmode, regs.clone(), dst) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, scale, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: None,
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*idx_arg]),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        if !mnem_upper.contains("MOVZ") && !mnem_upper.contains("MOVS");

    transl_load(addr, mc, addrmode, regs, dst) <--
        transl_load_inferred(addr, mc, addrmode, regs, dst);

    transl_load(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(dst, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(src, _, r2, idx_str, _scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        !transl_load_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    // Indexed load (mnemonic-based, non-SP/non-BP base with index register)
    transl_load(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(dst, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(src, _, r2, idx_str, scale, disp, msize),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*arg, *idx_arg]),
        !transl_load_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    // Scaled-index load with no base register (mnemonic-based): mov disp(,%idx,scale), dst
    transl_load(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(dst, dst_str),
        let dst_reg = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, scale, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode{
            base: None,
            index: Some((Ireg::from(idx_str), *scale)),
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_idx, Ireg::from(idx_str)),
        preg_of(idx_arg, preg_of_idx),
        let regs = Arc::new(vec![*idx_arg]),
        !transl_load_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    mach_inst(addr, MachInst::Mload(*memory_chunk, addressing, Arc::new(args), *dst)) <--
        transl_load(addr, memory_chunk, addrmode, regs, dst),
        !addrmode_needs_resolution(addr, *addrmode, _),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, None);

    // Resolved load: transl_load whose addrmode needs symbol resolution (e.g., absolute displacement)
    mach_inst(addr, MachInst::Mload(*memory_chunk, addressing, Arc::new(args), *src)) <--
        transl_load(addr, memory_chunk, addrmode, regs, src),
        addrmode_needs_resolution(addr, *addrmode, target_addr),
        site_resolved_addr_to_symbol(addr, target_addr, ident, offset),
        let resolved = Some((*ident, *offset)),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, resolved);

    mach_inst(addr, MachInst::Mload(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, _, _, disp, source_width),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, destination_chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_direct_load_chunk(mnem, *destination_chunk, *source_width);

    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), src)) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, base_str, _, _, disp, msize),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    // Absolute addressing load: mov 0x40402c, %eax (base="NONE", disp is the address)
    mach_inst(addr, MachInst::Mload(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, _, disp, source_width),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, destination_chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_direct_load_chunk(mnem, *destination_chunk, *source_width);

    // Scaled-index absolute addressing load
    mach_inst(addr, MachInst::Mload(mc, Addressing::Abasedscaled(*scale, *ident, *offset), Arc::new(vec![idx_mreg]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, scale, disp, source_width),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let idx_mreg = Mreg::x86(*idx_str),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, destination_chunk),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_direct_load_chunk(mnem, *destination_chunk, *source_width);

    mach_inst(addr, MachInst::Mload(mc, Addressing::Abasedscaled(*scale, *ident, *offset), Arc::new(vec![idx_mreg]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, scale, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let idx_mreg = Mreg::x86(*idx_str),
        !ireg_hold_type(dst_str.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    // Absolute addressing load (mnemonic-based fallback)
    mach_inst(addr, MachInst::Mload(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, base_str, idx_str, _, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        !ireg_hold_type(dst_str.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem_ext(mnem), *msize);

    // Absolute addressing store: mov %eax, 0x40402c (base="NONE", disp is the address)
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), src)) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, base_str, idx_str, _, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        let mc = refine_chunk_with_size(*chunk, *msize);

    // Absolute addressing store (mnemonic-based fallback)
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), src)) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, base_str, idx_str, _, disp, msize),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        !ireg_hold_type(src_str.to_string(), _),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        let mc = refine_chunk_with_size(chunk_from_mnem(mnem), *msize);

    // Absolute addressing immediate store: movl $0x1, 0x40402c (base="NONE", disp is the address)
    mach_inst(addr, MachInst::Mop(Operation::Ointconst(imm_int), Arc::new(vec![]), Mreg::DI)) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, sz),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, _, _),
        let imm_int = *imm_sym as i64;

    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::DI)) <--
        pmov(addr, dst, src),
        op_immediate(src, _, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, sz),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        // 3.8d: carry the operand's true width; refine_chunk_with_size narrows 1/2-byte sizes and keeps 4/8 as int chunks.
        let mc = refine_chunk_with_size(if *sz <= 4 { MemoryChunk::MInt32 } else { MemoryChunk::MInt64 }, *sz);


    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), *res)) <--
        pmov(address, rd, rs),
        !div_consumed(address),
        op_register(rd, res_str),
        ireg_of(preg_of_r, Ireg::from(res_str)),
        preg_of(res, preg_of_r),
        op_register(rs, arg_str),
        ireg_of(preg_of_rs, Ireg::from(arg_str)),
        preg_of(arg, preg_of_rs),
        let args = vec![*arg];

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(vec![src]), dst)) <--
        pmov(address, rd, rs),
        !div_consumed(address),
        op_register(rd, dst_str),
        reg_xmm(dst_str),
        op_register(rs, src_str),
        let dst = Mreg::x86(dst_str),
        let src = Mreg::x86(src_str);

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(vec![src]), dst)) <--
        pmov(address, rd, rs),
        !div_consumed(address),
        op_register(rd, dst_str),
        op_register(rs, src_str),
        reg_xmm(src_str),
        let dst = Mreg::x86(dst_str),
        let src = Mreg::x86(src_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(imm_int), Arc::new(args), *res)) <--
        pmov(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(imm_int), Arc::new(args), *res)) <--
        pmov(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(0), Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    // Divergence: XOR r,r can also be a genuine self-XOR (Asmgen.v: Oxor compiles to Pxorl_rr)
    mach_inst(address, MachInst::Mop(Operation::Oxor, Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![*res, *res];

    mach_inst(address, MachInst::Mop(Operation::Oxorl, Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![*res, *res];

    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*imm_str as usize), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(*imm_str as i64), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        !div_consumed(address),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*imm_str as i64), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        !div_consumed(address),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(*imm_str), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        !div_consumed(address),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        if *imm_str != 0,
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*imm_str), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        !div_consumed(address),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        if *imm_str != 0,
        !immediate_nonzero_data_symbol(*imm_str as Address),
        let args = vec![];

    mach_inst(address, MachInst::Mop(cast_op, Arc::new(args.clone()), *res)) <--
        pmov(address, r, r1),
        !div_consumed(address),
        op_register(r1, r1_str),
        op_register(r, r_str),
        reg_is_64(r1_str, r1_is_64),
        reg_is_64(r_str, r_is_64),
        if r1_is_64 != r_is_64,
        ireg_of(preg_of_r1, Ireg::from(r1_str)),
        preg_of(a1, preg_of_r1),
        ireg_of(preg_of_res, Ireg::from(r_str)),
        preg_of(res, preg_of_res),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let args = vec![*a1],
        let cast_op = if mnem_upper.starts_with("MOVZX") || mnem_upper.starts_with("MOVZB") {
            if is_reg_8(r1_str) {
                Operation::Ocast8unsigned
            } else {
                Operation::Ocast16unsigned
            }
        } else if mnem_upper.starts_with("MOVSXD") || mnem_upper.starts_with("CDQE") {
            Operation::Ocast32signed
        } else if mnem_upper.starts_with("MOVSX") || mnem_upper.starts_with("MOVSB") || mnem_upper.starts_with("MOVSW") {
            if is_reg_8(r1_str) {
                Operation::Ocast8signed
            } else {
                Operation::Ocast16signed
            }
        } else {
            Operation::Ocast8signed
        };

    // Sub-32-bit sign/zero extension via MOVSX/MOVZX from 8/16-bit source (prior rule only fires for reg_is_64 operands).
    mach_inst(address, MachInst::Mop(cast_op, Arc::new(args.clone()), *res)) <--
        pmov(address, r, r1),
        op_register(r1, r1_str),
        op_register(r, r_str),
        if is_reg_8(r1_str) || is_reg_16(r1_str),
        if !is_reg_8(r_str) && !is_reg_16(r_str),
        ireg_of(preg_of_r1, Ireg::from(r1_str)),
        preg_of(a1, preg_of_r1),
        ireg_of(preg_of_res, Ireg::from(r_str)),
        preg_of(res, preg_of_res),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let args = vec![*a1],
        let cast_op = if mnem_upper.starts_with("MOVZX") || mnem_upper.starts_with("MOVZB") || mnem_upper.starts_with("MOVZW") {
            if is_reg_8(r1_str) { Operation::Ocast8unsigned } else { Operation::Ocast16unsigned }
        } else if mnem_upper.starts_with("MOVSX") || mnem_upper.starts_with("MOVSB") || mnem_upper.starts_with("MOVSW") {
            if is_reg_8(r1_str) { Operation::Ocast8signed } else { Operation::Ocast16signed }
        } else {
            if is_reg_8(r1_str) { Operation::Ocast8signed } else { Operation::Ocast16signed }
        };

    mach_inst(address, MachInst::Mop(Operation::Oneg, Arc::new(args), *res)) <--
        pneg(address, r),
        !div_consumed(address),
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psub(address, r, r2),
        !div_consumed(address),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Osubl } else { Operation::Osub };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psbb(address, r, r2),
        !sbb_self_carry_lifted(address),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Osubl } else { Operation::Osub };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padc(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Oaddl } else { Operation::Oadd };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psbb(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        !adc_carry_lifted(address),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padc(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        !adc_carry_lifted(address),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) };

    // cmp + adc/sbb is branchless conditional-accumulate: model CF as the 0/1 result of the compare's carry condition so rtl_pass can expand it, instead of discarding CF and lowering a dead acc += imm.
    #[local] relation padc_or_sbb(Address);
    padc_or_sbb(addr) <-- padc(addr, _, _);
    padc_or_sbb(addr) <-- psbb(addr, _, _);

    #[local] relation cmp_adc_link(Address, Address);
    cmp_adc_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        padc_or_sbb(addr1);
    cmp_adc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _),
        padc_or_sbb(addr1);
    cmp_adc_link(addr0, addr2) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        padc_or_sbb(addr2);
    cmp_adc_link(addr0, addr3) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, addr3),
        padc_or_sbb(addr3);

    // adc_carry_op: the carry-aware fact rtl_pass expands, carrying the compare's carry condition, the add-vs-subtract selector, the residual constant, and the accumulator width.
    relation adc_carry_op(Address, Address, Condition, bool, i64, bool, Mreg, Mreg);
    #[local] relation adc_carry_lifted(Address);
    adc_carry_lifted(adc_addr) <-- adc_carry_op(adc_addr, _, _, _, _, _, _, _);

    // adc $imm,%acc with carry from `cmp $cimm,%creg`: acc = acc + CF + imm, CF = (creg <u cimm).
    adc_carry_op(adc_addr, cmp_addr, cf_cond, false, imm_int, acc_is_64, acc_mreg, cmp_mreg) <--
        padc(adc_addr, acc_r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(acc_r, acc_str),
        reg_is_64(acc_str, acc_is_64),
        let acc_mreg = Mreg::x86(acc_str),
        cmp_adc_link(cmp_addr, adc_addr),
        pcmp(cmp_addr, cmp_r, cmp_imm),
        op_register(cmp_r, cmp_str),
        op_immediate(cmp_imm, cimm, _),
        reg_is_64(cmp_str, cmp_is_64),
        let cmp_mreg = Mreg::x86(cmp_str),
        let cf_cond = if *cmp_is_64 { Condition::Ccompluimm(Comparison::Clt, *cimm) } else { Condition::Ccompuimm(Comparison::Clt, *cimm) };

    // sbb $imm,%acc with carry from `cmp $cimm,%creg`: acc = acc - CF - imm, CF = (creg <u cimm).
    adc_carry_op(adc_addr, cmp_addr, cf_cond, true, -imm_int, acc_is_64, acc_mreg, cmp_mreg) <--
        psbb(adc_addr, acc_r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(acc_r, acc_str),
        reg_is_64(acc_str, acc_is_64),
        let acc_mreg = Mreg::x86(acc_str),
        cmp_adc_link(cmp_addr, adc_addr),
        pcmp(cmp_addr, cmp_r, cmp_imm),
        op_register(cmp_r, cmp_str),
        op_immediate(cmp_imm, cimm, _),
        reg_is_64(cmp_str, cmp_is_64),
        let cmp_mreg = Mreg::x86(cmp_str),
        let cf_cond = if *cmp_is_64 { Condition::Ccompluimm(Comparison::Clt, *cimm) } else { Condition::Ccompuimm(Comparison::Clt, *cimm) };

    // `sbb %r,%r` is not a subtraction.  dst - dst - CF is -CF, so the whole
    // instruction materializes the preceding compare's carry as a 0/-1 mask and
    // the register's old value is irrelevant.  Lowering it as Osub(r, r) drops
    // the carry and folds to a constant 0, silently turning a computed boolean
    // into a fixed value; this is the dominant sbb form in optimized code, so
    // the carry has to be recovered rather than discarded.
    #[local] relation psbb_self(Address, Symbol);
    psbb_self(addr, r) <--
        psbb(addr, r, a1),
        op_register(r, r_str),
        op_register(a1, a1_str),
        if r_str == a1_str;

    // Instructions whose carry-out a following self-sbb can read.  CMP is the
    // ordinary compare; NEG sets CF from "operand was nonzero", which is how
    // `x != 0` gets booleanized branchlessly.
    #[local] relation carry_flag_src(Address);
    carry_flag_src(addr) <-- pcmp(addr, _, _);
    carry_flag_src(addr) <-- pneg(addr, _);

    // Same tolerance as cmp_adc_link: the carry survives instructions that do
    // not write flags, which is where the scheduler puts the sbb's own setup.
    #[local] relation carry_src_sbb_link(Address, Address);
    carry_src_sbb_link(src_addr, sbb_addr) <--
        carry_flag_src(src_addr),
        next(src_addr, sbb_addr),
        psbb_self(sbb_addr, _);
    carry_src_sbb_link(src_addr, sbb_addr) <--
        carry_flag_src(src_addr),
        next(src_addr, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, sbb_addr),
        psbb_self(sbb_addr, _);
    carry_src_sbb_link(src_addr, sbb_addr) <--
        carry_flag_src(src_addr),
        next(src_addr, addr1),
        instruction(addr1, _, _, mnem1, _, _, _, _, _, _),
        if !is_flag_setting(mnem1),
        next(addr1, addr2),
        instruction(addr2, _, _, mnem2, _, _, _, _, _, _),
        if !is_flag_setting(mnem2),
        next(addr2, sbb_addr),
        psbb_self(sbb_addr, _);

    // sbb_self_carry_op: acc = -Ocmp(cf_cond, regs read at flag_addr).  cf_arg2
    // is Mreg::Unknown when the condition takes a single register, the compared
    // immediate being folded into the condition itself.
    relation sbb_self_carry_op(Address, Address, Condition, bool, Mreg, Mreg, Mreg);
    #[local] relation sbb_self_carry_lifted(Address);
    sbb_self_carry_lifted(sbb_addr) <-- sbb_self_carry_op(sbb_addr, _, _, _, _, _, _);

    // `cmp $cimm,%creg; sbb %acc,%acc`: CF = (creg <u cimm).
    sbb_self_carry_op(sbb_addr, cmp_addr, cf_cond, acc_is_64, acc_mreg, cmp_mreg, Mreg::Unknown) <--
        psbb_self(sbb_addr, acc_r),
        op_register(acc_r, acc_str),
        reg_is_64(acc_str, acc_is_64),
        let acc_mreg = Mreg::x86(acc_str),
        if acc_mreg != Mreg::Unknown,
        carry_src_sbb_link(cmp_addr, sbb_addr),
        pcmp(cmp_addr, cmp_r, cmp_imm),
        op_register(cmp_r, cmp_str),
        op_immediate(cmp_imm, cimm, _),
        reg_is_64(cmp_str, cmp_is_64),
        let cmp_mreg = Mreg::x86(cmp_str),
        if cmp_mreg != Mreg::Unknown,
        let cf_cond = if *cmp_is_64 { Condition::Ccompluimm(Comparison::Clt, *cimm) } else { Condition::Ccompuimm(Comparison::Clt, *cimm) };

    // `cmp %src,%dst; sbb %acc,%acc`: CF = (dst <u src).  pcmp's second field is
    // the compare's destination operand, so it is the left-hand side.
    sbb_self_carry_op(sbb_addr, cmp_addr, cf_cond, acc_is_64, acc_mreg, lhs_mreg, rhs_mreg) <--
        psbb_self(sbb_addr, acc_r),
        op_register(acc_r, acc_str),
        reg_is_64(acc_str, acc_is_64),
        let acc_mreg = Mreg::x86(acc_str),
        if acc_mreg != Mreg::Unknown,
        carry_src_sbb_link(cmp_addr, sbb_addr),
        pcmp(cmp_addr, lhs_r, rhs_r),
        op_register(lhs_r, lhs_str),
        op_register(rhs_r, rhs_str),
        reg_is_64(lhs_str, cmp_is_64),
        let lhs_mreg = Mreg::x86(lhs_str),
        let rhs_mreg = Mreg::x86(rhs_str),
        if lhs_mreg != Mreg::Unknown && rhs_mreg != Mreg::Unknown,
        let cf_cond = if *cmp_is_64 { Condition::Ccomplu(Comparison::Clt) } else { Condition::Ccompu(Comparison::Clt) };

    // `neg %nreg; sbb %acc,%acc`: NEG sets CF exactly when its operand was
    // nonzero, so this is acc = -(nreg != 0).  The operand is read at the NEG's
    // own address, which is its pre-negation value.
    sbb_self_carry_op(sbb_addr, neg_addr, cf_cond, acc_is_64, acc_mreg, neg_mreg, Mreg::Unknown) <--
        psbb_self(sbb_addr, acc_r),
        op_register(acc_r, acc_str),
        reg_is_64(acc_str, acc_is_64),
        let acc_mreg = Mreg::x86(acc_str),
        if acc_mreg != Mreg::Unknown,
        carry_src_sbb_link(neg_addr, sbb_addr),
        pneg(neg_addr, neg_r),
        op_register(neg_r, neg_str),
        reg_is_64(neg_str, neg_is_64),
        let neg_mreg = Mreg::x86(neg_str),
        if neg_mreg != Mreg::Unknown,
        let cf_cond = if *neg_is_64 { Condition::Ccompluimm(Comparison::Cne, 0) } else { Condition::Ccompuimm(Comparison::Cne, 0) };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padd(address, r, r2),
        !div_consumed(address),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Oaddl } else { Operation::Oadd };

    // Divergence: ADD reg,reg can also be Olea(Aindexed2(0)); CompCert has no Oadd for x86, register addition is Olea(Aindexed2 0) compiling to LEA r,[r1+r2].
    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padd(address, r, r2),
        !div_consumed(address),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Oleal(Addressing::Aindexed2(0)) } else { Operation::Olea(Addressing::Aindexed2(0)) };

    mach_inst(address, MachInst::Mop(op, Arc::new(empty_args), *res)) <--
        plea(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_indirect(src_addr, _, base_str, idx_str, _, offset, _),
        reg_sp(base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        reg_is_64(dst_str, dst_is_64),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        sp_lea_shift(address, depth),
        let addressing = Addressing::Ainstack(offset - depth),
        let op = if *dst_is_64 { Operation::Oleal(addressing) } else { Operation::Olea(addressing) },
        let empty_args = vec![];

    // `mov reg, rsp` is `lea reg, 0(%rsp)`, so its slot identity is the raw
    // post-frame-allocation displacement 0 -- the coordinate system every other
    // frame reference uses (Mgetstack/Msetstack disp, Mstore(Ainstack),
    // `lea disp(%rsp)`).  Naming it by the entry-relative SP delta instead put
    // an escaping out-parameter base in a different coordinate system than the
    // frame it names, so nothing downstream could size or index the object.
    mach_inst(address, MachInst::Mop(op, Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_reg),
        op_register(src_reg, src_str),
        reg_sp(src_str),
        op_register(dst_reg, dst_str),
        !reg_sp(dst_str),
        reg_is_64(dst_str, dst_is_64),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        stack_offset(_, address, rsp_offsets),
        if let Some(_rsp_ofs) = exact_stack_offset(&rsp_offsets.0),
        let addressing = Addressing::Ainstack(0),
        let op = if *dst_is_64 { Operation::Oleal(addressing) } else { Operation::Olea(addressing) },
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*ident as usize), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_immediate(src_addr, symbol_addr, _),
        !reg_64(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        immediate_nonzero_data_symbol(*symbol_addr as Address),
        resolved_addr_to_symbol(*symbol_addr as Address, ident, _offset),
        if *ident != 0,
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*ident as usize), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_immediate(src_addr, symbol_addr, _),
        reg_64(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        immediate_nonzero_data_symbol(*symbol_addr as Address),
        resolved_addr_to_symbol(*symbol_addr as Address, ident, _offset),
        if *ident != 0,
        let empty_args = vec![];

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(symbol_name)))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_immediate(dst, imm_addr, _),
        symbols(*imm_addr as Address, symbol_name, _);

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padd(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) };

    // INC reg / DEC reg: capstone emits these as their own mnemonics (not ADD/SUB), so lower them as add of immediate +/-1; without this they emit no Mach op and are silently dropped, corrupting dataflow (e.g. a setcc then inc idiom loses its +1).
    mach_inst(address, MachInst::Mop(op, Arc::new(vec![*res]), *res)) <--
        instruction(address, _, _, "INC", dst, _, _, _, _, _),
        !div_consumed(address),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        reg_is_64(dst_str, is_64),
        let op = if *is_64 { Operation::Oaddlimm(1) } else { Operation::Oaddimm(1) };

    mach_inst(address, MachInst::Mop(op, Arc::new(vec![*res]), *res)) <--
        instruction(address, _, _, "DEC", dst, _, _, _, _, _),
        !div_consumed(address),
        op_register(dst, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        reg_is_64(dst_str, is_64),
        let op = if *is_64 { Operation::Oaddlimm(-1) } else { Operation::Oaddimm(-1) };

    // base="NONE" excluded: Mreg::x86("NONE") is Unknown so the load leg cannot lower and would conflict with the Aglobal float_load_op route.
    //
    // An SP base is admitted by the same rule rather than by a companion: Mreg::x86 maps every SP
    // spelling ("RSP"/"ESP"/"SP"/"SPL") to Mreg::SP, exactly the set reg_sp names, so the separate
    // SP rules ADD and IMUL used to carry produced these very tuples. Excluding SP from the others
    // left `sub/and/or/xor disp(%rsp), reg` matching NO rule at all, and an instruction that matches
    // no rule does not merely lose its own effect: stripped du's `or 0x18(%rsp),%eax` was the only
    // surviving read of a frame slot, so its absence made the slot's initializer dead and the RTL
    // optimizer deleted `bit_flags = FTS_PHYSICAL` from main. du then called fts_open with an
    // uninitialized flag word and segfaulted in the traversal.
    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        padd(address, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        psub(address, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // Register-source memory RMW.  The decoded memory width is authoritative:
    // all subregister spellings map to their full machine register, so testing
    // only `reg_is_64` widens byte/word writes to four bytes.  SP is an ordinary
    // base here; keeping it in this shared family prevents operation-specific
    // holes such as a stack-relative SUB/AND/OR/XOR silently disappearing.
    arith_store_reg(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(src_str)) <--
        padd(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_store_reg(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(src_str)) <--
        psub(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // AND/OR/XOR with memory destination: previously emitted arith_load_op (wrong direction), clobbering the source register and silently dropping the memory store (3.8c direction bug).
    arith_store_reg(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(src_str)) <--
        pand(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_store_reg(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(src_str)) <--
        por(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_store_reg(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(src_str)) <--
        pxor(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // Atomic XADD: the store side is the load-op-store recovered as add %reg,(%mem); capstone's operand order is (reg, mem), so bind op_register on field4 and op_indirect on field5 directly.
    arith_store_reg(*addr, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(reg_str)) <--
        instruction(addr, _, _, mnem, reg_op, mem_op, _, _, _, _),
        if *mnem == "LOCK XADD" || *mnem == "XADD",
        op_register(reg_op, reg_str),
        op_indirect(mem_op, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *memory_size == 8 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // Atomic XCHG: the store half is a plain register-to-memory store routed through pmov so transl_store builds the addrmode; operand order is (reg, mem) like XADD.
    pmov(addr, mem_op, reg_op) <--
        instruction(addr, _, _, "XCHG", reg_op, mem_op, _, _, _, _),
        op_register(reg_op, _),
        op_indirect(mem_op, _, base_str, idx, _, _, _),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_sp(base_str),
        !reg_ip(base_str);

    // AND/OR/XOR with memory source: previously no rule matched so the instruction vanished (3.8c); mirrors padd/psub arith_load_op, RIP excluded.
    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        pand(address, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        por(address, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        pxor(address, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // INDEXED memory-source integer arithmetic, routed through float_load_op
    // whose lowering is operation-agnostic and takes a full Addressing, since
    // arith_load_op cannot represent the index register.  Keep SP/BP here too:
    // rtl_pass classifies a structural frame base and expands it through
    // Olea(Ainstack) before the indexed load.  Excluding SP made forms such as
    // `xor -24(%rsp,%rdi,4), %eax` disappear completely; excluding the logical
    // operations did the same for every non-stack indexed AND/OR/XOR.
    float_load_op(*addr, op, chunk, addressing, Arc::new(vec![base_mreg, idx_mreg]), Mreg::x86(dst_str), false) <--
        padd(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx_str, scale, disp, memory_size),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let base_mreg = Mreg::x86(base_str),
        let idx_mreg = Mreg::x86(idx_str),
        let addressing = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) },
        let op = if *dst_is_64 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, addressing, Arc::new(vec![base_mreg, idx_mreg]), Mreg::x86(dst_str), false) <--
        psub(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx_str, scale, disp, memory_size),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let base_mreg = Mreg::x86(base_str),
        let idx_mreg = Mreg::x86(idx_str),
        let addressing = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) },
        let op = if *dst_is_64 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, addressing, Arc::new(vec![base_mreg, idx_mreg]), Mreg::x86(dst_str), false) <--
        pand(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx_str, scale, disp, memory_size),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let base_mreg = Mreg::x86(base_str),
        let idx_mreg = Mreg::x86(idx_str),
        let addressing = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) },
        let op = if *dst_is_64 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, addressing, Arc::new(vec![base_mreg, idx_mreg]), Mreg::x86(dst_str), false) <--
        por(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx_str, scale, disp, memory_size),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let base_mreg = Mreg::x86(base_str),
        let idx_mreg = Mreg::x86(idx_str),
        let addressing = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) },
        let op = if *dst_is_64 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, addressing, Arc::new(vec![base_mreg, idx_mreg]), Mreg::x86(dst_str), false) <--
        pxor(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx_str, scale, disp, memory_size),
        if *idx_str != "NONE" && !idx_str.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let base_mreg = Mreg::x86(base_str),
        let idx_mreg = Mreg::x86(idx_str),
        let addressing = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) },
        let op = if *dst_is_64 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // RIP-relative integer memory-source arithmetic (3.8c): arith_load_op cannot express a global ident and excludes RIP, so routed through float_load_op whose rtl lowering is operation-agnostic.
    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        padd(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, _, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        psub(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, _, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        pand(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, _, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        por(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, _, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        pxor(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, _, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // Absolute-addressed (clang -fno-pie) memory-source arith: base="NONE" with the address in disp; abs_target_addr rows exist for padd/psub/pand/por/pxor.
    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        padd(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        psub(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        pand(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        por(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    float_load_op(*addr, op, chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::x86(dst_str), false) <--
        pxor(addr, dst, src),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *dst_is_64 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // ADD/SUB immediate to memory: RIP excluded because Mreg::x86("RIP") is Unknown and would shadow the ident-keyed arith_store_abs_imm RIP route.
    arith_store_imm(*address, op, chunk, Mreg::x86(base_str), *disp) <--
        padd(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *sz == 8 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_imm(*address, op, chunk, Mreg::x86(base_str), *disp) <--
        psub(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *sz == 8 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // AND/OR/XOR immediate to memory: previously no rule matched (reg-dest Oandimm requires op_register on dst) so the instruction vanished (3.8c family).
    arith_store_imm(*address, op, chunk, Mreg::x86(base_str), *disp) <--
        pand(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *sz == 8 { Operation::Oandlimm(imm_int) } else { Operation::Oandimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_imm(*address, op, chunk, Mreg::x86(base_str), *disp) <--
        por(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *sz == 8 { Operation::Oorlimm(imm_int) } else { Operation::Oorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_imm(*address, op, chunk, Mreg::x86(base_str), *disp) <--
        pxor(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *sz == 8 { Operation::Oxorlimm(imm_int) } else { Operation::Oxorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // Absolute addressing arith: add reg, 0x40402c (read-modify-write at global)
    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        padd(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        psub(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // Absolute addressing arith: addl $imm, 0x40402c (read-modify-write at global)
    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        padd(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        psub(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // RIP-relative memory-dest arithmetic (3.8c): absolute-addressing rules require base="NONE"; the RIP form resolved nothing and the whole RMW vanished; arith_store_abs_* is ident-keyed so applies unchanged.
    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        padd(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddl } else { Operation::Oadd },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        psub(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Osubl } else { Operation::Osub },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        padd(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        psub(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // AND/OR/XOR global RMW (RIP-relative and -fno-pie absolute): previously no rule matched and the whole RMW vanished (3.8c); arith_store_abs_* is op-agnostic.
    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        pand(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        por(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        pxor(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        pand(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oandl } else { Operation::Oand },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        por(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oorl } else { Operation::Oor },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_reg(*address, op, chunk, *ident, *offset, Mreg::x86(src_str)) <--
        pxor(address, dst, src),
        op_register(src, src_str),
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oxorl } else { Operation::Oxor },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        pand(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oandlimm(imm_int) } else { Operation::Oandimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        por(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oorlimm(imm_int) } else { Operation::Oorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        pxor(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, disp, sz),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oxorlimm(imm_int) } else { Operation::Oxorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        pand(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oandlimm(imm_int) } else { Operation::Oandimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        por(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oorlimm(imm_int) } else { Operation::Oorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    arith_store_abs_imm(*address, op, chunk, *ident, *offset) <--
        pxor(address, dst, src),
        op_immediate(src, imm_str, _),
        let imm_int = *imm_str as i64,
        op_indirect(dst, _, base_str, idx, _, _, sz),
        if *idx == "NONE" || idx.is_empty(),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let op = if *sz == 8 { Operation::Oxorlimm(imm_int) } else { Operation::Oxorimm(imm_int) },
        if let Some(chunk) = integer_memory_chunk(*sz);

    // abs_target_addr for and/or/xor RMW destinations so they resolve to synthesized idents; mirrors the padd/psub dst-side rows (the src-side rows cover only the memory-source direction).
    abs_target_addr(addr, target) <--
        pand(addr, dst, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        por(addr, dst, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    abs_target_addr(addr, target) <--
        pxor(addr, dst, _),
        op_indirect(dst, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        let target = *disp as Address;

    mach_inst(address, MachInst::Mop(Operation::Omul, Arc::new(args), *res)) <--
        pimul(address, r, r2),
        !div_consumed(address),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tint,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];


    mach_inst(address, MachInst::Mop(Operation::Omulimm(imm_int), Arc::new(args), *res)) <--
        pimul(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    // 3-operand IMUL (32-bit): imul dst, src, imm; suppressed inside div-by-constant.
    mach_inst(address, MachInst::Mop(Operation::Omulimm(imm_int), Arc::new(args), *res)) <--
        pimul3(address, dst, src, imm),
        !div_consumed(address),
        op_immediate(imm, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(dst, dst_str),
        ireg_hold_type(dst_str.to_string(), typ),
        if *typ == Typ::Tint,
        op_register(src, src_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(src_arg, preg_of_src),
        let args = vec![*src_arg];

    // 3-operand IMUL (64-bit): imul dst, src, imm; suppressed inside div-by-constant.
    mach_inst(address, MachInst::Mop(Operation::Omullimm(imm_int), Arc::new(args), *res)) <--
        pimul3(address, dst, src, imm),
        !div_consumed(address),
        op_immediate(imm, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(dst, dst_str),
        ireg_hold_type(dst_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        op_register(src, src_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(src_arg, preg_of_src),
        let args = vec![*src_arg];

    // IMUL with a SIMPLE memory source (SP-relative included) loads the value and multiplies via arith_load_op; the legacy rules treated the memory operand as its base register's value and dropped the load.
    arith_load_op(*address, op, chunk, Mreg::x86(base_str), *disp, Mreg::x86(dst_str)) <--
        pimul(address, dst, src),
        !div_consumed(address),
        op_register(dst, dst_str),
        reg_is_64(dst_str, dst_is_64),
        op_indirect(src, _, base_str, idx, _, disp, memory_size),
        if *idx == "NONE" || idx.is_empty(),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        let op = if *dst_is_64 { Operation::Omull } else { Operation::Omul },
        if let Some(chunk) = integer_memory_chunk(*memory_size);

    // Legacy fallback for an INDEXED memory source: keep the base-register approximation, since there is no arith_load_op indexed form yet.
    mach_inst(address, MachInst::Mop(Operation::Omul, Arc::new(args), *res)) <--
        pimul(address, r, mem),
        !div_consumed(address),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tint,
        op_indirect(mem, _, base_str, idx, _, disp, _),
        if *idx != "NONE" && !idx.is_empty(),
        if !base_str.is_empty() && *base_str != "NONE",
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*res, *base_arg];

    mach_inst(address, MachInst::Mop(Operation::Omull, Arc::new(args), *res)) <--
        pimul(address, r, mem),
        !div_consumed(address),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        op_indirect(mem, _, base_str, idx, _, disp, _),
        if *idx != "NONE" && !idx.is_empty(),
        if !base_str.is_empty() && *base_str != "NONE",
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*res, *base_arg];

    mach_inst(address, MachInst::Mop(Operation::Omulhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omulhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit signed div: CDQ before IDIV -> Odiv (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odiv, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CDQ", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit unsigned div: xor EDX,EDX before DIV -> Odivu (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, rd, rs),
        op_register(rd, rd_str),
        op_register(rs, rs_str),
        if *rd_str == *rs_str,
        if *rd_str == "EDX" || *rd_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit signed mod: CDQ before IDIV -> Omod (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omod, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CDQ", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit unsigned mod: xor EDX,EDX before DIV -> Omodu (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, rd, rs),
        op_register(rd, rd_str),
        op_register(rs, rs_str),
        if *rd_str == *rs_str,
        if *rd_str == "EDX" || *rd_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: IDIV without CDQ predecessor, treat as signed 32-bit
    mach_inst(address, MachInst::Mop(Operation::Odiv, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omod, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: DIV without xor RDX predecessor, treat as unsigned 32-bit
    mach_inst(address, MachInst::Mop(Operation::Odivu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Standalone CDQ/CQO sign-extension is a real definition of DX when no IDIV consumes it (the manual signed modulo-by-power-of-two idiom), so emit the arithmetic-shift sign replication.
    mach_inst(addr, MachInst::Mop(Operation::Oshrimm(31), Arc::new(vec![Mreg::AX]), Mreg::DX)) <--
        instruction(addr, _, _, "CDQ", _, _, _, _, _, _),
        prev_instr(next, addr),
        !pidiv(next, _, _);

    mach_inst(addr, MachInst::Mop(Operation::Oshrlimm(63), Arc::new(vec![Mreg::AX]), Mreg::DX)) <--
        instruction(addr, _, _, "CQO", _, _, _, _, _, _),
        prev_instr(next, addr),
        !pidiv(next, _, _);


    mach_inst(address, MachInst::Mop(Operation::Oand, Arc::new(args), *res)) <--
        pand(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        !reg_64(r_str),
        !reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandimm(imm_int), Arc::new(args), *res)) <--
        pand(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oor, Arc::new(args), *res)) <--
        por(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        !reg_64(r_str),
        !reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oorimm(imm_int), Arc::new(args), *res)) <--
        por(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oxor, Arc::new(args), *res)) <--
        pxor(address, r, r2),
        if r!=r2,
        op_register(r, r_str),
        op_register(r2, r2_str),
        !reg_64(r_str),
        !reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oxorimm(imm_int), Arc::new(args), *res)) <--
        pxor(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Onot, Arc::new(args), *res)) <--
        pnot(address, r),
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshl, Arc::new(args), *res)) <--
        psal(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshlimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshr, Arc::new(args), *res)) <--
        psar(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrimm(imm_int), Arc::new(args), *res)) <--
        psar(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        // A 32-bit shift masks its count to 5 bits, so an immediate >= 32 can only be a 64-bit shift; suppress the 32-bit candidate so the mulhi product keeps full width instead of truncating to 0.
        if imm_int < 32,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshru, Arc::new(args), *res)) <--
        pshr(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshruimm(imm_int), Arc::new(args), *res)) <--
        pshr(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        // As with Oshrimm: a 32-bit logical shift masks its count to 5 bits, so imm >= 32 is a 64-bit shift and the 32-bit candidate is suppressed.
        if imm_int < 32,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororimm(imm_int), Arc::new(args), *res)) <--
        pror(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororimm(32 - imm_int), Arc::new(args), *res)) <--
        prol(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororlimm(64 - imm_int), Arc::new(args), *res)) <--
        prol(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshldimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, r2),
        op_indirect(_, r, _, r_str, _, n, _),
        let imm_int = *n as i64,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    // A stack-slot address-of with a 64-bit dest is a 64-bit pointer -> Oleal; the previous 32-bit Olea truncated the high bits of the x86-64 stack address.
    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, r_str, index_str, _scale, disp, _),
        reg_sp(*r_str),
        if *index_str == "NONE" || index_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        sp_lea_shift(address, depth),
        let addr = Addressing::Ainstack(disp - depth);

    // RSP plus an index is not a plain stack slot: retain both address inputs
    // so RTL can split the stack base from the indexed arithmetic without
    // fabricating a numeric frame address.
    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        reg_sp(*base_str),
        if *index_str != "NONE" && !index_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![Mreg::SP, *index_arg],
        let addr = if *scale > 1 {
            Addressing::Aindexed2scaled(*scale, *disp)
        } else {
            Addressing::Aindexed2(*disp)
        };

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, r_str, index_str, scale, disp, _),
        !reg_sp(*r_str), !reg_bp(*r_str),
        if *index_str == "NONE" || index_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);


    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale == 1,
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2(*disp);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale > 1,
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2scaled(*scale, *disp);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*index_arg],
        let addr = Addressing::Ascaled(*scale, *disp);

    // 64-bit LEA with a BP base and index when BP is not the frame pointer: without it the index is dropped and a frame-relative &local is fabricated for an argv-indexed pointer.
    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        reg_bp(*base_str),
        instr_in_function(address, func),
        !func_has_frame_pointer(func),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = if *scale > 1 { Addressing::Aindexed2scaled(*scale, *disp) } else { Addressing::Aindexed2(*disp) };

    // Base-only 64-bit LEA on BP when BP is not the frame pointer.  Under
    // -fomit-frame-pointer, gcc's default from -O1 on x86-64, RBP is an ordinary
    // callee-saved register, so `lea disp(%rbp),%r` is arithmetic on whatever
    // pointer it happens to hold and not the address of a frame slot.  The
    // indexed form above already says so; without this base-only twin the same
    // access has no lowering here at all and falls through to the frame reading
    // in rtl, which does not merely mislabel the result -- the frame-slot value
    // identity at that address IS the BP register's value identity, so the
    // register's pointer and whatever really lives at that frame offset are
    // welded into a single variable.
    mach_inst(address, MachInst::Mop(Operation::Oleal(Addressing::Aindexed(*disp)), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, _scale, disp, _),
        reg_bp(*base_str),
        if *index_str == "NONE" || index_str.is_empty(),
        instr_in_function(address, func),
        !func_has_frame_pointer(func),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*base_arg];

    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*ident as usize), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, _offset),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*target_addr as i64), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        !resolved_addr_to_symbol(target_addr, _, _),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);

    // Absolute addressing LEA: lea 0x40402c, %rax (base="NONE", no index, disp is the address)
    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*ident as usize), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, _offset),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*target_addr as i64), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(address, target_addr),
        !resolved_addr_to_symbol(target_addr, _, _),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);


    mach_inst(address, MachInst::Mop(cast_op, Arc::new(args.clone()), *res)) <--
        pmov(address, r, r1),
        !div_consumed(address),
        op_register(r1, r1_str),
        op_register(r, r_str),
        reg_is_64(r1_str, r1_is_64),
        reg_is_64(r_str, r_is_64),
        if r1_is_64 != r_is_64,
        ireg_of(preg_of_r1, Ireg::from(r1_str)),
        preg_of(a1, preg_of_r1),
        ireg_of(preg_of_res, Ireg::from(r_str)),
        preg_of(res, preg_of_res),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let args = vec![*a1],
        let cast_op = if mnem_upper.starts_with("MOVSXD") || mnem_upper.starts_with("CDQE") {
            Operation::Ocast32signed
        } else if !*r1_is_64 && *r_is_64 {
            Operation::Ocast32unsigned
        } else {
            Operation::Olowlong
        };

    mach_inst(address, MachInst::Mop(Operation::Onegl, Arc::new(args), *res)) <--
        pneg(address, r),
        !div_consumed(address),
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];


    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psub(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) };

    mach_inst(address, MachInst::Mop(Operation::Omull, Arc::new(args), *res)) <--
        pimul(address, r, r2),
        !div_consumed(address),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullimm(imm_int), Arc::new(args), *res)) <--
        pimul(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Omullhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX ,*a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX ,*a2];

    // 64-bit signed div: CQO before IDIV -> Odivl (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivl, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CQO", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit unsigned div: xor RDX,RDX before DIV -> Odivlu (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivlu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, rd, rs),
        op_register(rd, rd_str),
        op_register(rs, rs_str),
        if *rd_str == *rs_str,
        if *rd_str == "EDX" || *rd_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit signed mod: CQO before IDIV -> Omodl (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodl, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CQO", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit unsigned mod: xor RDX,RDX before DIV -> Omodlu (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodlu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, rd, rs),
        op_register(rd, rd_str),
        op_register(rs, rs_str),
        if *rd_str == *rs_str,
        if *rd_str == "EDX" || *rd_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: IDIV without CQO predecessor, treat as signed 64-bit
    mach_inst(address, MachInst::Mop(Operation::Odivl, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodl, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: DIV without xor RDX predecessor, treat as unsigned 64-bit
    mach_inst(address, MachInst::Mop(Operation::Odivlu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodlu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandl, Arc::new(args), *res)) <--
        pand(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_64(r_str),
        reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandlimm(imm_int), Arc::new(args), *res)) <--
        pand(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oorl, Arc::new(args), *res)) <--
        por(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_64(r_str),
        reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oorlimm(imm_int), Arc::new(args), *res)) <--
        por(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oxorl, Arc::new(args), *res)) <--
        pxor(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_64(r_str),
        reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oxorlimm(imm_int), Arc::new(args), *res)) <--
        pxor(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    // Bit-test-and-modify immediate forms lower to masked bitwise ops, with the bit index masked to the operand width and the mask built unsigned so bit 63 does not overflow the shift.
    mach_inst(address, MachInst::Mop(Operation::Oxorlimm(mask), Arc::new(args), *res)) <--
        pbtc(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        reg_64(r_str),
        let mask = (1u64 << ((*imm_str as u32) & 63)) as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oxorimm(mask), Arc::new(args), *res)) <--
        pbtc(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        !reg_64(r_str),
        let mask = (1u32 << ((*imm_str as u32) & 31)) as i32 as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oorlimm(mask), Arc::new(args), *res)) <--
        pbts(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        reg_64(r_str),
        let mask = (1u64 << ((*imm_str as u32) & 63)) as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oorimm(mask), Arc::new(args), *res)) <--
        pbts(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        !reg_64(r_str),
        let mask = (1u32 << ((*imm_str as u32) & 31)) as i32 as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oandlimm(mask), Arc::new(args), *res)) <--
        pbtr(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        reg_64(r_str),
        let mask = (!(1u64 << ((*imm_str as u32) & 63))) as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oandimm(mask), Arc::new(args), *res)) <--
        pbtr(address, r, n),
        op_immediate(n, imm_str, _),
        op_register(r, r_str),
        !reg_64(r_str),
        let mask = (!(1u32 << ((*imm_str as u32) & 31))) as i32 as i64,
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Onotl, Arc::new(args), *res)) <--
        pnot(address, r),
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshll, Arc::new(args), *res)) <--
        psal(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshllimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshrl, Arc::new(args), *res)) <--
        psar(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrlimm(imm_int), Arc::new(args), *res)) <--
        psar(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshrlu, Arc::new(args), *res)) <--
        pshr(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrluimm(imm_int), Arc::new(args), *res)) <--
        pshr(address, r, n),
        !div_consumed(address),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororlimm(imm_int), Arc::new(args), *res)) <--
        pror(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    // Mirror of the 64-bit rule: a stack-slot address-of with a 32-bit dest is Olea, since the previous Oleal over-promoted a genuine 32-bit leal result to long.
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, index_str, _scale, disp, _),
        reg_sp(*r_str),
        if *index_str == "NONE" || index_str.is_empty(),
        sp_lea_shift(address, depth),
        let addr = Addressing::Ainstack(disp - depth);

    // Preserve RSP plus index for genuine 32-bit LEA arithmetic as well; the
    // operation width stays Olea while the address inputs mirror the 64-bit
    // form above.
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        reg_sp(*base_str),
        if *index_str != "NONE" && !index_str.is_empty(),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![Mreg::SP, *index_arg],
        let addr = if *scale > 1 {
            Addressing::Aindexed2scaled(*scale, *disp)
        } else {
            Addressing::Aindexed2(*disp)
        };

    // A 32-bit LEA used as integer arithmetic is Olea (Xint), not Oleal: mis-promoting to long breaks a downstream unsigned 32-bit comparison, which then renders as a signed long compare.
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, index_str, scale, disp, _),
        if *index_str == "NONE" || index_str.is_empty(),
        !reg_sp(*r_str), !reg_bp(*r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);

    // A destination-width LEA still reads its base at pointer width.  In a
    // frameless function RBP is an ordinary callee-saved value, so a 32-bit
    // `lea disp(%rbp), %edx` is integer arithmetic on that value rather than a
    // frame address.  This is the 32-bit-result twin of the 64-bit RBP rule.
    mach_inst(address, MachInst::Mop(Operation::Olea(Addressing::Aindexed(*disp)), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, base_str, index_str, _scale, disp, _),
        reg_bp(*base_str),
        if *index_str == "NONE" || index_str.is_empty(),
        instr_in_function(address, func),
        !func_has_frame_pointer(func),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*base_arg];

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        padd(nextaddress, r_same, delta),
        next(address, nextaddress),
        op_register(r, res_str),
        op_register(r_same, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, _, scale, disp, _),
        reg_sp(*r_str),
        sp_lea_shift(address, depth),
        let addr = Addressing::Ainstack(disp - depth);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        padd(nextaddress, r_same, delta),
        next(address, nextaddress),
        op_register(r, res_str),
        op_register(r_same, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, index_str, scale, disp, _),
        if *index_str == "NONE" || index_str.is_empty(),
        !reg_sp(*r_str), !reg_bp(*r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);

    // 32-bit LEA with base + index (scale=1) -> Olea(Aindexed2)
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale == 1,
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2(*disp);

    // 32-bit LEA with base + index (scale>1) -> Olea(Aindexed2scaled)
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale > 1,
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2scaled(*scale, *disp);

    // 32-bit LEA with no base, just index -> Olea(Ascaled)
    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*index_arg],
        let addr = Addressing::Ascaled(*scale, *disp);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        ppxor(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::x86(r_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        pxorpd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::x86(r_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        pxorps(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::x86(r_str);

    // PCMPEQx xmm,xmm is the canonical packed all-ones idiom.  Its low
    // quadword is exactly the scalar -1 represented by the ordinary XMM Mach
    // pseudo; the high quadword travels through xmm_hi_seed kind 5 above.
    mach_inst(*address, MachInst::Mop(Operation::Olongconst(-1), Arc::new(vec![]), res)) <--
        instruction(address, _, _, mnem, src, dst, _, _, _, _),
        if simd_self_all_ones_mnem(mnem),
        op_register(src, src_str),
        op_register(dst, dst_str),
        if src_str == dst_str,
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str);

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), res)) <--
        pmovsd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_xmm(arg_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(addr, MachInst::Mload(MemoryChunk::MFloat64, addressing, Arc::new(args), dst)) <--
        pmovsd(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        reg_xmm(dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MFloat64, addressing, Arc::new(args), src)) <--
        pmovsd(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(address, MachInst::Mop(Operation::Ofloatoflong, Arc::new(args), res)) <--
        pcvtsi2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_64(arg_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ofloatofint, Arc::new(args), res)) <--
        pcvtsi2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_is_64(arg_str, false),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Olongoffloat, Arc::new(args), res)) <--
        pcvtsd2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_64(res_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ointoffloat, Arc::new(args), res)) <--
        pcvtsd2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_is_64(res_str, false),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Oaddf, Arc::new(args), res)) <--
        paddsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubf, Arc::new(args), res)) <--
        psubsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulf, Arc::new(args), res)) <--
        pmulsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivf, Arc::new(args), res)) <--
        pdivsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];


    mach_inst(address, MachInst::Mop(Operation::Oaddfs, Arc::new(args), res)) <--
        paddss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubfs, Arc::new(args), res)) <--
        psubss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulfs, Arc::new(args), res)) <--
        pmulss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivfs, Arc::new(args), res)) <--
        pdivss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];


    mach_inst(address, MachInst::Mop(Operation::Oaddf, Arc::new(args), res)) <--
        instruction(address, _, _, "VADDSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubf, Arc::new(args), res)) <--
        instruction(address, _, _, "VSUBSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulf, Arc::new(args), res)) <--
        instruction(address, _, _, "VMULSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivf, Arc::new(args), res)) <--
        instruction(address, _, _, "VDIVSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Oaddfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VADDSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VSUBSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VMULSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VDIVSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::x86(dst_str),
        let a1 = Mreg::x86(src1_str),
        let a2 = Mreg::x86(src2_str),
        let args = vec![a1, a2];


    mach_inst(address, MachInst::Mop(Operation::Osingleoffloat, Arc::new(args), res)) <--
        pcvtsd2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ofloatofsingle, Arc::new(args), res)) <--
        pcvtss2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];


    // A float/SSE op with a MEMORY source matches no reg-reg rule and would be dropped entirely, so capture it as a fused load+op lowered in rtl_pass; BP/SP and RIP bases are excluded.
    relation float_mem_op_raw(Address, Operation, MemoryChunk, Symbol, Mreg, bool);

    float_mem_op_raw(addr, Operation::Oaddfs, MemoryChunk::MFloat32, *src, Mreg::x86(d), false) <--
        paddss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Osubfs, MemoryChunk::MFloat32, *src, Mreg::x86(d), false) <--
        psubss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Omulfs, MemoryChunk::MFloat32, *src, Mreg::x86(d), false) <--
        pmulss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Odivfs, MemoryChunk::MFloat32, *src, Mreg::x86(d), false) <--
        pdivss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Oaddf, MemoryChunk::MFloat64, *src, Mreg::x86(d), false) <--
        paddsd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Osubf, MemoryChunk::MFloat64, *src, Mreg::x86(d), false) <--
        psubsd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Omulf, MemoryChunk::MFloat64, *src, Mreg::x86(d), false) <--
        pmulsd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Odivf, MemoryChunk::MFloat64, *src, Mreg::x86(d), false) <--
        pdivsd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Ofloatofsingle, MemoryChunk::MFloat32, *src, Mreg::x86(d), true) <--
        pcvtss2sd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);
    float_mem_op_raw(addr, Operation::Osingleoffloat, MemoryChunk::MFloat64, *src, Mreg::x86(d), true) <--
        pcvtsd2ss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _);

    relation float_load_op(Address, Operation, MemoryChunk, Addressing, Arc<Vec<Mreg>>, Mreg, bool);

    float_load_op(*addr, op.clone(), *chunk, addressing, Arc::new(args), *dst, *is_unary) <--
        float_mem_op_raw(addr, op, chunk, src, dst, is_unary),
        op_indirect(src, _, base_str, idx_str, scale, disp, _),
        if *base_str != "NONE" && !base_str.is_empty(),
        if Mreg::x86(base_str) != Mreg::BP && Mreg::x86(base_str) != Mreg::SP,
        !reg_ip(base_str),
        let has_idx = *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode {
            base: Some(Ireg::from(base_str)),
            index: if has_idx { Some((Ireg::from(idx_str), *scale)) } else { None },
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    // RIP-relative float source (3.8a): dominant PIE shape for float constants; previously excluded so the op vanished entirely (function collapsed to `return 0`); resolved to synthesized global symbol via Aglobal.
    float_load_op(*addr, op.clone(), *chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), *dst, *is_unary) <--
        float_mem_op_raw(addr, op, chunk, src, dst, is_unary),
        op_indirect(src, _, base_str, idx_str, _, _, _),
        reg_ip(*base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    // Absolute-addressed source (clang -fno-pie constant pool): base="NONE", disp is the address.
    float_load_op(*addr, op.clone(), *chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), *dst, *is_unary) <--
        float_mem_op_raw(addr, op, chunk, src, dst, is_unary),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);


    // cvtsi2ss/sd with a MEMORY source matches no register-source rule and would be dropped, so capture it as a unary conversion whose integer source width comes from the memory operand size.
    relation cvtsi2_mem_raw(Address, Operation, MemoryChunk, Symbol, Mreg);

    cvtsi2_mem_raw(addr, op, chunk, *src, Mreg::x86(d)) <--
        pcvtsi2sd(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _),
        op_indirect(src, _, _, _, _, _, sz),
        let (op, chunk) = if *sz == 8 { (Operation::Ofloatoflong, MemoryChunk::MInt64) }
                          else { (Operation::Ofloatofint, MemoryChunk::MInt32) };
    cvtsi2_mem_raw(addr, op, chunk, *src, Mreg::x86(d)) <--
        pcvtsi2ss(addr, dsym, src), op_register(dsym, d), reg_xmm(d), !op_register(src, _),
        op_indirect(src, _, _, _, _, _, sz),
        let (op, chunk) = if *sz == 8 { (Operation::Osingleoflong, MemoryChunk::MInt64) }
                          else { (Operation::Osingleofint, MemoryChunk::MInt32) };

    // Register-base and indexed source reuse float_load_op's chunk-agnostic unary load+op lowering; BP/SP and RIP are excluded here exactly as in the float_mem_op_raw derivation.
    float_load_op(*addr, op.clone(), *chunk, addressing, Arc::new(args), *dst, true) <--
        cvtsi2_mem_raw(addr, op, chunk, src, dst),
        op_indirect(src, _, base_str, idx_str, scale, disp, _),
        if *base_str != "NONE" && !base_str.is_empty(),
        if Mreg::x86(base_str) != Mreg::BP && Mreg::x86(base_str) != Mreg::SP,
        !reg_ip(base_str),
        let has_idx = *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode {
            base: Some(Ireg::from(base_str)),
            index: if has_idx { Some((Ireg::from(idx_str), *scale)) } else { None },
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    // RIP-relative integer source (a PIE int constant in .rodata) resolves to a global symbol like the float RIP path; it was previously excluded and the conversion vanished.
    float_load_op(*addr, op.clone(), *chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), *dst, true) <--
        cvtsi2_mem_raw(addr, op, chunk, src, dst),
        op_indirect(src, _, base_str, idx_str, _, _, _),
        reg_ip(*base_str),
        if *idx_str == "NONE" || idx_str.is_empty(),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    // A BP/SP-relative SCALAR stack slot must be read through the slot-variable model, not a raw Iload that would re-materialize it as *(&local + k); an indexed access is a stack array.
    relation cvtsi2_stack_op(Address, Operation, Mreg, i64, Mreg);
    cvtsi2_stack_op(*addr, op.clone(), Mreg::x86(base_str), *disp, *dst) <--
        cvtsi2_mem_raw(addr, op, _chunk, src, dst),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::BP || Mreg::x86(base_str) == Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty();

    // BINARY float arith reading a spilled float SCALAR slot, which float_load_op excludes: read it through the slot's canonical SSA reg as a binary in-RMW op; scalar slots only.
    relation float_arith_stack_op(Address, Operation, Mreg, i64, Mreg);
    float_arith_stack_op(*addr, op.clone(), Mreg::x86(base_str), *disp, *dst) <--
        float_mem_op_raw(addr, op, _chunk, src, dst, false),
        op_indirect(src, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::BP || Mreg::x86(base_str) == Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty();

    mach_inst(address, MachInst::Mop(Operation::Osingleofint, Arc::new(args), res)) <--
        pcvtsi2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_is_64(arg_str, false),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Osingleoflong, Arc::new(args), res)) <--
        pcvtsi2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_64(arg_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ointofsingle, Arc::new(args), res)) <--
        pcvtss2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_is_64(res_str, false),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Olongofsingle, Arc::new(args), res)) <--
        pcvtss2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_64(res_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];


    mach_inst(address, MachInst::Mop(Operation::Onegf, Arc::new(args), res)) <--
        pxorpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Oabsf, Arc::new(args), res)) <--
        pandpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Onegfs, Arc::new(args), res)) <--
        pxorps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Oabsfs, Arc::new(args), res)) <--
        pandps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    // Reg-reg fabs/fabsf: recovered from positive evidence that the loaded constant is the IEEE-754 sign-clear mask plus a structural CFG reaching-def proving the mask register still holds it.

    // A scalar move loading a 4-/8-byte sign-clear mask from RIP-relative .rodata into an XMM register; GCC also uses MOVQ for the 64-bit bit pattern, and the XMM-destination guard distinguishes it from an integer move.
    relation mask_load(Address, Mreg, usize);
    mask_load(load_addr, dst_reg, 4) <--
        instruction(load_addr, _, _, mnem, _, dst, _, _, _, _),
        if *mnem == "MOVSS" || *mnem == "VMOVSS",
        op_register(dst, dst_str),
        reg_xmm(dst_str),
        rip_target_addr(load_addr, target),
        fp_sign_clear_mask(target, 4),
        let dst_reg = Mreg::x86(dst_str);
    mask_load(load_addr, dst_reg, 8) <--
        instruction(load_addr, _, _, mnem, _, dst, _, _, _, _),
        if matches!(*mnem, "MOVSD" | "VMOVSD" | "MOVQ" | "VMOVQ"),
        op_register(dst, dst_str),
        reg_xmm(dst_str),
        rip_target_addr(load_addr, target),
        fp_sign_clear_mask(target, 8),
        let dst_reg = Mreg::x86(dst_str);

    // Reaching-def lattice for the mask register as monotone CFG propagation: defined at the load, flowing over next edges, killed by any reg_def; structural, never an address comparison.
    relation mask_reg_in(Address, Mreg, usize);
    relation mask_reg_out(Address, Mreg, usize);
    mask_reg_out(load_addr, reg, w) <-- mask_load(load_addr, reg, w);
    mask_reg_in(succ, reg, w) <--
        mask_reg_out(addr, reg, w),
        next(addr, succ);
    mask_reg_out(addr, reg, w) <--
        mask_reg_in(addr, reg, w),
        !reg_def(addr, reg);

    // andps/andpd where the mask register provably holds the sign-clear mask IS fabsf/fabs; r is the accumulator and r2 the mask register, matched by width.
    mach_inst(address, MachInst::Mop(Operation::Oabsfs, Arc::new(args), res)) <--
        pandps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_register(r2, r2_str),
        reg_xmm(r2_str),
        let mask_reg = Mreg::x86(r2_str),
        mask_reg_in(address, mask_reg, 4),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Oabsf, Arc::new(args), res)) <--
        pandpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_register(r2, r2_str),
        reg_xmm(r2_str),
        let mask_reg = Mreg::x86(r2_str),
        mask_reg_in(address, mask_reg, 8),
        let res = Mreg::x86(r_str),
        let args = vec![res];

    // ANDPS/ANDPD is commutative, so gcc may put the mask in the DESTINATION register; without this symmetric form the andps is dropped and the value subtree is DCE'd.
    mach_inst(address, MachInst::Mop(Operation::Oabsfs, Arc::new(args), res)) <--
        pandps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_register(r2, r2_str),
        reg_xmm(r2_str),
        let mask_reg = Mreg::x86(r_str),
        mask_reg_in(address, mask_reg, 4),
        let res = Mreg::x86(r_str),
        let value = Mreg::x86(r2_str),
        let args = vec![value];

    mach_inst(address, MachInst::Mop(Operation::Oabsf, Arc::new(args), res)) <--
        pandpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_register(r2, r2_str),
        reg_xmm(r2_str),
        let mask_reg = Mreg::x86(r_str),
        mask_reg_in(address, mask_reg, 8),
        let res = Mreg::x86(r_str),
        let value = Mreg::x86(r2_str),
        let args = vec![value];


    mach_inst(address, MachInst::Mop(Operation::Omaxf, Arc::new(args), res)) <--
        pmaxsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Ominf, Arc::new(args), res)) <--
        pminsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::x86(r_str),
        let a2 = Mreg::x86(r2_str),
        let args = vec![res, a2];


    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cgt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondA, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cge), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondAe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Clt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondB, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cle), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondBe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cnotcompf(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cgt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondA, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cge), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondAe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Clt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondB, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cle), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondBe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cnotcompfs(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);

    // comiss with a RIP-relative operand loads the constant into FP0 (x87 ST0, safe scratch); fp0_loaded_at records it so a synthetic reg_def connects the load to the consumer's reg_use.
    #[local] relation fp0_loaded_at(Address);

    reg_def(addr0, Mreg::FP0) <-- fp0_loaded_at(addr0);

    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat32, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomiss(addr0, _r1, r2),
        op_indirect(r2, _, base_str, _, _, _, _),
        reg_ip(*base_str),
        rip_target_addr(addr0, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat64, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomisd(addr0, _r1, r2),
        op_indirect(r2, _, base_str, _, _, _, _),
        reg_ip(*base_str),
        rip_target_addr(addr0, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    // comiss/ucomiss with absolute addressing memory operand
    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat32, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomiss(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr0, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat64, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomisd(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if *base_str == "NONE" || base_str.is_empty(),
        if *idx_str == "NONE" || idx_str.is_empty(),
        if *disp > 0,
        abs_target_addr(addr0, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset);

    // Register-base memory operand for comisd/ucomiss: loads into FP0, mirroring RIP/absolute paths; BP/SP excluded per slot-variable model.
    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat32, addressing, Arc::new(args), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomiss(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, scale, disp, _),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        if Mreg::x86(base_str) != Mreg::BP && Mreg::x86(base_str) != Mreg::SP,
        let has_idx = *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode {
            base: Some(Ireg::from(base_str)),
            index: if has_idx { Some((Ireg::from(idx_str), *scale)) } else { None },
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(addr0, MachInst::Mload(MemoryChunk::MFloat64, addressing, Arc::new(args), Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomisd(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, scale, disp, _),
        if *base_str != "NONE" && !base_str.is_empty(),
        !reg_ip(base_str),
        if Mreg::x86(base_str) != Mreg::BP && Mreg::x86(base_str) != Mreg::SP,
        let has_idx = *idx_str != "NONE" && !idx_str.is_empty(),
        let addrmode = Addrmode {
            base: Some(Ireg::from(base_str)),
            index: if has_idx { Some((Ireg::from(idx_str), *scale)) } else { None },
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    // BP-relative float compare operand: read the spilled slot into FP0 via Mgetstack, the same slot-variable path every other BP/SP float access uses; scalar slots only.
    mach_inst(addr0, MachInst::Mgetstack(*disp, Typ::Tsingle, Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomiss(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty();

    mach_inst(addr0, MachInst::Mgetstack(*disp, Typ::Tfloat, Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomisd(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::BP,
        if *idx_str == "NONE" || idx_str.is_empty();

    // SP-relative variant of the BP slot-load, for -O2/-O3 frame-pointer-less float spills, using the raw-disp RSP convention guarded by stack_offset; scalar slots only.
    mach_inst(addr0, MachInst::Mgetstack(disp - depth, Typ::Tsingle, Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomiss(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        sp_frame_shift(addr0, depth);

    mach_inst(addr0, MachInst::Mgetstack(disp - depth, Typ::Tfloat, Mreg::FP0)),
    fp0_loaded_at(*addr0) <--
        pucomisd(addr0, _r1, r2),
        op_indirect(r2, _, base_str, idx_str, _, disp, _),
        if Mreg::x86(base_str) == Mreg::SP,
        if *idx_str == "NONE" || idx_str.is_empty(),
        sp_frame_shift(addr0, depth);

    // pucomiss/pucomisd with a memory operand: (compare addr, is_double, register operand).
    #[local] relation fcmp_mem_arg(Address, bool, Mreg);
    fcmp_mem_arg(addr0, false, Mreg::x86(r1_str)) <--
        pucomiss(addr0, r1, r2), op_register(r1, r1_str), !op_register(r2, _), reg_xmm(r1_str);
    fcmp_mem_arg(addr0, true, Mreg::x86(r1_str)) <--
        pucomisd(addr0, r1, r2), op_register(r1, r1_str), !op_register(r2, _), reg_xmm(r1_str);

    // Mem-operand float compare + jcc relocated to the jcc's address (CF-5c): the FP0 Mload occupies the compare's address and the candidate pick would drop an Mcond keyed there.
    mach_inst(addr1, MachInst::Mcond(condition.clone(), Arc::new(vec![*arg1, Mreg::FP0]), lbl)),
    mcond_at_jcc(*addr1),
    reg_use(*addr1, *arg1),
    reg_use(*addr1, Mreg::FP0) <--
        fcmp_mem_arg(addr0, is_double, arg1),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, *is_double);

    // Two-branch JP+JNE float != with a MEMORY operand: mirror the register rule but read the loaded FP0, keyed at the JNE, gated on fp0_loaded_at so FP0 is defined before the read.
    mach_inst(addr2, MachInst::Mcond(Condition::Cnotcompfs(Comparison::Ceq), Arc::new(vec![*arg1, Mreg::FP0]), lbl)),
    mcond_at_jcc(*addr2),
    reg_use(*addr2, *arg1),
    reg_use(*addr2, Mreg::FP0) <--
        fcmp_mem_arg(addr0, false, arg1),
        fp0_loaded_at(*addr0),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, _lbl_p),
        direct_jump(addr1, tgt),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl),
        direct_jump(addr2, tgt);

    mach_inst(addr2, MachInst::Mcond(Condition::Cnotcompf(Comparison::Ceq), Arc::new(vec![*arg1, Mreg::FP0]), lbl)),
    mcond_at_jcc(*addr2),
    reg_use(*addr2, *arg1),
    reg_use(*addr2, Mreg::FP0) <--
        fcmp_mem_arg(addr0, true, arg1),
        fp0_loaded_at(*addr0),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, _lbl_p),
        direct_jump(addr1, tgt),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl),
        direct_jump(addr2, tgt);

    // GCC materializes ordered float equality as setnp; movzx; zero; cmovne.
    // The final value is one exactly when the comparison is ordered and equal.
    mach_inst(cmov, MachInst::Mop(
        operation,
        Arc::new(vec![*arg1, Mreg::FP0]),
        result
    )),
    reg_use(*cmov, *arg1),
    reg_use(*cmov, Mreg::FP0) <--
        fcmp_mem_arg(cmp, is_double, arg1),
        fp0_loaded_at(*cmp),
        next(cmp, set_ordered),
        psetcc(set_ordered, TestCond::CondNp, set_dst),
        op_register(set_dst, set_dst_name),
        next(set_ordered, extend),
        instruction(extend, _, _, "MOVZX", extend_src, extend_dst, _, _, _, _),
        op_register(extend_src, extend_src_name),
        op_register(extend_dst, extend_dst_name),
        if Mreg::x86(extend_src_name) == Mreg::x86(set_dst_name),
        next(extend, zero),
        instruction(zero, _, _, "MOV", zero_imm, zero_dst, _, _, _, _),
        op_immediate(zero_imm, zero_value, _),
        if *zero_value == 0,
        op_register(zero_dst, zero_dst_name),
        next(zero, cmov),
        pcmov(cmov, TestCond::CondNe, cmov_dst, cmov_src),
        op_register(cmov_dst, cmov_dst_name),
        op_register(cmov_src, cmov_src_name),
        if Mreg::x86(cmov_dst_name) == Mreg::x86(extend_dst_name),
        if Mreg::x86(cmov_src_name) == Mreg::x86(zero_dst_name),
        let result = Mreg::x86(cmov_dst_name),
        let condition = if *is_double {
            Condition::Ccompf(Comparison::Ceq)
        } else {
            Condition::Ccompfs(Comparison::Ceq)
        },
        let operation = Operation::Ocmp(condition);

    // Float compare feeding SETcc (3.8b): had no fcmp->setcc link so neither instruction lifted (function collapsed to `return 0`); mirrors cmp_setcc_link to produce Mop(Ocmp(Ccompf*/Cnotcompf*)) writing the setcc destination.
    #[local] relation fcmp_setcc_link(Address, Address);
    fcmp_setcc_link(addr0, addr1) <--
        pucomisd(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    fcmp_setcc_link(addr0, addr1) <--
        pucomiss(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);

    setcc_materialized_value(
        addr_set,
        addr0,
        Operation::Ocmp(condition.clone()),
        Arc::new(vec![arg1, arg2])
    ) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, true);

    setcc_materialized_value(
        addr_set,
        addr0,
        Operation::Ocmp(condition.clone()),
        Arc::new(vec![arg1, arg2])
    ) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, false);

    setcc_materialized_value(
        addr_set,
        addr0,
        Operation::Ocmp(condition.clone()),
        Arc::new(vec![*arg1, Mreg::FP0])
    ) <--
        fcmp_mem_arg(addr0, is_double, arg1),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, _),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, *is_double);

    // Reg-reg Ocmp keyed at compare's address: int cmp_setcc design parity; setcc node bridges via linear's branch-to-next default.
    mach_inst(addr0, MachInst::Mop(Operation::Ocmp(condition.clone()), Arc::new(vec![arg1, arg2]), *dst_mreg)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, true);

    mach_inst(addr0, MachInst::Mop(Operation::Ocmp(condition.clone()), Arc::new(vec![arg1, arg2]), *dst_mreg)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::x86(r1_str),
        let arg2 = Mreg::x86(r2_str),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, false);

    // Mem-operand Ocmp keyed at SETcc's address: FP0 Mload occupies compare's address causing the same single-instruction-per-node collision as the relocated Mcond.
    mach_inst(addr_set, MachInst::Mop(Operation::Ocmp(condition.clone()), Arc::new(vec![*arg1, Mreg::FP0]), *dst_mreg)),
    reg_use(*addr_set, *arg1),
    reg_use(*addr_set, Mreg::FP0) <--
        fcmp_mem_arg(addr0, is_double, arg1),
        fcmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        if let Some(condition) = fcmp_setcc_condition(*test_cond, *is_double);


    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), res)) <--
        pmovss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_xmm(arg_str),
        let res = Mreg::x86(res_str),
        let arg = Mreg::x86(arg_str),
        let args = vec![arg];

    mach_inst(addr, MachInst::Mload(MemoryChunk::MFloat32, addressing, Arc::new(args), dst)) <--
        pmovss(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        reg_xmm(dst_str),
        let dst = Mreg::x86(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MFloat32, addressing, Arc::new(args), src)) <--
        pmovss(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::x86(src_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::x86(r2) != Mreg::BP && Mreg::x86(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    expand_builtin_inline(addr, bswap_name, Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))]), BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))) <--
        pswap(addr, res),
        op_register(res, r_str),
        let bswap_name = bswap_builtin_for_reg(r_str);

    #[local] relation pbsr_forward(Address, Address, Address, Symbol, Symbol, Mreg);
    pbsr_forward(*addr, *successor, *block, *res, *a1, result_reg) <--
        pbsr(addr, res, a1),
        code_in_block(addr, block),
        op_register(res, result_name),
        let result_reg = Mreg::x86(*result_name),
        next(addr, successor),
        code_in_block(successor, block);

    pbsr_forward(*addr, *successor, *block, *res, *a1, *result_reg) <--
        pbsr_forward(addr, current, block, res, a1, result_reg),
        flags_flow_transparent(current),
        !reg_def(current, *result_reg),
        !reg_use(current, *result_reg),
        next(current, successor),
        code_in_block(successor, block);

    #[local] relation pbsr_xor_mask(Address, Symbol, Symbol, i64);
    pbsr_xor_mask(*addr, *res, *a1, *imm) <--
        pbsr_forward(addr, xor_addr, _, res, a1, result_reg),
        pxor(xor_addr, xor_result, n),
        op_register(xor_result, xor_result_name),
        if Mreg::x86(*xor_result_name) == *result_reg,
        op_immediate(n, imm, _);

    expand_builtin_inline(
        addr,
        bswap_name,
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pmov(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pswap(addr1, res),
        next(addr, addr1),
        if a1 != res,
        let bswap_name = bswap_builtin_for_reg(a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_clz",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsr_xor_mask(addr, res, a1, imm_str),
        op_register(res, r_str),
        op_register(a1, a1_str),
        if *imm_str == 31;

    expand_builtin_inline(
        addr,
        "__builtin_clzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsr_xor_mask(addr, res, a1, imm_str),
        op_register(res, r_str),
        op_register(a1, a1_str),
        if *imm_str == 31;

    expand_builtin_inline(
        addr,
        "__builtin_clzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsr_xor_mask(addr, res, a1, imm_str),
        op_register(res, r_str),
        op_register(a1, a1_str),
        if *imm_str == 63;

    expand_builtin_inline(
        addr,
        "__builtin_clzll",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsr_xor_mask(addr, res, a1, imm_str),
        op_register(res, r_str),
        op_register(a1, a1_str),
        if *imm_str == 63;

    expand_builtin_inline(
        addr,
        "__builtin_ctz",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzll",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzll",
        Arc::new(vec![
            BuiltinArg::BA(Mreg::x86(Ireg::from(ah))),
            BuiltinArg::BA(Mreg::x86(Ireg::from(al)))
        ]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        ptest(addr, al, *al),
        op_register(ah, ah_str),
        op_register(al, al_str),
        next(addr, addr1),
        pjcc(addr1, TestCond::CondE, lbl1),
        next(addr1, addr2),
        pbsf(addr2, res, al),
        op_register(res, res_str),
        next(addr2, addr3),
        pjmp(addr3, lbl2),
        next(addr3, addr4),
        plabel(addr4, lbl1),
        next(addr4, addr5),
        next(addr5, addr6),
        next(addr6, addr7),
        pbsf(addr5, res, ah),
        padd(addr6, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 32,
        plabel(addr7, lbl2);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrt(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrt(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrtsd(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrtsd(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrtss(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(a1_str)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(res_str)))
    ) <--
        psqrtss(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr1,
        "__builtin_negl",
        Arc::new(vec![
            BuiltinArg::BA(Mreg::x86(Ireg::from(ah_str))),
            BuiltinArg::BA(Mreg::x86(Ireg::from(al_str)))
        ]),
        BuiltinArg::BA(Mreg::x86(Ireg::from(rh_str)))
    ) <--
        pneg(addr1, rl),
        next(addr1, addr2),
        padc(addr2, rh, _),
        next(addr2, addr3),
        pneg(addr3, rh),
        op_register(rh, rh_str),
        op_register(rl, rl_str),
        op_register(ah, ah_str),
        op_register(al, al_str);


    expand_builtin_inline(
        addr,
        "__builtin_va_start",
        Arc::new(vec![BuiltinArg::BA(Mreg::x86(Ireg::from(*a)))]),
        BuiltinArg::BA(Mreg::x86(Ireg::Unknown))
    ) <--
        expand_builtin_va_start_32(addr, a);

    expand_builtin_va_start_32(addr1, Ireg::from(reg2)) <--
        plea(addr1, rax, mem_addr),
        op_register(rax, "RAX"),
        op_indirect(mem_addr, "RSP", _, _, 1, ofs, _ ),
        next(addr1, addr2),
        pmov(addr2, r, rax),
        op_indirect(r, reg1, reg2, reg3, scale, disp, _),
        op_register(rax, "RAX");

    mach_inst(addr, MachInst::Mbuiltin((*name).to_string(), args.to_vec(), (*res).clone())) <--
        expand_builtin_inline(addr, name, args, res),
        builtins(*name);

    mach_inst(addr, MachInst::Mlabel((*lbl).to_string())) <--
        symbols(addr, lbl, _);


    pallocframe(addr, sz) <--
        psub(addr, rsp_sym, sz_sym),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz_sym, sz, _);

    stack_delta(addr, -(*sz as i64)) <--
        psub(addr, rsp_sym, sz_sym),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz_sym, sz, _);

    // Clang stack alignment: push of scratch register at function entry instead of sub $8, %rsp
    #[local] relation push_align_alloc(Symbol, Address, i64);

    push_align_alloc(func_name, start_addr, 8) <--
        func_span(func_name, start_addr, end_addr),
        ppush(start_addr, sym),
        op_register(sym, reg_str),
        !is_callee_saved(Mreg::x86(*reg_str)),
        !reg_sp(reg_str);

    push_align_alloc(func_name, push_addr, 8) <--
        func_span(func_name, start_addr, end_addr),
        next(start_addr, push_addr),
        if push_addr < end_addr,
        ppush(push_addr, sym),
        op_register(sym, reg_str),
        !is_callee_saved(Mreg::x86(*reg_str)),
        !reg_sp(reg_str);

    push_align_alloc(func_name, push_addr, 8) <--
        func_span(func_name, start_addr, end_addr),
        next(start_addr, mid_addr),
        next(mid_addr, push_addr),
        if push_addr < end_addr,
        ppush(push_addr, sym),
        op_register(sym, reg_str),
        !is_callee_saved(Mreg::x86(*reg_str)),
        !reg_sp(reg_str);

    stack_delta(addr, *sz_val as i64) <--
        padd(addr, rsp_sym, sz_sym),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz_sym, sz_val, _);

    stack_offset(func_start, addr, Dual(Set::singleton(0))) <--
        instruction(addr, _, _, "LEAVE", src, dst, _, _, _, _),
        instr_in_function(addr, func_start),
        next(prevaddr, addr),
        stack_offset(func_start, prevaddr, prev_offsets),
        if exact_stack_offset(&prev_offsets.0) == Some(0);


    pallocframe_by_func(func_name, alloc_address, stack_size) <--
        func_span(func_name, start_addr, end_addr),
        pallocframe(alloc_address, stack_size),
        if alloc_address >= start_addr,
        if alloc_address < end_addr;

    func_stacksz(start_addr, end_addr, *func_name, stack_size_u64) <--
        func_span(func_name, start_addr, end_addr),
        agg stack_size = aggregators::sum(sz) in pallocframe_by_func(func_name, _, sz),
        let stack_size_u64 = stack_size.max(0) as u64;

    // Functions with no sub RSP but with alignment pushes: use push-based stack size
    func_stacksz(start_addr, end_addr, *func_name, push_size_u64) <--
        func_span(func_name, start_addr, end_addr),
        !pallocframe_by_func(func_name, _, _),
        agg push_size = aggregators::sum(sz) in push_align_alloc(func_name, _, sz),
        let push_size_u64 = push_size.max(0) as u64;

    // Functions with no sub RSP and no alignment pushes: zero stack size
    func_stacksz(start_addr, end_addr, *func_name, 0u64) <--
        func_span(func_name, start_addr, end_addr),
        !pallocframe_by_func(func_name, _, _),
        !push_align_alloc(func_name, _, _);


    relation is_arg_reg(Mreg);

    // Emit signed+unsigned chunk variants for byte/word; type inference narrows later

    // Load: byte signedness variants
    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt8Signed, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt8Unsigned, addressing, args, dst));

    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt8Unsigned, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt8Signed, addressing, args, dst));

    // Load: word signedness variants
    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt16Signed, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt16Unsigned, addressing, args, dst));

    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt16Unsigned, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt16Signed, addressing, args, dst));

    // Store: byte signedness variants
    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt8Signed, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt8Unsigned, addressing, args, src));

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt8Unsigned, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt8Signed, addressing, args, src));

    // Store: word signedness variants
    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt16Signed, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt16Unsigned, addressing, args, src));

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt16Unsigned, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt16Signed, addressing, args, src));

    // Diagnostic safety net: an instruction with a capstone reg_def but no lowering still KILLS the def it overwrote in the reaching-def lattice, so collect such sites for the wrapper to warn about.
    relation unhandled_reg_def_site(Address, &'static str);
    unhandled_reg_def_site(addr, mnemonic) <--
        reg_def(addr, _),
        unrefinedinstruction(addr, _, mnemonic, _, _, _, _, _, _, _),
        !mach_inst(addr, _),
        !trim_instruction(addr),
        // SETcc's Ocmp is correctly keyed at the fused CMP's address, so its own address legitimately has a reg_def and no mach_inst; exclude it so the diagnostic only fires for an unlowered mnemonic.
        !psetcc(addr, _, _);

}

// TRACE_FUNC diagnostic for the exact SIMD matcher/dataflow/finalizer
// boundary.  Local Ascent relations are otherwise swapped out with the pass
// and invisible to the pipeline-wide trace, which made a rejected chain look
// identical to a matcher that never fired.  Sorting keeps diagnostic output
// deterministic and this function never mutates the program.
fn trace_simd_dword_state(prog: &AsmPassProgram, func: Address, phase: &str) {
    let in_func = |node: Address| {
        prog.instr_in_function
            .iter()
            .any(|(candidate, owner)| *candidate == node && *owner == func)
    };
    let mut seeds: Vec<_> = prog
        .simd_dword_global_seed
        .iter()
        .filter(|(node, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut binops: Vec<_> = prog
        .simd_dword_mem_binop
        .iter()
        .filter(|(node, _, _, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut spills: Vec<_> = prog
        .simd_dword_frame_spill_site
        .iter()
        .filter(|(node, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut candidates: Vec<_> = prog
        .simd_dword_event_candidate
        .iter()
        .filter(|(node, _, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut uncertain_events: Vec<_> = prog
        .simd_dword_event_uncertain
        .iter()
        .filter(|(node,)| in_func(*node))
        .copied()
        .collect();
    let mut store_candidates: Vec<_> = prog
        .simd_dword_frame_store_candidate
        .iter()
        .filter(|(node, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut uncertain_stores: Vec<_> = prog
        .simd_dword_frame_store_uncertain
        .iter()
        .filter(|(node,)| in_func(*node))
        .copied()
        .collect();
    let mut uses: Vec<_> = prog
        .simd_dword_event_use
        .iter()
        .filter(|(node, _)| in_func(*node))
        .copied()
        .collect();
    let mut accepted_events: Vec<_> = prog
        .simd_dword_lane_event
        .iter()
        .filter(|(node, _, _, _)| in_func(*node))
        .copied()
        .collect();
    let mut accepted_stores: Vec<_> = prog
        .simd_dword_lane_frame_store
        .iter()
        .filter(|(node, _, _)| in_func(*node))
        .copied()
        .collect();
    seeds.sort();
    binops.sort();
    spills.sort();
    candidates.sort();
    uncertain_events.sort();
    store_candidates.sort();
    uncertain_stores.sort();
    uses.sort();
    accepted_events.sort();
    accepted_stores.sort();
    eprintln!(
        "[simd-dword:{phase}] func={func:#x} gp-proven={} gp-unproven={} seeds={seeds:?} binops={binops:?} spills={spills:?} candidates={candidates:?} uncertain-events={uncertain_events:?} store-candidates={store_candidates:?} uncertain-stores={uncertain_stores:?} uses={uses:?} accepted-events={accepted_events:?} accepted-stores={accepted_stores:?}",
        prog.simd_gp_return_proven.iter().any(|fact| *fact == (func,)),
        prog.simd_gp_return_unproven.iter().any(|fact| *fact == (func,)),
    );
}

// Relations projected from an improving Ascent lattice may retain transient
// states observed before the fixpoint settles.  Publish only chains for which
// every event has one unique predecessor/value and the exact 16-byte operand
// base is symbol-addressable.  The instruction width itself proves that lanes
// 1..3 are base+{4,8,12}; requiring independent symbol facts for those interior
// addresses would reject ordinary anonymous constant tables, for which only
// the RIP target has a symbol identity.  Walking predecessor links is value
// provenance, not an address-order or reachability approximation.
fn finalize_simd_dword_event_chains(prog: &mut AsmPassProgram) {
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    let resolved_addresses: HashSet<Address> = prog
        .resolved_addr_to_symbol
        .iter()
        .map(|(address, _, _)| *address)
        .collect();

    let mut event_options: BTreeMap<Address, BTreeSet<(i64, Address, Address)>> = BTreeMap::new();
    for (event, kind, input, target) in &prog.simd_dword_event_candidate {
        event_options
            .entry(*event)
            .or_default()
            .insert((*kind, *input, *target));
    }
    let uncertain_events: HashSet<Address> = prog
        .simd_dword_event_uncertain
        .iter()
        .map(|(event,)| *event)
        .collect();

    let mut exact_events = BTreeMap::new();
    for (event, options) in event_options {
        if options.len() != 1 || uncertain_events.contains(&event) {
            continue;
        }
        let (kind, input, target) = *options.iter().next().unwrap();
        let shape_is_valid = (kind == 0 && input == 0) || ((1..=5).contains(&kind) && input != 0);
        let base_resolves = resolved_addresses.contains(&target);
        let lane_addresses_fit = target.checked_add(12).is_some();
        if shape_is_valid
            && base_resolves
            && lane_addresses_fit
            && multi_synth_address_is_encodable(event)
        {
            exact_events.insert(event, (kind, input, target));
        }
    }

    fn chain_is_complete(
        event: Address,
        events: &BTreeMap<Address, (i64, Address, Address)>,
        visiting: &mut HashSet<Address>,
        memo: &mut HashMap<Address, bool>,
    ) -> bool {
        if let Some(result) = memo.get(&event) {
            return *result;
        }
        if !visiting.insert(event) {
            memo.insert(event, false);
            return false;
        }
        let complete = match events.get(&event).copied() {
            Some((0, 0, _)) => true,
            Some((kind @ 1..=5, input, _)) if input != 0 => {
                let _ = kind;
                chain_is_complete(input, events, visiting, memo)
            }
            _ => false,
        };
        visiting.remove(&event);
        memo.insert(event, complete);
        complete
    }

    let mut store_options: BTreeMap<Address, BTreeSet<(i64, Address)>> = BTreeMap::new();
    for (store, frame_ofs, definition) in &prog.simd_dword_frame_store_candidate {
        store_options
            .entry(*store)
            .or_default()
            .insert((*frame_ofs, *definition));
    }
    let uncertain_stores: HashSet<Address> = prog
        .simd_dword_frame_store_uncertain
        .iter()
        .map(|(store,)| *store)
        .collect();

    let mut memo = HashMap::new();
    let mut accepted_stores = BTreeSet::new();
    for (store, options) in store_options {
        if options.len() != 1
            || uncertain_stores.contains(&store)
            || !multi_synth_address_is_encodable(store)
        {
            continue;
        }
        let (frame_ofs, definition) = *options.iter().next().unwrap();
        if !chain_is_complete(definition, &exact_events, &mut HashSet::new(), &mut memo) {
            continue;
        }
        accepted_stores.insert((store, frame_ofs, definition));
    }

    let mut event_uses: BTreeMap<Address, BTreeSet<Address>> = BTreeMap::new();
    for (use_site, definition) in &prog.simd_dword_event_use {
        event_uses.entry(*definition).or_default().insert(*use_site);
    }

    let collect_required = |stores: &BTreeSet<(Address, i64, Address)>| {
        let mut required = BTreeSet::new();
        for (_, _, definition) in stores {
            let mut event = *definition;
            loop {
                required.insert(event);
                let (kind, input, _) = exact_events[&event];
                if kind == 0 {
                    break;
                }
                event = input;
            }
        }
        required
    };

    // Greatest closed set of valid store chains.  Starting from every exact
    // candidate and pruning is important: two accepted branches may safely
    // share one definition, while removing either branch can expose the
    // other's formerly-supported read as a dangling ordinary XMM consumer.
    let required_events = loop {
        let required = collect_required(&accepted_stores);
        let mut open_events = BTreeSet::new();
        for event in &required {
            for use_site in event_uses.get(event).into_iter().flatten() {
                let consumed_by_required_event = required.contains(use_site)
                    && exact_events
                        .get(use_site)
                        .is_some_and(|(kind, input, _)| *kind != 0 && input == event);
                let consumed_by_accepted_store = accepted_stores
                    .iter()
                    .any(|(store, _, definition)| store == use_site && definition == event);
                if !consumed_by_required_event && !consumed_by_accepted_store {
                    open_events.insert(*event);
                }
            }
        }
        if open_events.is_empty() {
            break required;
        }

        accepted_stores = accepted_stores
            .into_iter()
            .filter(|(_, _, definition)| {
                let mut event = *definition;
                loop {
                    if open_events.contains(&event) {
                        return false;
                    }
                    let (kind, input, _) = exact_events[&event];
                    if kind == 0 {
                        return true;
                    }
                    event = input;
                }
            })
            .collect();
    };

    prog.simd_dword_lane_event = required_events
        .iter()
        .map(|event| {
            let (kind, input, target) = exact_events[event];
            (*event, kind, input, target)
        })
        .collect();
    prog.simd_dword_lane_frame_store = accepted_stores.iter().copied().collect();

    // Accepted arithmetic is no longer an unmodelled-vector fingerprint, and
    // its event node must remain self-canonical through Linear so RTL can put
    // the scalar chain at the original instruction point.
    prog.packed_alu_addr = prog
        .packed_alu_addr
        .iter()
        .filter(|(address,)| !required_events.contains(address))
        .copied()
        .collect();
    prog.unhandled_reg_def_site = prog
        .unhandled_reg_def_site
        .iter()
        .filter(|(address, _)| !required_events.contains(address))
        .copied()
        .collect();
    let mut preserved_nodes: BTreeSet<(Address,)> =
        prog.node_unlowered_side_effect.iter().copied().collect();
    preserved_nodes.extend(required_events.iter().map(|address| (*address,)));
    prog.node_unlowered_side_effect = preserved_nodes.into_iter().collect();

    // The dword expansion completely replaces a recognized 16-byte frame
    // store; retaining the independent high-quadword expansion would create a
    // competing second write at the same machine event.
    let accepted_store_addresses: HashSet<Address> =
        accepted_stores.iter().map(|(store, _, _)| *store).collect();
    prog.xmm_hi_frame_store = prog
        .xmm_hi_frame_store
        .iter()
        .filter(|(store, _, _, _, _, _)| !accepted_store_addresses.contains(store))
        .copied()
        .collect();
}

pub struct AsmPass;

impl IRPass for AsmPass {
    fn name(&self) -> &'static str {
        "asm"
    }

    fn run(&self, db: &mut DecompileDB) {
        // This is the x86 frontend; AArch64 and ARM32 have their own. Stated as what this pass DOES handle, not as a list of what it does not: the former exclusion list named only AArch64 and was not updated when ARM32 landed, so the x86 pass ran on every ARM32 binary -- 30% of that pipeline's time, and a live hazard, since ARM32 spells MOV/ADD/SUB/CMP/PUSH/POP and R8-R12/SP, all of which parse in x86/asm.rs and x86/mach.rs.
        if !matches!(
            db.abi().arch,
            crate::abi::Arch::X86_64 | crate::abi::Arch::X86_32
        ) {
            return;
        }

        let mut prog = AsmPassProgram::default();
        prog.swap_db_fields(db);
        prog.run();
        let trace_simd_func = std::env::var("TRACE_FUNC").ok().and_then(|value| {
            let value = value.trim();
            if let Some(hex) = value
                .strip_prefix("0x")
                .or_else(|| value.strip_prefix("0X"))
            {
                Address::from_str_radix(hex, 16).ok()
            } else {
                value.parse::<Address>().ok()
            }
        });
        if let Some(func) = trace_simd_func {
            trace_simd_dword_state(&prog, func, "pre-finalize");
        }
        finalize_simd_dword_event_chains(&mut prog);
        if let Some(func) = trace_simd_func {
            trace_simd_dword_state(&prog, func, "post-finalize");
        }

        // Safety diagnostic: warn once per mnemonic for any instruction that wrote a register but produced no mach_inst, since its def still kills the value it overwrote in the reaching-def lattice.
        {
            use std::collections::BTreeMap;
            let mut per_mnem: BTreeMap<&'static str, (usize, Address)> = BTreeMap::new();
            for (addr, mnem) in prog.unhandled_reg_def_site.iter() {
                let entry = per_mnem.entry(*mnem).or_insert((0usize, *addr));
                entry.0 += 1;
                if *addr < entry.1 {
                    entry.1 = *addr;
                }
            }
            for (mnem, (count, first_addr)) in per_mnem {
                warn!(
                    "asm lowering: instruction '{}' writes a register but produced no mach_inst \
                     ({} site(s), first at {:#x}); its dropped def still kills the value it \
                     overwrote in reaching-defs -- a lowering for '{}' is likely missing.",
                    mnem, count, first_addr, mnem
                );
            }
        }

        if db.measure_rule_times {
            let pass_name = "AsmPassProgram".to_string();
            let summary = format!(
                "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
                prog.scc_times_summary(),
                prog.relation_sizes_summary(),
            );
            eprintln!(
                "[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]",
                pass_name, summary
            );
            db.rule_time_reports.push((pass_name, summary));
        }

        prog.swap_db_fields(db);
    }

    declare_io_from!(AsmPassProgram);
}

#[cfg(test)]
mod structural_dataflow_tests {
    use super::{
        exact_stack_offset, finalize_simd_dword_event_chains, integer_memory_chunk,
        recover_unsigned_divisor, refine_direct_load_chunk, AsmPass, AsmPassProgram,
    };
    use crate::decompile::passes::pass::IRPass;
    use crate::mreg::Mreg;
    use crate::x86::asm::{Ireg, TestCond};
    use crate::x86::op::{Addressing, Comparison, Condition, Operation, OverflowArithmetic};
    use crate::x86::types::{Address, Addrmode, Displacement, Ident, MachInst, MemoryChunk, Typ};
    use std::collections::BTreeSet;
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn on_large_stack(test: impl FnOnce() + Send + 'static) {
        // AsmPassProgram is intentionally very large. Keep these focused rule
        // tests independent of libtest's comparatively small worker stack.
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(test)
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn bsr_clz_idiom_crosses_unrelated_flag_transparent_moves() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let bsr = 0x1000;
            let middle = 0x1010;
            let middle2 = 0x1020;
            let xor = 0x1030;
            let block = 0x1000;
            prog.pbsr.push((bsr, "result", "source"));
            prog.next
                .extend([(bsr, middle), (middle, middle2), (middle2, xor)]);
            for node in [bsr, middle, middle2, xor] {
                prog.code_in_block.push((node, block));
            }
            prog.unrefinedinstruction
                .push((middle, 5, "", "MOV", "constant", "ECX", "", "", 0, 0));
            prog.unrefinedinstruction
                .push((middle2, 5, "", "MOV", "one", "EDI", "", "", 0, 0));
            prog.pxor.push((xor, "xor_result", "mask"));
            prog.op_immediate.push(("mask", 63, 8));
            prog.op_register
                .extend([("result", "RBX"), ("xor_result", "RBX"), ("source", "RBX")]);
            prog.builtins
                .extend([("__builtin_clzl",), ("__builtin_clzll",)]);

            prog.run();

            assert!(prog.expand_builtin_inline.iter().any(|(node, name, _, _)| {
                *node == bsr && matches!(*name, "__builtin_clzl" | "__builtin_clzll")
            }));
            assert!(prog
                .expand_builtin_inline
                .iter()
                .any(|(node, name, args, result)| {
                    *node == bsr
                        && matches!(*name, "__builtin_clzl" | "__builtin_clzll")
                        && args.as_slice() == [crate::x86::types::BuiltinArg::BA(Mreg::BX)]
                        && result == &crate::x86::types::BuiltinArg::BA(Mreg::BX)
                }));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == bsr
                    && matches!(
                        inst,
                        MachInst::Mbuiltin(
                            name,
                            args,
                            crate::x86::types::BuiltinArg::BA(result),
                        ) if matches!(name.as_str(), "__builtin_clzl" | "__builtin_clzll")
                            && args.as_slice()
                                == [crate::x86::types::BuiltinArg::BA(Mreg::BX)]
                            && *result == Mreg::BX
                    )
            }));
        });
    }

    #[test]
    fn ordered_float_eq_survives_interposed_true_value_move() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [cmp, parity, set_true, equal, false_target, success] = synthetic_ids();
            prog.pucomiss.push((cmp, "lhs", "rhs"));
            prog.op_register
                .extend([("lhs", "XMM0"), ("rhs", "XMM1"), ("true_dst", "EAX")]);
            prog.next.extend([
                (cmp, parity),
                (parity, set_true),
                (set_true, equal),
                (equal, false_target),
            ]);
            prog.pjcc.extend([
                (parity, TestCond::CondP, "false"),
                (equal, TestCond::CondE, "success"),
            ]);
            prog.direct_jump
                .extend([(parity, false_target), (equal, success)]);
            prog.instruction
                .push((set_true, 5, "", "MOV", "one", "true_dst", "", "", 0, 0));
            prog.op_immediate.push(("one", 1, 4));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == equal
                    && matches!(
                        inst,
                        MachInst::Mcond(Condition::Ccompfs(Comparison::Ceq), args, "success")
                            if args.as_slice() == [Mreg::X0, Mreg::X1]
                    )
            }));
        });
    }

    #[test]
    fn movq_loaded_double_sign_mask_recovers_fabs() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [load, and] = synthetic_ids();
            let mask = 0x2000;
            prog.instruction
                .push((load, 8, "", "MOVQ", "mask_mem", "mask_dst", "", "", 0, 0));
            prog.op_register.extend([
                ("mask_dst", "XMM1"),
                ("and_dst", "XMM1"),
                ("and_src", "XMM0"),
            ]);
            prog.rip_target_addr.push((load, mask));
            prog.fp_sign_clear_mask.push((mask, 8));
            prog.next.push((load, and));
            prog.pandpd.push((and, "and_dst", "and_src"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == and
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Oabsf, args, Mreg::X1)
                            if args.as_slice() == [Mreg::X0]
                    )
            }));
        });
    }

    #[test]
    fn setnp_cmovne_materializes_ordered_float_equality() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [cmp, set_ordered, extend, zero, cmov] = synthetic_ids();
            prog.fcmp_mem_arg.push((cmp, false, Mreg::X0));
            prog.fp0_loaded_at.push((cmp,));
            prog.next.extend([
                (cmp, set_ordered),
                (set_ordered, extend),
                (extend, zero),
                (zero, cmov),
            ]);
            prog.psetcc.push((set_ordered, TestCond::CondNp, "set_dst"));
            prog.instruction.push((
                extend,
                3,
                "",
                "MOVZX",
                "extend_src",
                "extend_dst",
                "",
                "",
                0,
                0,
            ));
            prog.instruction
                .push((zero, 5, "", "MOV", "zero_imm", "zero_dst", "", "", 0, 0));
            prog.op_immediate.push(("zero_imm", 0, 4));
            prog.pcmov
                .push((cmov, TestCond::CondNe, "cmov_dst", "cmov_src"));
            prog.op_register.extend([
                ("set_dst", "AL"),
                ("extend_src", "AL"),
                ("extend_dst", "EAX"),
                ("zero_dst", "EDX"),
                ("cmov_dst", "EAX"),
                ("cmov_src", "EDX"),
            ]);

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == cmov
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Ocmp(Condition::Ccompfs(Comparison::Ceq)),
                            args,
                            Mreg::AX
                        ) if args.as_slice() == [Mreg::X0, Mreg::FP0]
                    )
            }));
        });
    }

    #[derive(Clone, Copy)]
    enum AffineInterposed {
        None,
        HolderRedefinition,
        UnrelatedMove,
    }

    #[derive(Clone, Copy)]
    struct AffineFixtureNodes {
        extra: Option<u64>,
        negate: u64,
        add: u64,
        adjust: u64,
    }

    fn populate_affine_mod_fixture(
        prog: &mut AsmPassProgram,
        interposed: AffineInterposed,
        neg_view: &'static str,
        adjust_view: &'static str,
        split_before_neg: bool,
    ) -> AffineFixtureNodes {
        let func = 0x2100;
        let input_def = 0x2110;
        let bridge = 0x2120;
        let multiply = 0x2130;
        let endpoint = 0x2140;
        let q_times_three = 0x2150;
        let extra = match interposed {
            AffineInterposed::None => None,
            _ => Some(0x2160),
        };
        let negate = 0x2170;
        let add = 0x2180;
        let adjust = 0x2190;

        prog.unsigned_divide_origin.push((
            func,
            multiply,
            endpoint,
            Ireg::RCX,
            3,
            Ireg::RAX,
            false,
        ));
        prog.raw_gpr_analysis_width.push((func, 4));

        let mut nodes = vec![
            func,
            input_def,
            bridge,
            multiply,
            endpoint,
            q_times_three,
            negate,
            add,
            adjust,
        ];
        if let Some(extra) = extra {
            nodes.push(extra);
        }
        for node in nodes {
            prog.instr_in_function.push((node, func));
            let block = if split_before_neg && matches!(node, 0x2170 | 0x2180 | 0x2190) {
                negate
            } else {
                func
            };
            prog.code_in_block.push((node, block));
        }

        prog.next.extend([
            (func, input_def),
            (input_def, bridge),
            (bridge, multiply),
            (multiply, endpoint),
            (endpoint, q_times_three),
        ]);
        let before_neg = extra.unwrap_or(q_times_three);
        if let Some(extra) = extra {
            prog.next.push((q_times_three, extra));
        }
        prog.next
            .extend([(before_neg, negate), (negate, add), (add, adjust)]);
        if split_before_neg {
            prog.ddisasm_cfg_edge
                .push((before_neg, negate, "fallthrough"));
        }

        prog.reg_def.extend([
            (input_def, Mreg::AX),
            (q_times_three, Mreg::AX),
            (negate, Mreg::AX),
            (add, Mreg::AX),
            (adjust, Mreg::AX),
        ]);
        prog.plea
            .push((input_def, "fixture_input_dst", "fixture_input_addr"));
        prog.op_register.push(("fixture_input_dst", "EAX"));
        prog.op_indirect
            .push(("fixture_input_addr", "", "RBX", "NONE", 1, -1, 4));

        prog.plea
            .push((q_times_three, "fixture_q_dst", "fixture_q_addr"));
        prog.op_register.push(("fixture_q_dst", "EAX"));
        prog.op_indirect
            .push(("fixture_q_addr", "", "RCX", "RCX", 2, 0, 4));

        match interposed {
            AffineInterposed::None => {}
            AffineInterposed::HolderRedefinition => {
                let extra = extra.unwrap();
                prog.instruction.push((
                    extra,
                    5,
                    "",
                    "MOV",
                    "fixture_holder_imm",
                    "fixture_holder_dst",
                    "",
                    "",
                    0,
                    0,
                ));
                prog.op_immediate.push(("fixture_holder_imm", 123, 4));
                prog.op_register.push(("fixture_holder_dst", "EBX"));
                prog.reg_def.push((extra, Mreg::BX));
            }
            AffineInterposed::UnrelatedMove => {
                let extra = extra.unwrap();
                prog.instruction.push((
                    extra,
                    2,
                    "",
                    "MOV",
                    "fixture_unrelated_src",
                    "fixture_unrelated_dst",
                    "",
                    "",
                    0,
                    0,
                ));
                prog.op_register.extend([
                    ("fixture_unrelated_src", "EDI"),
                    ("fixture_unrelated_dst", "ESI"),
                ]);
                prog.reg_def.push((extra, Mreg::SI));
            }
        }

        prog.pneg.push((negate, "fixture_neg_dst"));
        prog.op_register.push(("fixture_neg_dst", neg_view));
        prog.padd.push((add, "fixture_add_dst", "fixture_add_src"));
        prog.op_register
            .extend([("fixture_add_dst", "EAX"), ("fixture_add_src", "EBX")]);
        prog.instruction
            .push((adjust, 2, "", "DEC", "fixture_adjust_dst", "", "", "", 0, 0));
        prog.op_register.push(("fixture_adjust_dst", adjust_view));

        AffineFixtureNodes {
            extra,
            negate,
            add,
            adjust,
        }
    }

    #[test]
    fn unsigned_magic_sub_remainder_reads_the_saved_dividend() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            // Deliberately nonmonotone identities: only the explicit `next`
            // chain establishes the quotient-product and remainder shape.
            let endpoint = 0x900;
            let quotient_times_three = 0x100;
            let remainder = 0x700;
            let saved_dividend = 0x300;
            let func = saved_dividend;

            prog.divide_q.push((
                func,
                saved_dividend,
                endpoint,
                Ireg::RAX,
                3,
                Ireg::RAX,
                4,
                true,
            ));
            prog.raw_gpr_analysis_width.push((func, 4));
            prog.next.extend([
                (saved_dividend, endpoint),
                (endpoint, quotient_times_three),
                (quotient_times_three, remainder),
            ]);
            for node in [saved_dividend, endpoint, quotient_times_three, remainder] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, func));
            }

            prog.plea.push((
                quotient_times_three,
                "q_times_three_dst",
                "q_times_three_addr",
            ));
            prog.op_register.push(("q_times_three_dst", "EAX"));
            prog.op_indirect
                .push(("q_times_three_addr", "", "RAX", "RAX", 2, 0, 4));

            // The original dividend was copied to EDX before EAX became q and
            // then q*3.  The old lowering nevertheless emitted EAX % 3.
            prog.pmov
                .push((saved_dividend, "saved_dividend_dst", "saved_dividend_src"));
            prog.instruction.push((
                saved_dividend,
                2,
                "",
                "MOV",
                "saved_dividend_src",
                "saved_dividend_dst",
                "",
                "",
                0,
                0,
            ));
            prog.op_register
                .extend([("saved_dividend_dst", "EDX"), ("saved_dividend_src", "EAX")]);
            prog.reg_def.push((saved_dividend, Mreg::DX));
            prog.psub
                .push((remainder, "remainder_dst", "remainder_src"));
            prog.op_register
                .extend([("remainder_dst", "EDX"), ("remainder_src", "EAX")]);

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == remainder
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Omoduimm(3), args, Mreg::DX)
                            if args.as_slice() == [Mreg::DX]
                    )
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == remainder
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Omodimm(3) | Operation::Omoduimm(3),
                            args,
                            Mreg::DX
                        ) if args.as_slice() == [Mreg::AX]
                    )
            }));
        });
    }

    #[test]
    fn legacy_unsigned_magic_matcher_feeds_shared_remainder_provenance() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let magic_load = 0x500;
            let multiply = 0x600;
            let quotient_endpoint = 0x700;
            let func = magic_load;

            // Clang's common unsigned /3 form is recognized by div_magic_64:
            // load 0xaaaaaaab, multiply a separate dividend register, then
            // shift the 64-bit product right by 33.
            prog.div_magic_64.push((
                magic_load,
                quotient_endpoint,
                0xaaaa_aaab,
                33,
                Ireg::RBX,
                Ireg::RCX,
            ));
            prog.next
                .extend([(magic_load, multiply), (multiply, quotient_endpoint)]);
            for node in [magic_load, multiply, quotient_endpoint] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, func));
            }
            prog.pimul
                .push((multiply, "legacy_imul_dst", "legacy_imul_src"));
            prog.pshr
                .push((quotient_endpoint, "legacy_shr_dst", "legacy_shift"));
            prog.op_register.extend([
                ("legacy_imul_dst", "RCX"),
                ("legacy_imul_src", "RBX"),
                ("legacy_shr_dst", "RCX"),
            ]);

            prog.run();

            assert!(prog.unsigned_divide_origin.iter().any(|row| {
                row == &(
                    func,
                    multiply,
                    quotient_endpoint,
                    Ireg::RCX,
                    3,
                    Ireg::RBX,
                    false,
                )
            }));
            assert!(prog.divide_q.iter().any(|row| {
                row == &(
                    func,
                    multiply,
                    quotient_endpoint,
                    Ireg::RCX,
                    3,
                    Ireg::RBX,
                    4,
                    true,
                )
            }));
        });
    }

    #[test]
    fn unsigned_magic_neg_add_adjust_recovers_modulo_at_real_defs() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x600;
            let input_def = 0x500;
            let between = 0x400;
            let multiply = 0x300;
            let endpoint = 0x900;
            let quotient_times_three = 0x100;
            let negate = 0x800;
            let add_holder = 0x200;
            let decrement = 0x700;

            // Populate only relations which exist before ASM in the real
            // pipeline.  In particular, do not inject downstream
            // `reg_def_used`: the point-keyed affine lattice must carry the
            // LEA definition to the multiply itself.
            prog.unsigned_divide_origin.push((
                func,
                multiply,
                endpoint,
                Ireg::RCX,
                3,
                Ireg::RAX,
                false,
            ));
            prog.raw_gpr_analysis_width.push((func, 4));
            for node in [
                func,
                input_def,
                between,
                multiply,
                endpoint,
                quotient_times_three,
                negate,
                add_holder,
                decrement,
            ] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, func));
            }
            prog.next.extend([
                (func, input_def),
                (input_def, between),
                (between, multiply),
                (multiply, endpoint),
            ]);
            prog.reg_def.push((input_def, Mreg::AX));
            prog.plea
                .push((input_def, "clang_input_dst", "clang_input_addr"));
            prog.op_register.push(("clang_input_dst", "EAX"));
            prog.op_indirect
                .push(("clang_input_addr", "", "RBX", "NONE", 1, -1, 4));

            prog.next.extend([
                (endpoint, quotient_times_three),
                (quotient_times_three, negate),
                (negate, add_holder),
                (add_holder, decrement),
            ]);

            prog.plea.push((
                quotient_times_three,
                "clang_q_times_three_dst",
                "clang_q_times_three_addr",
            ));
            prog.op_register.push(("clang_q_times_three_dst", "EAX"));
            prog.op_indirect
                .push(("clang_q_times_three_addr", "", "RCX", "RCX", 2, 0, 4));
            prog.pneg.push((negate, "clang_neg_dst"));
            prog.op_register.push(("clang_neg_dst", "EAX"));
            prog.padd
                .push((add_holder, "clang_add_dst", "clang_add_src"));
            prog.op_register
                .extend([("clang_add_dst", "EAX"), ("clang_add_src", "EBX")]);
            prog.instruction
                .push((decrement, 2, "", "DEC", "clang_dec_dst", "", "", "", 0, 0));
            prog.op_register.push(("clang_dec_dst", "EAX"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == add_holder
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Oaddimm(-1), args, Mreg::AX)
                            if args.as_slice() == [Mreg::BX]
                    )
            }));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == decrement
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Omoduimm(3), args, Mreg::AX)
                            if args.as_slice() == [Mreg::AX]
                    )
            }));
            assert!(prog.div_consumed.iter().any(|row| row == &(negate,)));
            assert!(prog
                .div_consumed
                .iter()
                .any(|row| row == &(quotient_times_three,)));
        });
    }

    #[test]
    fn unsigned_magic_affine_remainder_rejects_an_unknown_cfg_arm() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x100;
            let affine_def = 0x900;
            let unknown_def = 0x200;
            let join = 0x800;
            let multiply = 0x300;
            let endpoint = 0x700;
            let quotient_times_three = 0x400;
            let negate = 0x600;
            let add_holder = 0x500;
            let decrement = 0xa00;

            prog.unsigned_divide_origin.push((
                func,
                multiply,
                endpoint,
                Ireg::RCX,
                3,
                Ireg::RAX,
                false,
            ));
            prog.raw_gpr_analysis_width.push((func, 4));
            for node in [
                func,
                affine_def,
                unknown_def,
                join,
                multiply,
                endpoint,
                quotient_times_three,
                negate,
                add_holder,
                decrement,
            ] {
                prog.instr_in_function.push((node, func));
            }
            prog.ddisasm_cfg_edge.extend([
                (func, affine_def, "branch"),
                (func, unknown_def, "fallthrough"),
                (affine_def, join, "fallthrough"),
                (unknown_def, join, "fallthrough"),
                (join, multiply, "fallthrough"),
            ]);
            for node in [
                multiply,
                endpoint,
                quotient_times_three,
                negate,
                add_holder,
                decrement,
            ] {
                prog.code_in_block.push((node, multiply));
            }
            prog.reg_def
                .extend([(affine_def, Mreg::AX), (unknown_def, Mreg::AX)]);
            prog.plea
                .push((affine_def, "branch_input_dst", "branch_input_addr"));
            prog.op_register.push(("branch_input_dst", "EAX"));
            prog.op_indirect
                .push(("branch_input_addr", "", "RBX", "NONE", 1, -1, 4));

            prog.next.extend([
                (multiply, endpoint),
                (endpoint, quotient_times_three),
                (quotient_times_three, negate),
                (negate, add_holder),
                (add_holder, decrement),
            ]);
            prog.plea.push((
                quotient_times_three,
                "branch_q_times_three_dst",
                "branch_q_times_three_addr",
            ));
            prog.op_register.push(("branch_q_times_three_dst", "EAX"));
            prog.op_indirect
                .push(("branch_q_times_three_addr", "", "RCX", "RCX", 2, 0, 4));
            prog.pneg.push((negate, "branch_neg_dst"));
            prog.op_register.push(("branch_neg_dst", "EAX"));
            prog.padd
                .push((add_holder, "branch_add_dst", "branch_add_src"));
            prog.op_register
                .extend([("branch_add_dst", "EAX"), ("branch_add_src", "EBX")]);
            prog.instruction
                .push((decrement, 2, "", "DEC", "branch_dec_dst", "", "", "", 0, 0));
            prog.op_register.push(("branch_dec_dst", "EAX"));

            prog.run();

            assert!(prog
                .unsigned_affine_conflict
                .iter()
                .any(|row| row == &(func, multiply, Mreg::AX, 4)));
            assert!(!prog.mach_inst.iter().any(|(_, inst)| matches!(
                inst,
                MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX)
            )));
        });
    }

    #[test]
    fn unsigned_magic_reciprocal_requires_full_domain_exactness() {
        assert_eq!(recover_unsigned_divisor(0xaaaa_aaab, 33, 32), Some(3));
        // floor(2^33/3) looks one unit away from the valid reciprocal but
        // already under-divides n=3, so proximity is not a proof.
        assert_eq!(recover_unsigned_divisor(0xaaaa_aaaa, 33, 32), None);
    }

    #[test]
    fn unsigned_magic_load_must_reach_the_multiply_in_its_owner() {
        on_large_stack(|| {
            for cross_function in [false, true] {
                let mut prog = AsmPassProgram::default();
                let func = 0x3100;
                let prologue = func;
                let multiply = 0x3110;
                let magic_load = if cross_function { 0x4100 } else { 0x3120 };
                let shift = 0x3130;
                let magic_owner = if cross_function { magic_load } else { func };

                for node in [prologue, multiply, shift] {
                    prog.instr_in_function.push((node, func));
                    prog.code_in_block.push((node, func));
                }
                prog.instr_in_function.push((magic_load, magic_owner));
                prog.code_in_block.push((magic_load, magic_owner));
                prog.next.push((prologue, multiply));
                if cross_function {
                    prog.next.push((multiply, shift));
                } else {
                    // The matching constant exists only after the IMUL.
                    prog.next
                        .extend([(multiply, magic_load), (magic_load, shift)]);
                }

                prog.instruction.push((
                    magic_load,
                    5,
                    "",
                    "MOV",
                    "late_magic_imm",
                    "late_magic_dst",
                    "",
                    "",
                    0,
                    0,
                ));
                prog.op_immediate.push(("late_magic_imm", 0xaaaa_aaab, 4));
                prog.op_register.push(("late_magic_dst", "EDX"));
                prog.reg_def.push((magic_load, Mreg::DX));
                prog.pimul
                    .push((multiply, "late_imul_dst", "late_imul_src"));
                prog.op_register.extend([
                    ("late_imul_dst", "RAX"),
                    ("late_imul_src", "RDX"),
                    ("late_shr_dst", "RAX"),
                ]);
                prog.pshr.push((shift, "late_shr_dst", "late_shift_count"));
                prog.op_immediate.push(("late_shift_count", 33, 1));

                prog.run();

                assert!(prog.imul2_magic.is_empty());
                assert!(prog.div_magic_2op.is_empty());
            }
        });
    }

    #[test]
    fn preloaded_unsigned_magic_divide_can_start_a_basic_block() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x5100;
            let magic_load = 0x5110;
            let branch = 0x5120;
            let multiply = 0x5130;
            let shift = 0x5140;

            for node in [func, magic_load, branch, multiply, shift] {
                prog.instr_in_function.push((node, func));
            }
            for node in [func, magic_load, branch] {
                prog.code_in_block.push((node, func));
            }
            for node in [multiply, shift] {
                prog.code_in_block.push((node, multiply));
            }
            prog.next.extend([
                (func, magic_load),
                (magic_load, branch),
                (branch, multiply),
                (multiply, shift),
            ]);
            prog.ddisasm_cfg_edge.push((branch, multiply, "branch"));

            prog.instruction.push((
                magic_load,
                5,
                "",
                "MOV",
                "magic_imm",
                "magic_dst",
                "",
                "",
                0,
                0,
            ));
            prog.pmov.push((magic_load, "magic_dst", "magic_imm"));
            prog.op_register.push(("magic_dst", "ESI"));
            prog.op_immediate
                .push(("magic_imm", 0xcccc_cccdu32 as i64, 4));
            prog.reg_def.push((magic_load, Mreg::SI));

            prog.pimul.push((multiply, "mul_dst", "mul_src"));
            prog.op_register
                .extend([("mul_dst", "RAX"), ("mul_src", "RSI")]);
            prog.reg_def.push((multiply, Mreg::AX));

            prog.pshr.push((shift, "shr_dst", "shr_count"));
            prog.op_register.push(("shr_dst", "RAX"));
            prog.op_immediate.push(("shr_count", 35, 1));
            prog.reg_def.push((shift, Mreg::AX));

            prog.run();

            assert!(prog
                .div_magic_2op
                .iter()
                .any(|row| { row == &(multiply, shift, 10, Ireg::RAX, Ireg::RAX) }));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == multiply
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Odivuimm(10), args, Mreg::AX)
                            if args.as_slice() == [Mreg::AX]
                    )
            }));
        });
    }

    #[test]
    fn unsigned_affine_modulo_rejects_holder_redefinition() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let nodes = populate_affine_mod_fixture(
                &mut prog,
                AffineInterposed::HolderRedefinition,
                "EAX",
                "EAX",
                false,
            );
            prog.run();

            assert!(!prog.mach_inst.iter().any(|(_, inst)| matches!(
                inst,
                MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX)
            )));
            assert!(!prog.div_consumed.iter().any(|row| row == &(nodes.negate,)));
        });
    }

    #[test]
    fn unsigned_affine_modulo_rejects_partial_register_steps() {
        on_large_stack(|| {
            for (neg_view, adjust_view) in [("AX", "EAX"), ("EAX", "AX")] {
                let mut prog = AsmPassProgram::default();
                populate_affine_mod_fixture(
                    &mut prog,
                    AffineInterposed::None,
                    neg_view,
                    adjust_view,
                    false,
                );
                prog.run();
                assert!(!prog.mach_inst.iter().any(|(_, inst)| matches!(
                    inst,
                    MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX)
                )));
            }
        });
    }

    #[test]
    fn unsigned_affine_modulo_does_not_cross_a_basic_block_boundary() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            populate_affine_mod_fixture(&mut prog, AffineInterposed::None, "EAX", "EAX", true);
            prog.run();
            assert!(!prog.mach_inst.iter().any(|(_, inst)| matches!(
                inst,
                MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX)
            )));
        });
    }

    #[test]
    fn unsigned_affine_modulo_requires_every_shared_owner() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let nodes =
                populate_affine_mod_fixture(&mut prog, AffineInterposed::None, "EAX", "EAX", false);
            // The address-global final instruction is shared, but this second
            // owner has no divide/affine proof.
            prog.instr_in_function.push((nodes.adjust, 0x5100));
            prog.run();
            assert!(!prog.mach_inst.iter().any(|(_, inst)| matches!(
                inst,
                MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX)
            )));
        });
    }

    #[test]
    fn modulo_suppression_preserves_unrelated_interleaved_move() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let nodes = populate_affine_mod_fixture(
                &mut prog,
                AffineInterposed::UnrelatedMove,
                "EAX",
                "EAX",
                false,
            );
            prog.run();
            let extra = nodes.extra.unwrap();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == nodes.adjust
                    && matches!(inst, MachInst::Mop(Operation::Omoduimm(3), _, Mreg::AX))
            }));
            assert!(!prog.div_consumed.iter().any(|row| row == &(extra,)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == extra
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Omove, args, Mreg::SI)
                            if args.as_slice() == [Mreg::DI]
                    )
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == nodes.negate && matches!(inst, MachInst::Mop(Operation::Oneg, _, _))
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == nodes.adjust && matches!(inst, MachInst::Mop(Operation::Oaddimm(-1), _, _))
            }));
            assert!(prog.div_consumed.iter().any(|row| row == &(nodes.add,)));
        });
    }

    #[test]
    #[ignore = "diagnostic harness; requires MANIFOLD_DIAG_BINARY"]
    fn trace_pipeline_binary_from_env() {
        on_large_stack(|| {
            let binary = std::path::PathBuf::from(
                std::env::var("MANIFOLD_DIAG_BINARY")
                    .expect("MANIFOLD_DIAG_BINARY must name an input binary"),
            );
            let mut db = crate::decompile::elevator::DecompileDB::default();
            crate::decompile::disassembly::load_from_binary(&mut db, &binary);
            crate::decompile::disassembly::load_preset(&mut db);
            db.run_pipeline(&binary, false, false);
        });
    }

    #[test]
    fn direct_symbol_loads_use_memory_source_width_before_extension() {
        assert_eq!(
            refine_direct_load_chunk("MOVZX", MemoryChunk::MInt32, 1),
            MemoryChunk::MInt8Unsigned
        );
        assert_eq!(
            refine_direct_load_chunk("MOVSX", MemoryChunk::MInt64, 2),
            MemoryChunk::MInt16Signed
        );
        assert_eq!(
            refine_direct_load_chunk("MOV", MemoryChunk::MInt64, 1),
            MemoryChunk::MInt8Unsigned
        );

        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let rip_load = 0x401138;
            let absolute_load = 0x401240;

            for (node, source, destination) in [
                (rip_load, "rip_byte", "rip_dst"),
                (absolute_load, "absolute_byte", "absolute_dst"),
            ] {
                prog.instruction
                    .push((node, 7, "", "MOVZX", source, destination, "", "", 0, 0));
                prog.pmov.push((node, destination, source));
                prog.op_indirect.push((
                    source,
                    "",
                    if node == rip_load { "RIP" } else { "NONE" },
                    "NONE",
                    1,
                    0x404031,
                    1,
                ));
            }
            prog.op_register
                .extend([("rip_dst", "EDX"), ("absolute_dst", "EAX")]);
            prog.rip_target_addr.push((rip_load, 0x404031));
            prog.abs_target_addr.push((absolute_load, 0x404031));
            prog.resolved_addr_to_symbol.push((0x404031, 0x404030, 1));

            prog.run();

            for (node, destination) in [(rip_load, Mreg::DX), (absolute_load, Mreg::AX)] {
                assert!(prog.mach_inst.iter().any(|(candidate_node, inst)| {
                    *candidate_node == node
                        && matches!(
                            inst,
                            MachInst::Mload(
                                MemoryChunk::MInt8Unsigned,
                                Addressing::Aglobal(0x404030, 1),
                                args,
                                actual_destination
                            ) if args.is_empty() && *actual_destination == destination
                        )
                }));
                assert!(!prog.mach_inst.iter().any(|(candidate_node, inst)| {
                    *candidate_node == node
                        && matches!(inst, MachInst::Mload(MemoryChunk::MInt32, _, _, _))
                }));
            }
        });
    }

    #[test]
    fn integer_memory_arithmetic_uses_decoded_operand_width() {
        assert_eq!(integer_memory_chunk(1), Some(MemoryChunk::MInt8Unsigned));
        assert_eq!(integer_memory_chunk(2), Some(MemoryChunk::MInt16Unsigned));
        assert_eq!(integer_memory_chunk(4), Some(MemoryChunk::MInt32));
        assert_eq!(integer_memory_chunk(8), Some(MemoryChunk::MInt64));
        assert_eq!(integer_memory_chunk(3), None);

        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cases = [
                (
                    0x6100,
                    "byte_dst",
                    "byte_mem",
                    "CL",
                    1,
                    Operation::Oxor,
                    MemoryChunk::MInt8Unsigned,
                    Mreg::CX,
                ),
                (
                    0x6110,
                    "word_dst",
                    "word_mem",
                    "AX",
                    2,
                    Operation::Oadd,
                    MemoryChunk::MInt16Unsigned,
                    Mreg::AX,
                ),
                (
                    0x6120,
                    "dword_dst",
                    "dword_mem",
                    "EAX",
                    4,
                    Operation::Osub,
                    MemoryChunk::MInt32,
                    Mreg::AX,
                ),
                (
                    0x6130,
                    "qword_dst",
                    "qword_mem",
                    "RAX",
                    8,
                    Operation::Oorl,
                    MemoryChunk::MInt64,
                    Mreg::AX,
                ),
            ];

            for (node, dst, src, dst_name, width, expected_op, _, _) in &cases {
                match expected_op {
                    Operation::Oxor => prog.pxor.push((*node, *dst, *src)),
                    Operation::Oadd => prog.padd.push((*node, *dst, *src)),
                    Operation::Osub => prog.psub.push((*node, *dst, *src)),
                    Operation::Oorl => prog.por.push((*node, *dst, *src)),
                    _ => unreachable!(),
                };
                prog.op_register.push((*dst, *dst_name));
                prog.op_indirect
                    .push((*src, "", "RSP", "NONE", 1, 3, *width));
            }

            prog.run();

            for (node, _, _, _, _, expected_op, expected_chunk, expected_mreg) in cases {
                assert!(prog.arith_load_op.iter().any(|fact| {
                    fact == &(
                        node,
                        expected_op.clone(),
                        expected_chunk,
                        Mreg::SP,
                        3,
                        expected_mreg,
                    )
                }));
            }
        });
    }

    #[test]
    fn integer_memory_destination_rmw_preserves_width_and_stack_base() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let register_cases = [
                (
                    0x6200,
                    1_i64,
                    "add_byte_mem",
                    "add_byte_src",
                    "CL",
                    1_usize,
                    Operation::Oadd,
                    MemoryChunk::MInt8Unsigned,
                ),
                (
                    0x6210,
                    2,
                    "sub_word_mem",
                    "sub_word_src",
                    "AX",
                    2,
                    Operation::Osub,
                    MemoryChunk::MInt16Unsigned,
                ),
                (
                    0x6220,
                    3,
                    "and_byte_mem",
                    "and_byte_src",
                    "CL",
                    1,
                    Operation::Oand,
                    MemoryChunk::MInt8Unsigned,
                ),
                (
                    0x6230,
                    4,
                    "or_word_mem",
                    "or_word_src",
                    "AX",
                    2,
                    Operation::Oor,
                    MemoryChunk::MInt16Unsigned,
                ),
                (
                    0x6240,
                    5,
                    "xor_byte_mem",
                    "xor_byte_src",
                    "CL",
                    1,
                    Operation::Oxor,
                    MemoryChunk::MInt8Unsigned,
                ),
                (
                    0x6250,
                    1,
                    "add_qword_mem",
                    "add_qword_src",
                    "RAX",
                    8,
                    Operation::Oaddl,
                    MemoryChunk::MInt64,
                ),
            ];

            for (node, kind, memory, source, source_name, width, _, _) in &register_cases {
                match kind {
                    1 => prog.padd.push((*node, *memory, *source)),
                    2 => prog.psub.push((*node, *memory, *source)),
                    3 => prog.pand.push((*node, *memory, *source)),
                    4 => prog.por.push((*node, *memory, *source)),
                    5 => prog.pxor.push((*node, *memory, *source)),
                    _ => unreachable!(),
                };
                prog.op_register.push((*source, *source_name));
                prog.op_indirect
                    .push((*memory, "", "RSP", "NONE", 1, 24, *width));
            }

            let immediate_cases = [
                (
                    0x6260,
                    2_i64,
                    "sub_word_imm_mem",
                    "sub_word_imm",
                    7_i64,
                    2_usize,
                    Operation::Oaddimm(-7),
                    MemoryChunk::MInt16Unsigned,
                ),
                (
                    0x6270,
                    3,
                    "and_byte_imm_mem",
                    "and_byte_imm",
                    0x7f,
                    1,
                    Operation::Oandimm(0x7f),
                    MemoryChunk::MInt8Unsigned,
                ),
                (
                    0x6280,
                    4,
                    "or_qword_imm_mem",
                    "or_qword_imm",
                    9,
                    8,
                    Operation::Oorlimm(9),
                    MemoryChunk::MInt64,
                ),
            ];
            for (node, kind, memory, immediate, value, width, _, _) in &immediate_cases {
                match kind {
                    2 => prog.psub.push((*node, *memory, *immediate)),
                    3 => prog.pand.push((*node, *memory, *immediate)),
                    4 => prog.por.push((*node, *memory, *immediate)),
                    _ => unreachable!(),
                };
                prog.op_immediate.push((*immediate, *value, 1));
                prog.op_indirect
                    .push((*memory, "", "RSP", "NONE", 1, 32, *width));
            }

            let xadd = 0x6290;
            prog.instruction.push((
                xadd,
                4,
                "",
                "XADD",
                "xadd_byte_src",
                "xadd_byte_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("xadd_byte_src", "CL"));
            prog.op_indirect
                .push(("xadd_byte_mem", "", "RSP", "NONE", 1, 40, 1));

            let rip = 0x62a0;
            let rip_target = 0x404031;
            let rip_ident = 0x404030;
            prog.pxor.push((rip, "rip_byte_mem", "rip_byte_src"));
            prog.op_register.push(("rip_byte_src", "CL"));
            prog.op_indirect
                .push(("rip_byte_mem", "", "RIP", "NONE", 1, 17, 1));
            prog.rip_target_addr.push((rip, rip_target));
            prog.resolved_addr_to_symbol
                .push((rip_target, rip_ident, 1));

            let absolute = 0x62b0;
            let absolute_target = 0x405002;
            let absolute_ident = 0x405000;
            prog.por
                .push((absolute, "absolute_word_mem", "absolute_word_imm"));
            prog.op_immediate.push(("absolute_word_imm", 0x55, 1));
            prog.op_indirect.push((
                "absolute_word_mem",
                "",
                "NONE",
                "NONE",
                1,
                absolute_target as i64,
                2,
            ));
            prog.abs_target_addr.push((absolute, absolute_target));
            prog.resolved_addr_to_symbol
                .push((absolute_target, absolute_ident, 2));

            prog.run();

            for (node, _, _, _, source_name, _, expected_op, expected_chunk) in register_cases {
                assert!(prog.arith_store_reg.iter().any(|fact| {
                    fact == &(
                        node,
                        expected_op.clone(),
                        expected_chunk,
                        Mreg::SP,
                        24,
                        Mreg::x86(source_name),
                    )
                }));
            }
            for (node, _, _, _, _, _, expected_op, expected_chunk) in immediate_cases {
                assert!(prog.arith_store_imm.iter().any(|fact| {
                    fact == &(node, expected_op.clone(), expected_chunk, Mreg::SP, 32)
                }));
            }
            assert!(prog.arith_store_reg.iter().any(|fact| {
                fact == &(
                    xadd,
                    Operation::Oadd,
                    MemoryChunk::MInt8Unsigned,
                    Mreg::SP,
                    40,
                    Mreg::CX,
                )
            }));
            assert!(prog.arith_store_abs_reg.iter().any(|fact| {
                fact == &(
                    rip,
                    Operation::Oxor,
                    MemoryChunk::MInt8Unsigned,
                    rip_ident,
                    1,
                    Mreg::CX,
                )
            }));
            assert!(prog.arith_store_abs_imm.iter().any(|fact| {
                fact == &(
                    absolute,
                    Operation::Oorimm(0x55),
                    MemoryChunk::MInt16Unsigned,
                    absolute_ident,
                    2,
                )
            }));
        });
    }

    #[test]
    fn settled_simd_event_provenance_rejects_ambiguous_cfg_joins() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let load = 0x900;
            let add = 0x100;
            let xor = 0x700;
            let store = 0x200;
            let base = 0x404040;
            let addend = 0x402010;
            let mask = 0x402020;

            prog.simd_dword_event_candidate.extend([
                (load, 0, 0, base),
                (add, 1, load, addend),
                (xor, 5, add, mask),
            ]);
            prog.simd_dword_event_use
                .extend([(add, load), (xor, add), (store, xor)]);
            prog.simd_dword_frame_store_candidate
                .push((store, -24, xor));
            for (ident, target) in [
                (base as usize, base),
                (addend as usize, addend),
                (mask as usize, mask),
            ] {
                // Anonymous constant tables normally expose one synthetic symbol
                // at the instruction's exact RIP target, not four symbols at its
                // interior dword addresses.
                prog.resolved_addr_to_symbol.push((target, ident, 0));
            }
            prog.packed_alu_addr.extend([(add,), (xor,)]);
            prog.unhandled_reg_def_site
                .extend([(add, "PADDD"), (xor, "PXOR")]);
            prog.xmm_hi_frame_store
                .push((store, -16, 3, Mreg::Unknown, base as i64, load));

            finalize_simd_dword_event_chains(&mut prog);

            assert_eq!(
                prog.simd_dword_lane_event,
                vec![
                    (add, 1, load, addend),
                    (xor, 5, add, mask),
                    (load, 0, 0, base)
                ]
            );
            assert_eq!(prog.simd_dword_lane_frame_store, vec![(store, -24, xor)]);
            for event in [load, add, xor] {
                assert!(prog
                    .node_unlowered_side_effect
                    .iter()
                    .any(|fact| fact == &(event,)));
            }
            assert!(prog.packed_alu_addr.is_empty());
            assert!(prog.unhandled_reg_def_site.is_empty());
            assert!(prog.xmm_hi_frame_store.is_empty());

            let mut ambiguous = AsmPassProgram::default();
            ambiguous.simd_dword_event_candidate.extend([
                (load, 0, 0, base),
                (add, 1, load, addend),
                // A distinct reaching definition at the same event models a real
                // CFG join; neither predecessor may be selected arbitrarily.
                (add, 1, 0x880, addend),
            ]);
            ambiguous
                .simd_dword_frame_store_candidate
                .push((store, -24, add));
            for target in [base, addend] {
                ambiguous
                    .resolved_addr_to_symbol
                    .push((target, target as usize, 0));
            }

            finalize_simd_dword_event_chains(&mut ambiguous);
            assert!(ambiguous.simd_dword_lane_event.is_empty());
            assert!(ambiguous.simd_dword_lane_frame_store.is_empty());

            let mut absent_path = AsmPassProgram::default();
            absent_path
                .simd_dword_event_candidate
                .extend([(load, 0, 0, base), (add, 1, load, addend)]);
            // One predecessor carries `load`; another reaches the operation with
            // no supported XMM definition.  Explicit Unknown must veto the chain
            // even though the known option alone is unique.
            absent_path.simd_dword_event_uncertain.push((add,));
            absent_path
                .simd_dword_frame_store_candidate
                .push((store, -24, add));
            absent_path
                .resolved_addr_to_symbol
                .extend([(base, base as usize, 0), (addend, addend as usize, 0)]);
            finalize_simd_dword_event_chains(&mut absent_path);
            assert!(absent_path.simd_dword_lane_event.is_empty());
            assert!(absent_path.simd_dword_lane_frame_store.is_empty());

            let mut uncertain_store = AsmPassProgram::default();
            uncertain_store
                .simd_dword_event_candidate
                .push((load, 0, 0, base));
            uncertain_store
                .simd_dword_frame_store_candidate
                .push((store, -24, load));
            uncertain_store
                .simd_dword_frame_store_uncertain
                .push((store,));
            uncertain_store
                .resolved_addr_to_symbol
                .push((base, base as usize, 0));
            finalize_simd_dword_event_chains(&mut uncertain_store);
            assert!(uncertain_store.simd_dword_lane_event.is_empty());
            assert!(uncertain_store.simd_dword_lane_frame_store.is_empty());

            let mut open_component = AsmPassProgram::default();
            let unused_consumer = 0x330;
            open_component.simd_dword_event_candidate.extend([
                (load, 0, 0, base),
                (add, 1, load, addend),
                // This recognized branch has no accepted spill.  Leaving it as an
                // ordinary packed instruction while removing LOAD would make it
                // read an undefined architectural XMM value.
                (unused_consumer, 5, load, mask),
            ]);
            open_component.simd_dword_event_use.extend([
                (add, load),
                (unused_consumer, load),
                (store, add),
            ]);
            open_component
                .simd_dword_frame_store_candidate
                .push((store, -24, add));
            open_component.resolved_addr_to_symbol.extend([
                (base, base as usize, 0),
                (addend, addend as usize, 0),
                (mask, mask as usize, 0),
            ]);
            finalize_simd_dword_event_chains(&mut open_component);
            assert!(open_component.simd_dword_lane_event.is_empty());
            assert!(open_component.simd_dword_lane_frame_store.is_empty());
        });
    }

    #[test]
    fn simd_event_state_rejects_raw_consumers_and_vzeroall() {
        on_large_stack(|| {
            let make_program = |intervening: u64, mnemonic: &'static str, raw_use: bool| {
                let load = 0x900;
                let add = 0x700;
                let store = 0x200;
                let base = 0x404040;
                let addend = 0x402010;
                let mut prog = AsmPassProgram::default();
                prog.simd_dword_global_seed.push((load, Mreg::X0, base));
                prog.simd_dword_mem_binop
                    .push((add, 1, Mreg::X0, Mreg::X0, addend));
                prog.simd_dword_frame_spill_site
                    .push((store, Mreg::X0, -24));
                prog.reg_def.extend([(load, Mreg::X0), (add, Mreg::X0)]);
                prog.reg_use.extend([(add, Mreg::X0), (store, Mreg::X0)]);
                if raw_use {
                    prog.reg_use.push((intervening, Mreg::X0));
                }
                prog.instruction
                    .push((intervening, 3, "", mnemonic, "", "", "", "", 0, 0));
                for node in [load, intervening, add, store] {
                    prog.instr_in_function.push((node, load));
                }
                prog.ddisasm_cfg_edge.extend([
                    (load, intervening, "fallthrough"),
                    (intervening, add, "fallthrough"),
                    (add, store, "fallthrough"),
                ]);
                prog.resolved_addr_to_symbol
                    .extend([(base, base as usize, 0), (addend, addend as usize, 0)]);
                prog
            };

            let mut raw_read = make_program(0x100, "PTEST", true);
            raw_read.run();
            assert!(raw_read
                .simd_dword_unsupported_use
                .iter()
                .any(|fact| fact == &(0x100, Mreg::X0)));
            assert!(raw_read
                .simd_dword_event_uncertain
                .iter()
                .any(|fact| fact == &(0x700,)));
            finalize_simd_dword_event_chains(&mut raw_read);
            assert!(raw_read.simd_dword_lane_event.is_empty());
            assert!(raw_read.simd_dword_lane_frame_store.is_empty());

            let mut zero_all = make_program(0x110, "VZEROALL", false);
            zero_all.run();
            assert!(zero_all
                .simd_dword_lane_barrier
                .iter()
                .any(|fact| fact == &(0x110,)));
            assert!(zero_all
                .simd_dword_event_uncertain
                .iter()
                .any(|fact| fact == &(0x700,)));
            finalize_simd_dword_event_chains(&mut zero_all);
            assert!(zero_all.simd_dword_lane_event.is_empty());
            assert!(zero_all.simd_dword_lane_frame_store.is_empty());

            let mut restored = make_program(0x120, "FXRSTOR64", false);
            restored.run();
            assert!(restored
                .simd_dword_lane_barrier
                .iter()
                .any(|fact| fact == &(0x120,)));
            assert!(restored
                .simd_dword_event_uncertain
                .iter()
                .any(|fact| fact == &(0x700,)));
            finalize_simd_dword_event_chains(&mut restored);
            assert!(restored.simd_dword_lane_event.is_empty());
            assert!(restored.simd_dword_lane_frame_store.is_empty());

            let load = 0x900;
            let store = 0x200;
            let ret = 0x50;
            let base = 0x404040;
            let mut live_at_return = AsmPassProgram::default();
            live_at_return
                .simd_dword_global_seed
                .push((load, Mreg::X0, base));
            live_at_return
                .simd_dword_frame_spill_site
                .push((store, Mreg::X0, -24));
            live_at_return.reg_def.push((load, Mreg::X0));
            live_at_return.reg_use.push((store, Mreg::X0));
            live_at_return.mach_inst.push((ret, MachInst::Mreturn));
            for node in [load, store, ret] {
                live_at_return.instr_in_function.push((node, load));
            }
            live_at_return
                .ddisasm_cfg_edge
                .extend([(load, store, "fallthrough"), (store, ret, "fallthrough")]);
            live_at_return
                .resolved_addr_to_symbol
                .push((base, base as usize, 0));

            live_at_return.run();
            assert!(live_at_return
                .simd_dword_event_use
                .iter()
                .any(|fact| fact == &(ret, load)));
            finalize_simd_dword_event_chains(&mut live_at_return);
            assert!(live_at_return.simd_dword_lane_event.is_empty());
            assert!(live_at_return.simd_dword_lane_frame_store.is_empty());

            let ax_def = 0x100;
            let mut integer_return = AsmPassProgram::default();
            integer_return
                .simd_dword_global_seed
                .push((load, Mreg::X0, base));
            integer_return
                .simd_dword_frame_spill_site
                .push((store, Mreg::X0, -24));
            integer_return
                .reg_def
                .extend([(load, Mreg::X0), (ax_def, Mreg::AX)]);
            integer_return.reg_use.push((store, Mreg::X0));
            integer_return.mach_inst.push((ret, MachInst::Mreturn));
            for node in [load, store, ax_def, ret] {
                integer_return.instr_in_function.push((node, load));
            }
            integer_return.ddisasm_cfg_edge.extend([
                (load, store, "fallthrough"),
                (store, ax_def, "fallthrough"),
                (ax_def, ret, "fallthrough"),
            ]);
            integer_return
                .resolved_addr_to_symbol
                .push((base, base as usize, 0));

            integer_return.run();
            assert!(integer_return
                .simd_gp_return_proven
                .iter()
                .any(|fact| fact == &(load,)));
            assert!(!integer_return
                .simd_dword_event_use
                .iter()
                .any(|fact| fact == &(ret, load)));
            finalize_simd_dword_event_chains(&mut integer_return);
            assert_eq!(
                integer_return.simd_dword_lane_event,
                vec![(load, 0, 0, base)]
            );
            assert_eq!(
                integer_return.simd_dword_lane_frame_store,
                vec![(store, -24, load)]
            );
        });
    }

    #[test]
    fn packed_dword_matcher_respects_avx_operands_and_legacy_alignment() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x400;
            let legacy_aligned = 0x900;
            let legacy_unaligned = 0x100;
            let avx_unaligned = 0x700;
            let avx_masked = 0x600;
            let masked_seed = 0x580;
            let masked_spill = 0x540;
            let masked_copy = 0x500;
            let unmasked_wide_store = 0x480;
            let spill = 0x200;
            let aligned_target = 0x404040;
            let dword_target = 0x404044;

            for (node, mem, dst, target) in [
                (
                    legacy_aligned,
                    "legacy_aligned_mem",
                    "legacy_aligned_dst",
                    aligned_target,
                ),
                (
                    legacy_unaligned,
                    "legacy_unaligned_mem",
                    "legacy_unaligned_dst",
                    dword_target,
                ),
            ] {
                prog.instruction
                    .push((node, 4, "", "PADDD", mem, dst, "", "", 0, 0));
                prog.op_indirect.push((mem, "", "RIP", "NONE", 1, 0, 16));
                prog.op_register.push((dst, "XMM0"));
                prog.rip_target_addr.push((node, target));
            }
            // Decoder convention after its operand swap is src1,dst,src2.
            prog.instruction.push((
                avx_unaligned,
                5,
                "",
                "VPADDD",
                "avx_input",
                "avx_dst",
                "avx_mem",
                "",
                0,
                0,
            ));
            prog.op_register
                .extend([("avx_input", "XMM1"), ("avx_dst", "XMM2")]);
            prog.op_indirect
                .push(("avx_mem", "", "RIP", "NONE", 1, 0, 16));
            prog.rip_target_addr.push((avx_unaligned, dword_target));

            prog.instruction.push((
                avx_masked,
                6,
                "",
                "VPADDD",
                "masked_input",
                "masked_dst",
                "masked_mem",
                "",
                0,
                0,
            ));
            prog.op_register
                .extend([("masked_input", "XMM1"), ("masked_dst", "XMM2")]);
            prog.op_indirect
                .push(("masked_mem", "", "RIP", "NONE", 1, 0, 16));
            prog.rip_target_addr.push((avx_masked, dword_target));
            prog.avx_masked_site.push((avx_masked,));

            // EVEX writemasks make a wide move lane-selective.  Neither a
            // partial/zero-masked load nor a masked store/copy is an exact
            // four-lane event, so all exact SIMD models must leave it alone.
            prog.instruction.push((
                masked_seed,
                7,
                "",
                "VMOVDQU",
                "masked_seed_mem",
                "masked_seed_dst",
                "",
                "",
                0,
                0,
            ));
            prog.op_indirect
                .push(("masked_seed_mem", "", "RIP", "NONE", 1, 0, 16));
            prog.op_register.push(("masked_seed_dst", "XMM3"));
            prog.rip_target_addr.push((masked_seed, aligned_target));

            prog.instruction.push((
                masked_spill,
                8,
                "",
                "VMOVDQU",
                "masked_spill_src",
                "masked_spill_mem",
                "",
                "",
                0,
                0,
            ));
            prog.op_register.push(("masked_spill_src", "XMM3"));
            prog.op_indirect
                .push(("masked_spill_mem", "", "RSP", "NONE", 1, -40, 16));
            prog.sp_frame_shift.push((masked_spill, 0));

            prog.instruction.push((
                masked_copy,
                9,
                "",
                "VMOVDQU",
                "masked_copy_src",
                "masked_copy_dst",
                "",
                "",
                0,
                0,
            ));
            prog.op_register
                .extend([("masked_copy_src", "XMM3"), ("masked_copy_dst", "XMM4")]);

            // Establish the high-lane analysis demand independently of the
            // masked store, so the negative seed/copy assertions exercise the
            // mask guards rather than short-circuiting on no consumer.
            prog.instruction.push((
                unmasked_wide_store,
                10,
                "",
                "MOVDQU",
                "wide_store_src",
                "wide_store_mem",
                "",
                "",
                0,
                0,
            ));
            prog.op_register.push(("wide_store_src", "XMM5"));
            prog.op_indirect
                .push(("wide_store_mem", "", "RSP", "NONE", 1, -64, 16));
            prog.sp_frame_shift.push((unmasked_wide_store, 0));

            prog.avx_masked_site
                .extend([(masked_seed,), (masked_spill,), (masked_copy,)]);

            prog.simd_dword_frame_spill_site
                .push((spill, Mreg::X2, -24));
            for node in [
                legacy_aligned,
                legacy_unaligned,
                avx_unaligned,
                avx_masked,
                masked_seed,
                masked_spill,
                masked_copy,
                unmasked_wide_store,
                spill,
            ] {
                prog.instr_in_function.push((node, func));
            }

            prog.run();

            assert!(prog
                .simd_dword_mem_binop
                .iter()
                .any(|fact| { fact == &(legacy_aligned, 1, Mreg::X0, Mreg::X0, aligned_target,) }));
            assert!(!prog
                .simd_dword_mem_binop
                .iter()
                .any(|(node, ..)| *node == legacy_unaligned));
            assert!(prog
                .simd_dword_mem_binop
                .iter()
                .any(|fact| { fact == &(avx_unaligned, 1, Mreg::X1, Mreg::X2, dword_target) }));
            assert!(!prog
                .simd_dword_mem_binop
                .iter()
                .any(|(node, ..)| *node == avx_masked));
            assert!(!prog
                .simd_dword_global_seed
                .iter()
                .any(|(node, ..)| *node == masked_seed));
            assert!(!prog
                .simd_dword_frame_spill_site
                .iter()
                .any(|(node, ..)| *node == masked_spill));
            assert!(!prog
                .simd_dword_reg_copy
                .iter()
                .any(|(node, ..)| *node == masked_copy));
            assert!(!prog
                .sse_wide_frame_store
                .iter()
                .any(|(node, ..)| *node == masked_spill));
            assert!(!prog
                .xmm_hi_seed
                .iter()
                .any(|(node, ..)| *node == masked_seed));
            assert!(!prog
                .xmm_hi_reg_copy
                .iter()
                .any(|(node, ..)| *node == masked_copy));
            assert!(prog
                .sse_wide_frame_store
                .iter()
                .any(|(node, ..)| *node == unmasked_wide_store));
        });
    }

    #[test]
    fn immediate_moves_require_absolute_data_address_evidence() {
        on_large_stack(|| {
            let code_literal = 0x100;
            let data_pointer = 0x110;
            let mut absolute = AsmPassProgram::default();
            absolute.raw_image_addresses_are_absolute.push((true,));
            absolute.symbols.push((0x2000, "FUN_2000", "Beg"));
            absolute.symbols.push((0x4000, "L_4000", "Beg"));
            absolute.data_section_range.push((0x4000, 0x5000));
            absolute.pmov.push((code_literal, "code_dst", "code_imm"));
            absolute.op_register.push(("code_dst", "EDX"));
            absolute.op_immediate.push(("code_imm", 0x2000, 4));
            absolute.pmov.push((data_pointer, "data_dst", "data_imm"));
            absolute.op_register.push(("data_dst", "ECX"));
            absolute.op_immediate.push(("data_imm", 0x4000, 4));

            absolute.run();

            assert!(absolute.mach_inst.iter().any(|(node, inst)| {
                *node == code_literal
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Ointconst(0x2000), args, Mreg::DX)
                            if args.is_empty()
                    )
            }));
            assert!(!absolute.mach_inst.iter().any(|(node, inst)| {
                *node == code_literal
                    && matches!(inst, MachInst::Mop(Operation::Oindirectsymbol(_), _, _))
            }));
            assert!(absolute.mach_inst.iter().any(|(node, inst)| {
                *node == data_pointer
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Oindirectsymbol(0x4000), args, Mreg::CX)
                            if args.is_empty()
                    )
            }));
            assert!(!absolute.mach_inst.iter().any(|(node, inst)| {
                *node == data_pointer
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Ointconst(_) | Operation::Olongconst(_), _, _)
                    )
            }));

            let pie_literal = 0x120;
            let mut pie = AsmPassProgram::default();
            pie.raw_image_addresses_are_absolute.push((false,));
            pie.symbols.push((0x4000, "L_4000", "Beg"));
            pie.data_section_range.push((0x4000, 0x5000));
            pie.pmov.push((pie_literal, "pie_dst", "pie_imm"));
            pie.op_register.push(("pie_dst", "EDX"));
            pie.op_immediate.push(("pie_imm", 0x4000, 4));

            pie.run();

            assert!(pie.mach_inst.iter().any(|(node, inst)| {
                *node == pie_literal
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Ointconst(0x4000), args, Mreg::DX)
                            if args.is_empty()
                    )
            }));
            assert!(!pie.mach_inst.iter().any(|(node, inst)| {
                *node == pie_literal
                    && matches!(inst, MachInst::Mop(Operation::Oindirectsymbol(_), _, _))
            }));
        });
    }

    #[test]
    fn one_register_absolute_data_displacement_keeps_symbolic_storage_identity() {
        on_large_stack(|| {
            const FUNC: Address = 0x900;
            const MASK: Address = 0x500;
            const SHIFT: Address = 0x100;
            const CALL: Address = 0x700;
            const LOAD_FIRST: Address = 0x300;
            const LOAD_SECOND: Address = 0x80;
            const TABLE: Address = 0x4000;

            let build = |raw_absolute: bool,
                         raw_base: &'static str,
                         mask_value: Option<i64>,
                         second_coordinate: Address,
                         call_barrier: bool| {
                let mut prog = AsmPassProgram::default();
                prog.raw_image_addresses_are_absolute.push((raw_absolute,));
                prog.data_section_range.push((TABLE, 0x6000));

                for node in [FUNC, MASK, SHIFT, LOAD_FIRST, LOAD_SECOND] {
                    prog.instr_in_function.push((node, FUNC));
                }
                if call_barrier {
                    prog.instr_in_function.push((CALL, FUNC));
                }

                prog.ddisasm_cfg_edge.push((FUNC, MASK, "fallthrough"));
                prog.ddisasm_cfg_edge.push((MASK, SHIFT, "fallthrough"));
                if call_barrier {
                    prog.ddisasm_cfg_edge.push((SHIFT, CALL, "fallthrough"));
                    prog.ddisasm_cfg_edge
                        .push((CALL, LOAD_FIRST, "fallthrough"));
                    prog.instruction
                        .push((CALL, 5, "", "CALL", "0", "0", "0", "0", 0, 0));
                } else {
                    prog.ddisasm_cfg_edge
                        .push((SHIFT, LOAD_FIRST, "fallthrough"));
                }
                prog.ddisasm_cfg_edge
                    .push((LOAD_FIRST, LOAD_SECOND, "fallthrough"));

                if let Some(mask_value) = mask_value {
                    prog.pand.push((MASK, "bounded_dst", "bounded_mask"));
                    prog.op_register.push(("bounded_dst", "EDI"));
                    prog.op_immediate.push(("bounded_mask", mask_value, 4));
                    prog.decoded_reg_def.push((MASK, Mreg::DI));
                }
                prog.psal.push((SHIFT, "scaled_dst", "scaled_shift"));
                prog.op_register.push(("scaled_dst", "EDI"));
                prog.op_immediate.push(("scaled_shift", 4, 1));
                prog.decoded_reg_def.push((SHIFT, Mreg::DI));

                for (node, memory, destination, target, result) in [
                    (
                        LOAD_FIRST,
                        "first_field_mem",
                        "first_field_dst",
                        TABLE,
                        Mreg::BX,
                    ),
                    (
                        LOAD_SECOND,
                        "second_field_mem",
                        "second_field_dst",
                        second_coordinate,
                        Mreg::R14,
                    ),
                ] {
                    prog.instruction.push((
                        node,
                        7,
                        "",
                        "MOV",
                        memory,
                        destination,
                        "0",
                        "0",
                        0,
                        0,
                    ));
                    prog.op_indirect
                        .push((memory, "", raw_base, "NONE", 1, target as i64, 8));
                    prog.transl_load.push((
                        node,
                        MemoryChunk::MAny64,
                        Addrmode {
                            base: Some(Ireg::RDI),
                            index: None,
                            disp: Displacement::Const(target as i64),
                        },
                        Arc::new(vec![Mreg::DI]),
                        result,
                    ));
                }

                prog.run();
                prog
            };

            let exact = build(true, "RDI", Some(3), TABLE + 8, false);
            let mut certificates: Vec<_> = exact
                .bounded_absolute_data_access
                .iter()
                .filter(|(func, ..)| *func == FUNC)
                .copied()
                .collect();
            certificates.sort_unstable();
            assert_eq!(
                certificates,
                vec![
                    (FUNC, LOAD_SECOND, TABLE as Ident, 8, 16, 4, MASK, 8,),
                    (FUNC, LOAD_FIRST, TABLE as Ident, 0, 16, 4, MASK, 8,),
                ]
            );
            assert!(exact
                .global_symbol
                .iter()
                .any(|fact| fact == &(TABLE, "TABLE_4000")));
            assert!(!exact
                .global_symbol
                .iter()
                .any(|(address, _)| *address == TABLE + 8));
            for (node, offset, result) in [(LOAD_FIRST, 0, Mreg::BX), (LOAD_SECOND, 8, Mreg::R14)] {
                assert!(exact.mach_inst.iter().any(|(actual_node, inst)| {
                    *actual_node == node
                        && matches!(
                            inst,
                            MachInst::Mload(
                                MemoryChunk::MAny64,
                                Addressing::Abased(owner, actual_offset),
                                args,
                                actual_result,
                            ) if *owner == TABLE as Ident
                                && *actual_offset == offset
                                && args.as_slice() == [Mreg::DI]
                                && *actual_result == result
                        )
                }));
                assert!(!exact.mach_inst.iter().any(|(actual_node, inst)| {
                    *actual_node == node
                        && matches!(inst, MachInst::Mload(_, Addressing::Aindexed(_), _, _))
                }));
            }

            // Every negative retains ordinary numeric addressing.  Section
            // membership alone, an address-size override, a non-contiguous
            // mask, a call barrier, ET_DYN encoding, or two distant tables is
            // insufficient to invent storage ownership.
            for (case, numeric) in [
                ("no bound", build(true, "RDI", None, TABLE + 8, false)),
                (
                    "address-size override",
                    build(true, "EDI", Some(3), TABLE + 8, false),
                ),
                (
                    "non-contiguous mask",
                    build(true, "RDI", Some(5), TABLE + 8, false),
                ),
                ("call barrier", build(true, "RDI", Some(3), TABLE + 8, true)),
                (
                    "position-independent image",
                    build(false, "RDI", Some(3), TABLE + 8, false),
                ),
                ("distant tables", build(true, "RDI", Some(3), 0x5000, false)),
            ] {
                assert!(
                    numeric.bounded_absolute_data_access.is_empty(),
                    "{case} unexpectedly acquired a bounded owner"
                );
                assert!(
                    numeric.global_symbol.is_empty(),
                    "{case} unexpectedly acquired a global symbol"
                );
                for node in [LOAD_FIRST, LOAD_SECOND] {
                    assert!(
                        numeric.mach_inst.iter().any(|(actual_node, inst)| {
                            *actual_node == node
                                && matches!(inst, MachInst::Mload(_, Addressing::Aindexed(_), _, _))
                        }),
                        "{case} lost its numeric load at {node:#x}"
                    );
                }
            }

            // Two alternate masks establish different provenance tokens.  A
            // structural CFG join therefore becomes Top even though both
            // happen to have the same numeric mask and shift.
            let mut branch_join = AsmPassProgram::default();
            let left = 0x610;
            let right = 0x220;
            branch_join.raw_image_addresses_are_absolute.push((true,));
            branch_join.data_section_range.push((TABLE, 0x6000));
            for node in [FUNC, left, right, SHIFT, LOAD_FIRST] {
                branch_join.instr_in_function.push((node, FUNC));
            }
            branch_join.ddisasm_cfg_edge.push((FUNC, left, "branch"));
            branch_join
                .ddisasm_cfg_edge
                .push((FUNC, right, "fallthrough"));
            branch_join
                .ddisasm_cfg_edge
                .push((left, SHIFT, "fallthrough"));
            branch_join
                .ddisasm_cfg_edge
                .push((right, SHIFT, "fallthrough"));
            branch_join
                .ddisasm_cfg_edge
                .push((SHIFT, LOAD_FIRST, "fallthrough"));
            for (node, dst, immediate) in [
                (left, "left_mask_dst", "left_mask"),
                (right, "right_mask_dst", "right_mask"),
            ] {
                branch_join.pand.push((node, dst, immediate));
                branch_join.op_register.push((dst, "EDI"));
                branch_join.op_immediate.push((immediate, 3, 4));
                branch_join.decoded_reg_def.push((node, Mreg::DI));
            }
            branch_join
                .psal
                .push((SHIFT, "join_shift_dst", "join_shift"));
            branch_join.op_register.push(("join_shift_dst", "EDI"));
            branch_join.op_immediate.push(("join_shift", 4, 1));
            branch_join.decoded_reg_def.push((SHIFT, Mreg::DI));
            branch_join.instruction.push((
                LOAD_FIRST, 7, "", "MOV", "join_mem", "join_dst", "0", "0", 0, 0,
            ));
            branch_join
                .op_indirect
                .push(("join_mem", "", "RDI", "NONE", 1, TABLE as i64, 8));
            branch_join.transl_load.push((
                LOAD_FIRST,
                MemoryChunk::MAny64,
                Addrmode {
                    base: Some(Ireg::RDI),
                    index: None,
                    disp: Displacement::Const(TABLE as i64),
                },
                Arc::new(vec![Mreg::DI]),
                Mreg::BX,
            ));
            branch_join.run();
            assert!(branch_join.bounded_absolute_data_access.is_empty());
            assert!(branch_join.mach_inst.iter().any(|(node, inst)| {
                *node == LOAD_FIRST
                    && matches!(inst, MachInst::Mload(_, Addressing::Aindexed(_), _, _))
            }));
        });
    }

    #[test]
    fn scheduled_setcc_def_is_emitted_at_setcc_not_compare() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let compare = 0x900;
            let independent = 0x100;
            let setcc = 0x800;

            prog.pcmp.push((compare, "cmp_value", "cmp_five"));
            prog.op_register.push(("cmp_value", "EAX"));
            prog.op_immediate.push(("cmp_five", 5, 4));
            prog.next.push((compare, independent));
            prog.instruction.push((
                independent,
                3,
                "",
                "LEA",
                "lea_src",
                "lea_dst",
                "0",
                "0",
                0,
                0,
            ));
            prog.next.push((independent, setcc));
            prog.psetcc.push((setcc, TestCond::CondE, "setcc_dst"));
            prog.op_register.push(("setcc_dst", "AL"));

            prog.run();

            assert!(prog
                .setcc_compare_site
                .iter()
                .any(|fact| fact == &(setcc, compare)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == setcc
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Ocmp(_), args, Mreg::AX)
                            if args.as_slice() == [Mreg::AX]
                    )
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == compare && matches!(inst, MachInst::Mop(Operation::Ocmp(_), _, _))
            }));
        });
    }

    #[test]
    fn scheduled_setcc_to_stack_preserves_flags_origin_and_exact_cell() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x500;
            let test = 0x900;
            let first_gap = 0x100;
            let second_gap = 0x800;
            let setcc = 0x200;
            let block = 0x777;

            // Execution order is intentionally unrelated to numeric order.
            // The two intervening MOVs may replace EBX while TEST's flags stay
            // live; the SETcc condition must therefore retain `test` as its
            // operand-resolution point.
            prog.func_span.push(("f", func, 0xa00));
            for node in [func, test, first_gap, second_gap, setcc] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, block));
            }
            prog.next.extend([
                (func, test),
                (test, first_gap),
                (first_gap, second_gap),
                (second_gap, setcc),
            ]);

            prog.ptest.push((test, "tested_ebx", "tested_ebx_2"));
            prog.op_register
                .extend([("tested_ebx", "EBX"), ("tested_ebx_2", "EBX")]);
            for (node, src, dst) in [
                (first_gap, "gap1_src", "gap1_dst"),
                (second_gap, "gap2_src", "gap2_dst"),
            ] {
                prog.instruction
                    .push((node, 3, "", "MOV", src, dst, "", "", 0, 0));
            }
            prog.psetcc.push((setcc, TestCond::CondNe, "frame_boolean"));
            prog.op_indirect
                .push(("frame_boolean", "", "RSP", "NONE", 1, 50, 1));

            prog.run();

            let expected = (
                setcc,
                50,
                test,
                Operation::Ocmp(Condition::Ccompimm(Comparison::Cne, 0)),
                Arc::new(vec![Mreg::BX]),
            );
            assert!(prog.mach_stack_setcc.iter().any(|fact| fact == &expected));
            assert!(prog
                .setcc_compare_site
                .iter()
                .any(|fact| fact == &(setcc, test)));
            assert!(prog
                .node_unlowered_side_effect
                .iter()
                .any(|fact| fact == &(setcc,)));
            assert!(!prog.mach_inst.iter().any(|(node, _)| *node == setcc));
        });
    }

    #[test]
    fn register_setcc_crosses_three_flag_transparent_instructions() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [test, first_move, second_move, cmov, setcc, block] = synthetic_ids();

            prog.ptest.push((test, "tested_edi", "tested_edi_again"));
            prog.op_register
                .extend([("tested_edi", "EDI"), ("tested_edi_again", "EDI")]);
            for (node, mnemonic) in [(first_move, "MOV"), (second_move, "MOV"), (cmov, "CMOVG")] {
                let row = (node, 3, "", mnemonic, "", "", "", "", 0, 0);
                prog.instruction.push(row);
                prog.unrefinedinstruction.push(row);
            }
            prog.psetcc.push((setcc, TestCond::CondG, "boolean_cl"));
            prog.op_register.push(("boolean_cl", "CL"));
            prog.next.extend([
                (test, first_move),
                (first_move, second_move),
                (second_move, cmov),
                (cmov, setcc),
            ]);
            for node in [test, first_move, second_move, cmov, setcc] {
                prog.code_in_block.push((node, block));
            }

            prog.run();

            assert!(prog
                .test_setcc_link
                .iter()
                .any(|fact| fact == &(test, setcc)));
            assert!(prog
                .setcc_compare_site
                .iter()
                .any(|fact| fact == &(setcc, test)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == setcc
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Ocmp(Condition::Ccompimm(Comparison::Cgt, 0)),
                            args,
                            Mreg::CX,
                        ) if args.as_slice() == [Mreg::DI]
                    )
            }));
        });
    }

    #[test]
    fn register_tailcall_publishes_target_use_at_semantic_anchor() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let restore = 0x1000;
            let physical_jump = 0x1004;

            prog.padd.push((restore, "rsp", "restore_size"));
            prog.op_register.push(("rsp", "RSP"));
            prog.op_immediate.push(("restore_size", 32, 4));
            prog.next.push((restore, physical_jump));
            prog.pjmp.push((physical_jump, "target"));
            prog.op_register.push(("target", "R12"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == restore
                    && matches!(inst, MachInst::Mtailcall(either::Either::Left(Mreg::R12)))
            }));
            assert!(prog
                .reg_use
                .iter()
                .any(|fact| fact == &(restore, Mreg::R12)));
            assert_ne!(restore, physical_jump);
        });
    }

    #[test]
    fn memory_jumps_are_tailcalls_only_when_not_classified_as_jump_tables() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let tail = 0x1800;
            let table = 0x1810;
            let unresolved_indexed = 0x1820;

            for (node, operand) in [
                (tail, "tail_slot"),
                (table, "table_slot"),
                (unresolved_indexed, "unresolved_table_slot"),
            ] {
                prog.instruction
                    .push((node, 6, "", "JMP", operand, "", "", "", 0, 0));
                let index = if node == unresolved_indexed {
                    "RAX"
                } else {
                    "NONE"
                };
                let scale = if node == unresolved_indexed { 8 } else { 1 };
                prog.op_indirect
                    .push((operand, "", "R12", index, scale, 24, 8));
            }
            prog.jump_table_target.push((table, 0, 0x1900));
            prog.jump_table_target.push((table, 1, 0x1910));

            prog.run();

            assert!(prog
                .is_memory_tailcall_jmp
                .iter()
                .any(|(node,)| *node == tail));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == tail
                    && matches!(
                        inst,
                        MachInst::Mtailcall(either::Either::Left(Mreg::Unknown))
                    )
            }));
            assert!(!prog
                .mach_inst
                .iter()
                .any(|(node, inst)| *node == tail && matches!(inst, MachInst::Mgoto(_))));

            assert!(!prog
                .is_memory_tailcall_jmp
                .iter()
                .any(|(node,)| *node == table));
            assert!(prog
                .mach_inst
                .iter()
                .any(|(node, inst)| *node == table && matches!(inst, MachInst::Mgoto(_))));
            assert!(!prog
                .is_memory_tailcall_jmp
                .iter()
                .any(|(node,)| *node == unresolved_indexed));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == unresolved_indexed && matches!(inst, MachInst::Mgoto(_))
            }));
        });
    }

    #[test]
    fn base_less_memory_calls_survive_until_rtl_address_normalization() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let absolute = 0x2000;
            let indexed = 0x2010;
            let resolved = 0x2020;

            for (node, operand) in [
                (absolute, "absolute_slot"),
                (indexed, "indexed_slot"),
                (resolved, "resolved_slot"),
            ] {
                prog.instruction
                    .push((node, 6, "", "CALL", operand, "", "", "", 0, 0));
            }
            prog.op_indirect
                .push(("absolute_slot", "", "NONE", "NONE", 1, 0x404000, 8));
            prog.op_indirect
                .push(("indexed_slot", "", "NONE", "RAX", 8, 0x405000, 8));
            prog.op_indirect
                .push(("resolved_slot", "", "NONE", "NONE", 1, 0x406000, 8));
            prog.data_section_range.push((0x400000, 0x410000));
            prog.pointer_to_external_symbol
                .push((0x406000, "external_target"));

            prog.run();

            for node in [absolute, indexed] {
                let calls: Vec<_> = prog
                    .mach_inst
                    .iter()
                    .filter(|(site, _)| *site == node)
                    .collect();
                assert_eq!(calls.len(), 1, "site {node:#x}: {calls:?}");
                assert!(matches!(
                    calls[0].1,
                    MachInst::Mcall(either::Either::Left(Mreg::Unknown))
                ));
            }

            let resolved_calls: Vec<_> = prog
                .mach_inst
                .iter()
                .filter(|(site, _)| *site == resolved)
                .collect();
            assert_eq!(resolved_calls.len(), 1, "{resolved_calls:?}");
            assert!(matches!(
                resolved_calls[0].1,
                MachInst::Mcall(either::Either::Right(either::Either::Left(
                    "external_target"
                )))
            ));
        });
    }

    #[test]
    fn test_cmov_uses_cfg_flags_origin_across_setcc() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [test, setcc, cmov, block] = synthetic_ids();

            prog.ptest.push((test, "test_lhs", "test_rhs"));
            prog.op_register.push(("test_lhs", "EDI"));
            prog.op_register.push(("test_rhs", "EDI"));

            // SETcc reads the flags but does not overwrite them.
            prog.psetcc.push((setcc, TestCond::CondG, "bool_dst"));
            prog.op_register.push(("bool_dst", "DL"));

            prog.pcmov
                .push((cmov, TestCond::CondLe, "select_dst", "select_src"));
            prog.op_register.push(("select_dst", "EAX"));
            prog.op_register.push(("select_src", "ECX"));

            prog.next.push((test, setcc));
            prog.next.push((setcc, cmov));
            for node in [test, setcc, cmov] {
                prog.code_in_block.push((node, block));
            }

            prog.run();

            assert!(prog
                .osel_compare_site
                .iter()
                .any(|fact| fact == &(cmov, test)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == cmov
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Osel(
                                Condition::Ccompimm(Comparison::Cgt, 0),
                                Typ::Tint
                            ),
                            args,
                            Mreg::AX
                        ) if args.as_slice() == [Mreg::AX, Mreg::CX, Mreg::DI]
                    )
            }));
        });
    }

    #[test]
    fn masked_memory_test_cmov_exports_a_two_value_select() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            // Reverse numeric order deliberately: the TEST reaches CMOV via
            // the CFG flags lattice, never by comparing instruction ids.
            let test = 0x900;
            let cmov = 0x100;
            let block = 0x500;

            prog.ptest.push((test, "stream_flags", "mask"));
            prog.op_indirect
                .push(("stream_flags", "", "RBP", "NONE", 1, 0, 1));
            prog.op_immediate.push(("mask", 0x20, 1));
            prog.pcmov
                .push((cmov, TestCond::CondE, "saved_errno", "zero"));
            prog.op_register.push(("saved_errno", "R13D"));
            prog.op_register.push(("zero", "EAX"));
            prog.next.push((test, cmov));
            prog.code_in_block.push((test, block));
            prog.code_in_block.push((cmov, block));

            prog.run();

            assert!(prog
                .osel_compare_site
                .iter()
                .any(|fact| fact == &(cmov, test)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == cmov
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Osel(Condition::Cmasknotzero(0x20), Typ::Tint),
                            args,
                            Mreg::R13
                        ) if args.as_slice() == [Mreg::R13, Mreg::AX]
                    )
            }));
        });
    }

    #[test]
    fn rip_relative_compare_exports_its_cmov_condition_site() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            // Reverse numeric order deliberately: the flags link is derived
            // from the CFG, never from address magnitude.
            let compare = 0x900;
            let cmov = 0x500;
            let block = 0x100;

            prog.pcmp.push((compare, "global_word", "zero"));
            prog.op_indirect
                .push(("global_word", "", "RIP", "NONE", 1, 0x40, 4));
            prog.op_immediate.push(("zero", 0, 4));
            prog.pcmov
                .push((cmov, TestCond::CondNe, "select_dst", "select_src"));
            prog.op_register.push(("select_dst", "RSI"));
            prog.op_register.push(("select_src", "RAX"));
            prog.next.push((compare, cmov));
            prog.code_in_block.push((compare, block));
            prog.code_in_block.push((cmov, block));

            prog.run();

            assert!(prog
                .osel_compare_site
                .iter()
                .any(|fact| fact == &(cmov, compare)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == cmov
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Osel(
                                Condition::Ccompl(Comparison::Ceq),
                                Typ::Tany64
                            ),
                            args,
                            Mreg::SI
                        ) if args.as_slice() == [Mreg::SI, Mreg::AX]
                    )
            }));
        });
    }

    #[test]
    fn jo_and_jno_recover_exact_wrapping_arithmetic_conditions() {
        on_large_stack(|| {
            for (mnemonic, expected) in [
                ("JO", Condition::Carithoverflow(OverflowArithmetic::Add, 8)),
                (
                    "JNO",
                    Condition::Cnarithoverflow(OverflowArithmetic::Add, 8),
                ),
            ] {
                let mut prog = AsmPassProgram::default();
                // Reverse numeric order deliberately.  The proof follows the
                // structural CFG, never an address comparison.
                let origin = 0x900;
                let jcc = 0x100;
                let func = 0x5000;
                let block = 0x7000;

                prog.padd.push((origin, "sum", "rhs"));
                prog.op_register.extend([("sum", "RDI"), ("rhs", "RSI")]);
                prog.instruction
                    .push((jcc, 2, "", mnemonic, "overflow_target", "", "", "", 0, 0));
                prog.next.push((origin, jcc));
                for node in [origin, jcc] {
                    prog.code_in_block.push((node, block));
                    prog.instr_in_function.push((node, func));
                }

                prog.run();

                assert!(prog.mach_inst.iter().any(|(node, inst)| {
                    *node == jcc
                        && matches!(
                            inst,
                            MachInst::Mcond(condition, args, "overflow_target")
                                if condition == &expected
                                    && args.as_slice() == [Mreg::DI, Mreg::SI]
                        )
                }));
                assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                    *node == jcc
                        && matches!(
                            inst,
                            MachInst::Mcond(Condition::Coverflow | Condition::Cnotoverflow, _, _)
                        )
                }));
                assert!(prog.reg_use.iter().any(|fact| fact == &(jcc, Mreg::DI)));
                assert!(prog.reg_use.iter().any(|fact| fact == &(jcc, Mreg::SI)));
            }

            let mut immediate = AsmPassProgram::default();
            let [origin, jcc, func, block] = synthetic_ids();
            immediate.psub.push((origin, "difference", "one"));
            immediate.op_register.push(("difference", "EAX"));
            immediate.op_immediate.push(("one", 1, 1));
            immediate
                .instruction
                .push((jcc, 2, "", "JNO", "no_overflow_target", "", "", "", 0, 0));
            immediate.next.push((origin, jcc));
            for node in [origin, jcc] {
                immediate.code_in_block.push((node, block));
                immediate.instr_in_function.push((node, func));
            }

            immediate.run();

            assert!(immediate.mach_inst.iter().any(|(node, inst)| {
                *node == jcc
                    && matches!(
                        inst,
                        MachInst::Mcond(
                            Condition::Cnarithoverflow(
                                OverflowArithmetic::SubImmediate(1),
                                4
                            ),
                            args,
                            "no_overflow_target"
                        ) if args.as_slice() == [Mreg::AX]
                    )
            }));
            assert!(!immediate.mach_inst.iter().any(|(_, inst)| matches!(
                inst,
                MachInst::Mcond(Condition::Coverflow | Condition::Cnotoverflow, _, _)
            )));
            assert!(
                !immediate.pjcc.iter().any(|(node, _, _)| *node == jcc),
                "OF-only jumps must not activate legacy comparison-JCC rules"
            );
        });
    }

    #[test]
    fn exact_overflow_rejects_redefined_partial_same_register_and_missing_owner_cases() {
        on_large_stack(|| {
            #[derive(Clone, Copy)]
            enum InvalidShape {
                RedefinedSource,
                PartialWidth,
                SameRegister,
                MissingOwner,
            }

            for invalid in [
                InvalidShape::RedefinedSource,
                InvalidShape::PartialWidth,
                InvalidShape::SameRegister,
                InvalidShape::MissingOwner,
            ] {
                let mut prog = AsmPassProgram::default();
                let [origin, shadow, jcc, func, other_func, block] = synthetic_ids();
                let (dst_view, src_view) = match invalid {
                    InvalidShape::PartialWidth => ("AX", "BX"),
                    InvalidShape::SameRegister => ("RDI", "RDI"),
                    _ => ("RDI", "RSI"),
                };

                prog.padd.push((origin, "sum", "rhs"));
                prog.op_register
                    .extend([("sum", dst_view), ("rhs", src_view)]);
                prog.instruction
                    .push((jcc, 2, "", "JO", "overflow_target", "", "", "", 0, 0));

                if matches!(invalid, InvalidShape::RedefinedSource) {
                    prog.next.extend([(origin, shadow), (shadow, jcc)]);
                    for node in [origin, shadow, jcc] {
                        prog.code_in_block.push((node, block));
                        prog.instr_in_function.push((node, func));
                    }
                    prog.unrefinedinstruction.push((
                        shadow,
                        3,
                        "",
                        "MOV",
                        "shadow_dst",
                        "shadow_src",
                        "",
                        "",
                        0,
                        0,
                    ));
                    prog.reg_def.push((shadow, Mreg::SI));
                } else {
                    prog.next.push((origin, jcc));
                    for node in [origin, jcc] {
                        prog.code_in_block.push((node, block));
                        prog.instr_in_function.push((node, func));
                    }
                }

                if matches!(invalid, InvalidShape::MissingOwner) {
                    prog.instr_in_function.push((jcc, other_func));
                }

                prog.run();

                assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                    *node == jcc
                        && matches!(
                            inst,
                            MachInst::Mcond(
                                Condition::Carithoverflow(..) | Condition::Cnarithoverflow(..),
                                _,
                                _
                            )
                        )
                }));
                assert!(prog.mach_inst.iter().any(|(node, inst)| {
                    *node == jcc
                        && matches!(
                            inst,
                            MachInst::Mcond(Condition::Coverflow, args, "overflow_target")
                                if args.is_empty()
                        )
                }));
            }
        });
    }

    #[test]
    fn unknown_flags_arm_vetoes_exact_overflow_origin() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [origin, unknown_kill, jcc, func, left_block, right_block, join_block] =
                synthetic_ids();

            prog.padd.push((origin, "sum", "rhs"));
            prog.op_register.extend([("sum", "RDI"), ("rhs", "RSI")]);
            prog.instruction
                .push((jcc, 2, "", "JO", "overflow_target", "", "", "", 0, 0));
            // MUL is deliberately not one of linked_flags_origin's modeled
            // producers.  It clobbers flags, so this path must contribute
            // explicit Unknown rather than disappear at the join.
            prog.unrefinedinstruction.push((
                unknown_kill,
                3,
                "",
                "MUL",
                "factor",
                "",
                "",
                "",
                0,
                0,
            ));
            prog.ddisasm_cfg_edge.extend([
                (origin, jcc, "branch"),
                (origin, unknown_kill, "fallthrough"),
                (unknown_kill, jcc, "branch"),
            ]);
            for (node, block) in [
                (origin, left_block),
                (unknown_kill, right_block),
                (jcc, join_block),
            ] {
                prog.code_in_block.push((node, block));
                prog.instr_in_function.push((node, func));
            }

            prog.run();

            assert!(!prog.exact_overflow_condition.iter().any(|row| row.0 == jcc));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == jcc
                    && matches!(
                        inst,
                        MachInst::Mcond(Condition::Coverflow, args, "overflow_target")
                            if args.is_empty()
                    )
            }));
        });
    }

    #[test]
    fn decrement_branch_uses_the_updated_counter_at_the_jcc() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [decrement, jcc, block] = synthetic_ids();

            prog.instruction
                .push((decrement, 1, "", "DEC", "counter", "", "", "", 0, 0));
            prog.op_register.push(("counter", "ECX"));
            prog.pjcc.push((jcc, TestCond::CondNe, "loop_head"));
            prog.next.push((decrement, jcc));
            prog.code_in_block.push((decrement, block));
            prog.code_in_block.push((jcc, block));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == jcc
                    && matches!(
                        inst,
                        MachInst::Mcond(
                            Condition::Ccompimm(Comparison::Cne, 0),
                            args,
                            "loop_head"
                        ) if args.as_slice() == [Mreg::CX]
                    )
            }));
        });
    }

    #[test]
    fn sub_result_cmov_tests_the_post_subtract_value() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [subtract, cmov, block] = synthetic_ids();

            prog.psub.push((subtract, "sub_result", "sub_rhs"));
            prog.op_register.push(("sub_result", "ESI"));
            prog.op_register.push(("sub_rhs", "EDI"));
            prog.pcmov
                .push((cmov, TestCond::CondGe, "select_dst", "select_src"));
            prog.op_register.push(("select_dst", "EAX"));
            prog.op_register.push(("select_src", "ESI"));
            prog.next.push((subtract, cmov));
            prog.code_in_block.push((subtract, block));
            prog.code_in_block.push((cmov, block));

            prog.run();

            assert!(!prog.osel_compare_site.iter().any(|(node, _)| *node == cmov));
            assert!(prog
                .osel_flags_result_site
                .iter()
                .any(|fact| fact == &(cmov, subtract)));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == cmov
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Osel(
                                Condition::Ccompimm(Comparison::Clt, 0),
                                Typ::Tint
                            ),
                            args,
                            Mreg::AX
                        ) if args.as_slice() == [Mreg::AX, Mreg::SI, Mreg::SI]
                    )
            }));
        });
    }

    #[test]
    fn frame_reference_below_the_frame_origin_names_the_cell_not_the_raw_slot() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x100;
            let alloc = 0x110;
            let settled_load = 0x118;
            let origin_call = 0x120;
            let push = 0x130;
            let window_load = 0x140;
            let arg_call = 0x150;
            let block = 0x100;

            prog.arch_bit.push((64,));
            prog.func_span.push(("f", func, 0x200));
            prog.block_in_function.push((block, func));
            for addr in [
                func,
                alloc,
                settled_load,
                origin_call,
                push,
                window_load,
                arg_call,
            ] {
                prog.code_in_block.push((addr, block));
            }
            for edge in [
                (func, alloc),
                (alloc, settled_load),
                (settled_load, origin_call),
                (origin_call, push),
                (push, window_load),
                (window_load, arg_call),
            ] {
                prog.next.push(edge);
            }

            // sub $0x20,%rsp: the frame, and with it the coordinate origin.
            prog.psub.push((alloc, "rsp_op", "alloc_sz"));
            prog.op_register.push(("rsp_op", "RSP"));
            prog.op_immediate.push(("alloc_sz", 0x20, 4));

            // A call passing everything in registers sits exactly at the origin.
            prog.instruction
                .push((origin_call, 5, "", "CALL", "callee", "0", "0", "0", 0, 0));
            prog.instruction
                .push((arg_call, 5, "", "CALL", "callee", "0", "0", "0", 0, 0));

            // push %rbx opens an outgoing-argument window eight bytes deep.
            prog.ppush.push((push, "push_op"));
            prog.op_register.push(("push_op", "RBX"));

            // mov 0x18(%rsp),%rax before the push already names cell 0x18.
            prog.pmov.push((settled_load, "settled_dst", "settled_mem"));
            prog.op_register.push(("settled_dst", "RCX"));
            prog.op_indirect
                .push(("settled_mem", "", "RSP", "NONE", 1, 0x18, 8));

            // The same displacement inside the window names cell 0x10.
            prog.pmov.push((window_load, "load_dst", "load_mem"));
            prog.op_register.push(("load_dst", "RAX"));
            prog.op_indirect
                .push(("load_mem", "", "RSP", "NONE", 1, 0x18, 8));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == settled_load && matches!(inst, MachInst::Mgetstack(0x18, _, Mreg::CX))
            }));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == window_load && matches!(inst, MachInst::Mgetstack(0x10, _, Mreg::AX))
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == window_load && matches!(inst, MachInst::Mgetstack(0x18, _, _))
            }));
        });
    }

    #[test]
    fn movhps_preserves_low_lane_and_exports_memory_bases() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let sp_load = 0x100;
            let general_load = 0x200;
            let bp_func = 0x300;
            let bp_setup = 0x301;
            let bp_load = 0x310;
            let rip_load = 0x400;

            prog.func_span.push(("sp", sp_load, 0x180));
            prog.instr_in_function.push((sp_load, sp_load));
            prog.func_span.push(("bp", bp_func, 0x380));
            prog.instr_in_function.push((bp_setup, bp_func));
            prog.instr_in_function.push((bp_load, bp_func));
            prog.stack_base_move.push((bp_setup, "RSP", "RBP"));

            for (addr, src, dst, base, disp) in [
                (sp_load, "sp_mem", "sp_xmm", "RSP", 24),
                (general_load, "gen_mem", "gen_xmm", "RAX", 32),
                (bp_load, "bp_mem", "bp_xmm", "RBP", -48),
                (rip_load, "rip_mem", "rip_xmm", "RIP", 64),
            ] {
                prog.instruction
                    .push((addr, 5, "", "MOVHPS", src, dst, "", "", 0, 0));
                prog.op_indirect.push((src, "", base, "NONE", 1, disp, 8));
            }
            for (sym, reg) in [
                ("sp_xmm", "XMM0"),
                ("gen_xmm", "XMM1"),
                ("bp_xmm", "XMM2"),
                ("rip_xmm", "XMM3"),
            ] {
                prog.op_register.push((sym, reg));
            }

            prog.run();

            for fact in [
                (sp_load, Mreg::X0, "RSP", "NONE", 1, 24, true),
                (general_load, Mreg::X1, "RAX", "NONE", 1, 32, false),
                (bp_load, Mreg::X2, "RBP", "NONE", 1, -48, true),
                (rip_load, Mreg::X3, "RIP", "NONE", 1, 64, false),
            ] {
                assert!(prog.movhps_hi_load.iter().any(|row| row == &fact));
            }
            for (addr, dst) in [
                (sp_load, Mreg::X0),
                (general_load, Mreg::X1),
                (bp_load, Mreg::X2),
                (rip_load, Mreg::X3),
            ] {
                assert!(prog.mach_inst.iter().any(|(node, inst)| {
                    *node == addr
                        && matches!(inst, MachInst::Mop(Operation::Omove, args, out)
                            if args.as_slice() == [dst] && *out == dst)
                }));
            }
        });
    }

    #[test]
    fn wide_simd_spill_reload_preserves_lane_provenance_at_join() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x500;
            // Deliberately non-monotone node ids: both paths are connected
            // solely by explicit CFG edges and stack reaching definitions.
            let bp_setup = 0x510;
            let interleave = 0x900;
            let direct = 0x100;
            let spill = 0x800;
            let call = 0x200;
            let reload = 0x700;
            let store = 0x300;
            let frame_ofs = -0x30;

            prog.stack_base_move.push((bp_setup, "RSP", "RBP"));
            prog.instruction.push((
                interleave,
                4,
                "",
                "PUNPCKLQDQ",
                "interleave_src",
                "interleave_dst",
                "0",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("interleave_src", "XMM0"));
            prog.op_register.push(("interleave_dst", "XMM0"));
            prog.reg_def.push((interleave, Mreg::X0));

            prog.instruction.push((
                spill,
                5,
                "",
                "MOVAPS",
                "spill_xmm",
                "spill_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((spill, "spill_mem", "spill_xmm"));
            prog.op_register.push(("spill_xmm", "XMM0"));
            prog.op_indirect
                .push(("spill_mem", "", "RBP", "NONE", 1, frame_ofs, 16));

            prog.instruction
                .push((call, 5, "", "CALL", "callee", "0", "0", "0", 0, 0));

            prog.instruction.push((
                reload,
                5,
                "",
                "MOVDQA",
                "reload_mem",
                "reload_xmm",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((reload, "reload_xmm", "reload_mem"));
            prog.op_indirect
                .push(("reload_mem", "", "RBP", "NONE", 1, frame_ofs, 16));
            prog.op_register.push(("reload_xmm", "XMM0"));
            prog.reg_def.push((reload, Mreg::X0));

            prog.instruction.push((
                store,
                4,
                "",
                "MOVUPS",
                "store_xmm",
                "store_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((store, "store_mem", "store_xmm"));
            prog.op_register.push(("store_xmm", "XMM0"));
            prog.op_indirect
                .push(("store_mem", "", "RAX", "NONE", 1, 0x20, 16));

            prog.stack_def.push((spill, "RBP", frame_ofs + 8));
            for edge in [
                (func, bp_setup),
                (bp_setup, interleave),
                (interleave, direct),
                (interleave, spill),
                (direct, store),
                (spill, call),
                (call, reload),
                (reload, store),
            ] {
                prog.ddisasm_cfg_edge.push((edge.0, edge.1, "fallthrough"));
            }
            for node in [
                func, bp_setup, interleave, direct, spill, call, reload, store,
            ] {
                prog.instr_in_function.push((node, func));
            }

            prog.run();

            let resolved: Vec<_> = prog
                .xmm_hi_mem_store
                .iter()
                .filter(|(addr, _, _, _, _)| *addr == store)
                .collect();
            assert_eq!(resolved.len(), 1, "unexpected lane sources: {resolved:?}");
            assert_eq!(
                resolved[0],
                &(store, 1, Mreg::X0, 0, interleave),
                "the spill/reload path must retain the direct path's provenance"
            );
        });
    }

    #[test]
    fn self_pcmpeqd_wide_store_recovers_both_all_ones_lanes() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x500;
            let compare = 0x900;
            let store = 0x100;

            prog.instruction.push((
                compare,
                4,
                "",
                "PCMPEQD",
                "compare_src",
                "compare_dst",
                "0",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("compare_src", "XMM0"));
            prog.op_register.push(("compare_dst", "XMM0"));
            prog.reg_def.push((compare, Mreg::X0));

            prog.instruction.push((
                store,
                4,
                "",
                "MOVUPS",
                "store_xmm",
                "store_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((store, "store_mem", "store_xmm"));
            prog.op_register.push(("store_xmm", "XMM0"));
            prog.op_indirect
                .push(("store_mem", "", "RAX", "NONE", 1, -0x10, 16));
            prog.ddisasm_cfg_edge.push((compare, store, "fallthrough"));
            for node in [compare, store] {
                prog.instr_in_function.push((node, func));
            }

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == compare
                    && matches!(
                        inst,
                        MachInst::Mop(Operation::Olongconst(-1), args, Mreg::X0)
                            if args.is_empty()
                    )
            }));
            assert!(prog
                .xmm_hi_mem_store
                .iter()
                .any(|fact| fact == &(store, 5, Mreg::Unknown, 0, compare)));
        });
    }

    #[test]
    fn wide_simd_store_through_general_base_resolves_its_high_lane() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let interleave = 0x600;
            let independent = 0x200;
            let store = 0x900;

            prog.instruction.push((
                interleave,
                4,
                "",
                "PUNPCKLQDQ",
                "ileave_src",
                "ileave_dst",
                "0",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("ileave_src", "XMM0"));
            prog.op_register.push(("ileave_dst", "XMM0"));
            prog.reg_def.push((interleave, Mreg::X0));

            prog.instruction.push((
                store,
                4,
                "",
                "MOVUPS",
                "store_xmm",
                "store_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((store, "store_mem", "store_xmm"));
            prog.op_register.push(("store_xmm", "XMM0"));
            prog.op_indirect
                .push(("store_mem", "", "RAX", "NONE", 1, 0x20, 16));

            for edge in [(interleave, independent), (independent, store)] {
                prog.ddisasm_cfg_edge.push((edge.0, edge.1, "fallthrough"));
            }

            let block = 0x100;
            let func = 0x100;
            prog.block_in_function.push((block, func));
            for addr in [interleave, independent, store] {
                prog.code_in_block.push((addr, block));
            }

            prog.run();

            assert!(prog
                .sse_wide_mem_store
                .iter()
                .any(|fact| { fact == &(store, Mreg::X0, "RAX", "NONE", 1, 0x20) }));
            assert!(prog
                .xmm_hi_mem_store
                .iter()
                .any(|fact| { fact == &(store, 1, Mreg::X0, 0, interleave) }));
            // A general-base destination is not a frame slot, so the frame form
            // must not claim it as well.
            assert!(!prog
                .xmm_hi_frame_store
                .iter()
                .any(|(addr, _, _, _, _, _)| *addr == store));
        });
    }

    #[test]
    fn wide_simd_store_through_rip_base_resolves_its_high_lane() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let interleave = 0x600;
            let independent = 0x200;
            let store = 0x900;
            let store_len = 7;
            let disp = 0x1000;
            let target = store + store_len as u64 + disp as u64;

            prog.instruction.push((
                interleave,
                4,
                "",
                "PUNPCKLQDQ",
                "ileave_src",
                "ileave_dst",
                "0",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("ileave_src", "XMM0"));
            prog.op_register.push(("ileave_dst", "XMM0"));
            prog.reg_def.push((interleave, Mreg::X0));

            prog.instruction.push((
                store,
                store_len,
                "",
                "MOVAPS",
                "store_xmm",
                "store_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((store, "store_mem", "store_xmm"));
            prog.op_register.push(("store_xmm", "XMM0"));
            prog.op_indirect
                .push(("store_mem", "", "RIP", "NONE", 1, disp, 16));

            for edge in [(interleave, independent), (independent, store)] {
                prog.ddisasm_cfg_edge.push((edge.0, edge.1, "fallthrough"));
            }

            let block = 0x100;
            let func = 0x100;
            prog.block_in_function.push((block, func));
            for addr in [interleave, independent, store] {
                prog.code_in_block.push((addr, block));
            }

            prog.run();

            assert!(prog
                .sse_wide_global_store
                .iter()
                .any(|fact| { fact == &(store, Mreg::X0, target) }));
            assert!(prog
                .xmm_hi_mem_store
                .iter()
                .any(|fact| { fact == &(store, 1, Mreg::X0, 0, interleave) }));
            // The register forms must not claim a RIP destination: there is no
            // general base to read and no frame cell to write.
            assert!(!prog
                .sse_wide_mem_store
                .iter()
                .any(|(addr, _, _, _, _, _)| *addr == store));
            assert!(!prog
                .xmm_hi_frame_store
                .iter()
                .any(|(addr, _, _, _, _, _)| *addr == store));
        });
    }

    #[test]
    fn simd_dword_broadcast_flows_through_cfg_transparently() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let movd = 0x700;
            let independent1 = 0x100;
            let shuffle = 0x900;
            let independent2 = 0x200;
            let independent3 = 0x800;
            let store = 0x300;

            prog.instruction
                .push((movd, 4, "", "MOVD", "value", "seed_xmm", "0", "0", 0, 0));
            prog.pmov.push((movd, "seed_xmm", "value"));
            prog.op_register.push(("seed_xmm", "XMM1"));
            prog.op_register.push(("value", "ESI"));
            prog.reg_def.push((movd, Mreg::X1));

            prog.instruction.push((
                shuffle,
                5,
                "",
                "PSHUFD",
                "shuffle_src",
                "shuffle_dst",
                "shuffle_imm",
                "0",
                0,
                0,
            ));
            prog.op_register.push(("shuffle_src", "XMM1"));
            prog.op_register.push(("shuffle_dst", "XMM0"));
            prog.op_immediate.push(("shuffle_imm", 0, 1));
            prog.reg_def.push((shuffle, Mreg::X0));

            prog.instruction.push((
                store,
                3,
                "",
                "MOVUPS",
                "store_xmm",
                "store_mem",
                "0",
                "0",
                0,
                0,
            ));
            prog.pmov.push((store, "store_mem", "store_xmm"));
            prog.op_register.push(("store_xmm", "XMM0"));
            prog.op_indirect
                .push(("store_mem", "", "RDI", "NONE", 1, 0, 16));

            // The CFG deliberately has no relationship to numeric node order.
            for edge in [
                (movd, independent1),
                (independent1, shuffle),
                (shuffle, independent2),
                (independent2, independent3),
                (independent3, store),
            ] {
                prog.ddisasm_cfg_edge.push((edge.0, edge.1, "fallthrough"));
            }

            // The broadcast dataflow is seeded only inside a function that also
            // contains a 16-byte SIMD store, so the seed needs to know which
            // function these instructions belong to.  Ownership flows from
            // block_in_function through code_in_block; one block for the whole
            // body keeps the point of the test, which is that the state follows
            // CFG edges rather than address order.
            let block = 0x100;
            let func = 0x100;
            prog.block_in_function.push((block, func));
            for addr in [
                movd,
                independent1,
                shuffle,
                independent2,
                independent3,
                store,
            ] {
                prog.code_in_block.push((addr, block));
            }

            prog.run();

            assert!(prog
                .simd_dword_broadcast_store
                .iter()
                .any(|fact| { fact == &(store, movd, "RDI", "NONE", 1, 0, Mreg::SI) }));
        });
    }

    #[test]
    fn sp_indexed_register_store_preserves_runtime_index() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let store = 0x900;

            prog.pmov.push((store, "stack_element", "value"));
            prog.op_indirect
                .push(("stack_element", "", "RSP", "RAX", 8, 24, 8));
            prog.op_register.push(("value", "R9"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == store
                    && matches!(
                        inst,
                        MachInst::Mstore(
                            MemoryChunk::MAny64,
                            Addressing::Aindexed2scaled(8, 24),
                            args,
                            Mreg::R9
                        ) if args.as_slice() == [Mreg::SP, Mreg::AX]
                    )
            }));
        });
    }

    #[test]
    fn indexed_integer_memory_sources_cover_arithmetic_and_logical_ops() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cases = [
                (
                    0x910,
                    1i64,
                    "indexed_dst_add",
                    "indexed_src_add",
                    "EAX",
                    4usize,
                    Operation::Oadd,
                    MemoryChunk::MInt32,
                ),
                (
                    0x920,
                    2,
                    "indexed_dst_sub",
                    "indexed_src_sub",
                    "EAX",
                    4,
                    Operation::Osub,
                    MemoryChunk::MInt32,
                ),
                (
                    0x930,
                    3,
                    "indexed_dst_and",
                    "indexed_src_and",
                    "EAX",
                    4,
                    Operation::Oand,
                    MemoryChunk::MInt32,
                ),
                (
                    0x940,
                    4,
                    "indexed_dst_or",
                    "indexed_src_or",
                    "EAX",
                    4,
                    Operation::Oor,
                    MemoryChunk::MInt32,
                ),
                (
                    0x950,
                    5,
                    "indexed_dst_xor",
                    "indexed_src_xor",
                    "CL",
                    1,
                    Operation::Oxor,
                    MemoryChunk::MInt8Unsigned,
                ),
            ];

            for (addr, kind, dst, src, dst_name, width, _, _) in cases.iter() {
                match kind {
                    1 => prog.padd.push((*addr, *dst, *src)),
                    2 => prog.psub.push((*addr, *dst, *src)),
                    3 => prog.pand.push((*addr, *dst, *src)),
                    4 => prog.por.push((*addr, *dst, *src)),
                    5 => prog.pxor.push((*addr, *dst, *src)),
                    _ => unreachable!(),
                };
                prog.op_register.push((*dst, *dst_name));
                prog.op_indirect
                    .push((*src, "", "RSP", "RDI", 4, -24, *width));
            }

            prog.run();

            for (addr, _, _, _, dst_name, _, expected_op, expected_chunk) in cases {
                assert!(prog.float_load_op.iter().any(|fact| {
                    fact == &(
                        addr,
                        expected_op.clone(),
                        expected_chunk,
                        Addressing::Aindexed2scaled(4, -24),
                        Arc::new(vec![Mreg::SP, Mreg::DI]),
                        Mreg::x86(dst_name),
                        false,
                    )
                }));
            }
        });
    }

    #[test]
    fn asm_stack_indexed_lea_preserves_index_scale_and_result_width() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [no_index, dst32_unscaled, dst32_scaled, dst64_unscaled, dst64_scaled] =
                synthetic_ids();

            let cases = [
                // address, dst symbol/name, memory symbol, index, scale,
                // displacement, expected operation, expected dst/index mregs
                (
                    dst64_scaled,
                    "dst64_scaled",
                    "RAX",
                    "mem64_scaled",
                    "R12",
                    4,
                    96,
                    Operation::Oleal(Addressing::Aindexed2scaled(4, 96)),
                    Mreg::AX,
                    Mreg::R12,
                ),
                (
                    dst64_unscaled,
                    "dst64_unscaled",
                    "RBX",
                    "mem64_unscaled",
                    "R13",
                    1,
                    40,
                    Operation::Oleal(Addressing::Aindexed2(40)),
                    Mreg::BX,
                    Mreg::R13,
                ),
                (
                    dst32_scaled,
                    "dst32_scaled",
                    "EAX",
                    "mem32_scaled",
                    "R14",
                    8,
                    24,
                    Operation::Olea(Addressing::Aindexed2scaled(8, 24)),
                    Mreg::AX,
                    Mreg::R14,
                ),
                (
                    dst32_unscaled,
                    "dst32_unscaled",
                    "ECX",
                    "mem32_unscaled",
                    "R15",
                    1,
                    -16,
                    Operation::Olea(Addressing::Aindexed2(-16)),
                    Mreg::CX,
                    Mreg::R15,
                ),
            ];

            for (addr, dst_sym, dst_name, mem_sym, index, scale, disp, _, _, _) in &cases {
                prog.plea.push((*addr, *dst_sym, *mem_sym));
                prog.op_register.push((*dst_sym, *dst_name));
                prog.op_indirect
                    .push((*mem_sym, "", "RSP", *index, *scale, *disp, 8));
            }

            // A no-index stack LEA remains the established Ainstack form.
            prog.plea.push((no_index, "dst_no_index", "mem_no_index"));
            prog.op_register.push(("dst_no_index", "RDX"));
            prog.op_indirect
                .push(("mem_no_index", "", "RSP", "NONE", 1, 32, 8));

            prog.run();

            for (addr, _, _, _, _, _, _, expected_op, expected_dst, expected_index) in cases {
                let expected = MachInst::Mop(
                    expected_op,
                    Arc::new(vec![Mreg::SP, expected_index]),
                    expected_dst,
                );
                assert!(
                    prog.mach_inst
                        .iter()
                        .any(|fact| fact == &(addr, expected.clone())),
                    "missing stack-indexed LEA at {addr:#x}; facts: {:?}",
                    prog.mach_inst
                        .iter()
                        .filter(|(node, _)| *node == addr)
                        .collect::<Vec<_>>()
                );
                assert!(
                    !prog.mach_inst.iter().any(|(node, inst)| {
                        *node == addr
                            && matches!(
                                inst,
                                MachInst::Mop(
                                    Operation::Olea(Addressing::Ainstack(_))
                                        | Operation::Oleal(Addressing::Ainstack(_)),
                                    args,
                                    _
                                ) if args.is_empty()
                            )
                    }),
                    "indexed stack LEA at {addr:#x} also lost its index"
                );
            }

            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    no_index,
                    MachInst::Mop(
                        Operation::Oleal(Addressing::Ainstack(32)),
                        Arc::new(vec![]),
                        Mreg::DX,
                    ),
                )
            }));
            assert!(!prog.mach_inst.iter().any(|(addr, inst)| {
                *addr == no_index
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Olea(Addressing::Aindexed2(_))
                                | Operation::Olea(Addressing::Aindexed2scaled(_, _))
                                | Operation::Oleal(Addressing::Aindexed2(_))
                                | Operation::Oleal(Addressing::Aindexed2scaled(_, _)),
                            _,
                            _
                        )
                    )
            }));
        });
    }

    #[test]
    fn asm_general_lea_preserves_destination_width() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [indexed64, indexed32, base64, base32] = synthetic_ids();

            let cases = [
                (
                    indexed64,
                    "dst_indexed64",
                    "R11",
                    "mem_indexed64",
                    "RDI",
                    "R12",
                    Operation::Oleal(Addressing::Aindexed2(0)),
                    Mreg::R11,
                ),
                (
                    indexed32,
                    "dst_indexed32",
                    "EAX",
                    "mem_indexed32",
                    "RDI",
                    "R12",
                    Operation::Olea(Addressing::Aindexed2(0)),
                    Mreg::AX,
                ),
                (
                    base64,
                    "dst_base64",
                    "R10",
                    "mem_base64",
                    "RDI",
                    "NONE",
                    Operation::Oleal(Addressing::Aindexed(24)),
                    Mreg::R10,
                ),
                (
                    base32,
                    "dst_base32",
                    "ECX",
                    "mem_base32",
                    "RDI",
                    "NONE",
                    Operation::Olea(Addressing::Aindexed(24)),
                    Mreg::CX,
                ),
            ];

            for (addr, dst_sym, dst_name, mem_sym, base_name, index_name, _, _) in &cases {
                prog.plea.push((*addr, *dst_sym, *mem_sym));
                prog.op_register.push((*dst_sym, *dst_name));
                let displacement = if *index_name == "NONE" { 24 } else { 0 };
                prog.op_indirect
                    .push((*mem_sym, "", *base_name, *index_name, 1, displacement, 8));
            }

            prog.run();

            for (addr, _, _, _, _, _, expected_op, expected_dst) in cases {
                assert!(
                    prog.mach_inst.iter().any(|fact| {
                        fact == &(
                            addr,
                            MachInst::Mop(
                                expected_op.clone(),
                                Arc::new(match &expected_op {
                                    Operation::Olea(Addressing::Aindexed2(_))
                                    | Operation::Oleal(Addressing::Aindexed2(_)) => {
                                        vec![Mreg::DI, Mreg::R12]
                                    }
                                    _ => vec![Mreg::DI],
                                }),
                                expected_dst,
                            ),
                        )
                    }),
                    "missing width-preserving general LEA at {addr:#x}; facts: {:?}",
                    prog.mach_inst
                        .iter()
                        .filter(|(node, _)| *node == addr)
                        .collect::<Vec<_>>()
                );
                assert!(
                    !prog.mach_inst.iter().any(|(node, inst)| {
                        *node == addr
                            && match (&expected_op, inst) {
                                (
                                    Operation::Oleal(_),
                                    MachInst::Mop(Operation::Olea(_), _, _),
                                )
                                | (
                                    Operation::Olea(_),
                                    MachInst::Mop(Operation::Oleal(_), _, _),
                                ) => true,
                                _ => false,
                            }
                    }),
                    "general LEA at {addr:#x} also admitted the opposite result width",
                );
            }
        });
    }

    #[test]
    fn frameless_bp_base_supports_a_32_bit_lea_result() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x1000;
            let lea = 0x1100;
            prog.plea.push((lea, "lea_dst", "lea_mem"));
            prog.op_register.push(("lea_dst", "EDX"));
            prog.op_indirect
                .push(("lea_mem", "", "RBP", "NONE", 1, -1, 8));
            prog.instr_in_function.push((lea, func));

            prog.run();

            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    lea,
                    MachInst::Mop(
                        Operation::Olea(Addressing::Aindexed(-1)),
                        Arc::new(vec![Mreg::BP]),
                        Mreg::DX,
                    ),
                )
            }));
        });
    }

    #[test]
    fn variable_shift_width_follows_the_encoded_destination_register() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [wide, narrow] = synthetic_ids();
            prog.pshr.extend([
                (wide, "wide_dst", "wide_count"),
                (narrow, "narrow_dst", "narrow_count"),
            ]);
            prog.op_register.extend([
                ("wide_dst", "RAX"),
                ("wide_count", "CL"),
                ("narrow_dst", "EAX"),
                ("narrow_count", "CL"),
            ]);

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == wide && matches!(inst, MachInst::Mop(Operation::Oshrlu, _, Mreg::AX))
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == wide && matches!(inst, MachInst::Mop(Operation::Oshru, _, _))
            }));
            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == narrow && matches!(inst, MachInst::Mop(Operation::Oshru, _, Mreg::AX))
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == narrow && matches!(inst, MachInst::Mop(Operation::Oshrlu, _, _))
            }));
        });
    }

    #[test]
    fn unary_rotate_and_immediate_multiply_follow_encoded_width() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [neg_wide, neg_narrow, not_wide, not_narrow, mul_wide, mul_narrow, ror_wide, ror_narrow] =
                synthetic_ids();
            prog.pneg
                .extend([(neg_wide, "neg_w"), (neg_narrow, "neg_n")]);
            prog.pnot
                .extend([(not_wide, "not_w"), (not_narrow, "not_n")]);
            prog.pimul.extend([
                (mul_wide, "mul_w", "mul_w_imm"),
                (mul_narrow, "mul_n", "mul_n_imm"),
            ]);
            prog.pror.extend([
                (ror_wide, "ror_w", "ror_w_imm"),
                (ror_narrow, "ror_n", "ror_n_imm"),
            ]);
            prog.op_register.extend([
                ("neg_w", "RAX"),
                ("neg_n", "EAX"),
                ("not_w", "RBX"),
                ("not_n", "EBX"),
                ("mul_w", "RCX"),
                ("mul_n", "ECX"),
                ("ror_w", "RDX"),
                ("ror_n", "EDX"),
            ]);
            prog.op_immediate.extend([
                ("mul_w_imm", 3, 1),
                ("mul_n_imm", 3, 1),
                ("ror_w_imm", 5, 1),
                ("ror_n_imm", 5, 1),
            ]);

            prog.run();

            let expected = [
                (neg_wide, Operation::Onegl),
                (neg_narrow, Operation::Oneg),
                (not_wide, Operation::Onotl),
                (not_narrow, Operation::Onot),
                (mul_wide, Operation::Omullimm(3)),
                (mul_narrow, Operation::Omulimm(3)),
                (ror_wide, Operation::Ororlimm(5)),
                (ror_narrow, Operation::Ororimm(5)),
            ];
            for (node, expected_op) in expected {
                assert!(prog.mach_inst.iter().any(|(candidate_node, inst)| {
                    *candidate_node == node
                        && matches!(inst, MachInst::Mop(op, _, _) if op == &expected_op)
                }));
            }
            for (node, forbidden) in [
                (neg_wide, Operation::Oneg),
                (neg_narrow, Operation::Onegl),
                (not_wide, Operation::Onot),
                (not_narrow, Operation::Onotl),
                (mul_wide, Operation::Omulimm(3)),
                (mul_narrow, Operation::Omullimm(3)),
                (ror_wide, Operation::Ororimm(5)),
                (ror_narrow, Operation::Ororlimm(5)),
            ] {
                assert!(!prog.mach_inst.iter().any(|(candidate_node, inst)| {
                    *candidate_node == node
                        && matches!(inst, MachInst::Mop(op, _, _) if op == &forbidden)
                }));
            }
        });
    }

    #[test]
    fn asm_structural_secondary_consumer_follows_cfg_not_numeric_ids() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cmp = 0x900;
            let first_jcc = 0x800;
            let second_jcc = 0x100;

            prog.pcmp.push((cmp, "cmp_lhs", "cmp_rhs"));
            prog.op_register.push(("cmp_lhs", "RAX"));
            prog.op_immediate.push(("cmp_rhs", 0, 8));
            prog.pjcc.push((first_jcc, TestCond::CondE, "first_target"));
            prog.pjcc
                .push((second_jcc, TestCond::CondNe, "second_target"));
            prog.flags_and_jump_pair
                .push((cmp, first_jcc, "cmp-to-first"));
            prog.flags_and_jump_pair
                .push((cmp, second_jcc, "cmp-to-second"));

            // Deliberately descending IDs: only structural CFG flow can tell
            // that first_jcc executes before second_jcc.
            prog.next.push((cmp, first_jcc));
            prog.code_in_block.push((cmp, 0xa00));
            prog.code_in_block.push((first_jcc, 0xa00));
            prog.ddisasm_cfg_edge
                .push((first_jcc, second_jcc, "fallthrough"));

            prog.run();

            assert!(prog
                .secondary_flags_consumer
                .iter()
                .any(|fact| fact == &(cmp, second_jcc)));
            assert!(!prog
                .secondary_flags_consumer
                .iter()
                .any(|fact| fact == &(cmp, first_jcc)));
            assert!(prog
                .secondary_safe
                .iter()
                .any(|fact| fact == &(cmp, second_jcc)));
            assert!(prog.mcond_at_jcc.iter().any(|fact| fact == &(second_jcc,)));
            assert!(!prog.mcond_at_jcc.iter().any(|fact| fact == &(first_jcc,)));
        });
    }

    #[test]
    fn asm_structural_secondary_consumer_merge_rejects_any_path_redefinition() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cmp = 0x900;
            let first_jcc = 0x800;
            let redef_arm = 0x700;
            let preserving_arm = 0x600;
            let second_jcc = 0x100;

            prog.pcmp.push((cmp, "cmp_lhs", "cmp_rhs"));
            prog.op_register.push(("cmp_lhs", "RAX"));
            prog.op_immediate.push(("cmp_rhs", 0, 8));
            prog.pjcc.push((first_jcc, TestCond::CondE, "first_target"));
            prog.pjcc
                .push((second_jcc, TestCond::CondNe, "second_target"));
            prog.flags_and_jump_pair
                .push((cmp, first_jcc, "cmp-to-first"));
            prog.flags_and_jump_pair
                .push((cmp, second_jcc, "cmp-to-second"));

            prog.next.push((cmp, first_jcc));
            prog.code_in_block.push((cmp, 0xa00));
            prog.code_in_block.push((first_jcc, 0xa00));
            prog.ddisasm_cfg_edge.push((first_jcc, redef_arm, "branch"));
            prog.ddisasm_cfg_edge
                .push((first_jcc, preserving_arm, "fallthrough"));
            prog.ddisasm_cfg_edge
                .push((redef_arm, second_jcc, "fallthrough"));
            prog.ddisasm_cfg_edge
                .push((preserving_arm, second_jcc, "fallthrough"));

            // Both arms preserve flags, but only one overwrites the compared
            // register. A may-redefinition lattice must retain that fact at
            // the merge even though the other incoming path is safe.
            prog.unrefinedinstruction.push((
                redef_arm, 1, "", "MOV", "mov_src", "mov_dst", "0", "0", 0, 0,
            ));
            prog.unrefinedinstruction.push((
                preserving_arm,
                1,
                "",
                "NOP",
                "0",
                "0",
                "0",
                "0",
                0,
                0,
            ));
            prog.reg_def.push((redef_arm, Mreg::AX));

            prog.run();

            assert!(prog
                .secondary_flags_consumer
                .iter()
                .any(|fact| fact == &(cmp, second_jcc)));
            assert!(prog
                .secondary_flags_arg_redefined
                .iter()
                .any(|fact| fact == &(cmp, second_jcc)));
            assert!(!prog
                .secondary_safe
                .iter()
                .any(|fact| fact == &(cmp, second_jcc)));
            assert!(!prog.mcond_at_jcc.iter().any(|fact| fact == &(second_jcc,)));
        });
    }

    #[test]
    fn asm_shadowed_primary_pair_keys_mcond_at_the_jcc() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cmp = 0x900;
            let shadow_mov = 0x904;
            let jcc = 0x908;

            prog.pcmp.push((cmp, "cmp_lhs", "cmp_rhs"));
            prog.op_register.push(("cmp_lhs", "RAX"));
            prog.op_immediate.push(("cmp_rhs", 0, 8));
            prog.pjcc.push((jcc, TestCond::CondE, "target"));
            prog.flags_and_jump_pair.push((cmp, jcc, "cmp-to-jcc"));

            prog.next.push((cmp, shadow_mov));
            prog.next.push((shadow_mov, jcc));
            prog.code_in_block.push((cmp, 0xa00));
            prog.code_in_block.push((shadow_mov, 0xa00));
            prog.code_in_block.push((jcc, 0xa00));
            // The shadow instruction is flag-neutral and writes an UNRELATED
            // register, so the compared value survives to the jump.
            prog.unrefinedinstruction.push((
                shadow_mov, 4, "", "MOV", "mov_src", "mov_dst", "0", "0", 0, 0,
            ));
            prog.reg_def.push((shadow_mov, Mreg::BX));

            prog.run();

            assert!(prog.shadowed_safe.iter().any(|fact| fact == &(cmp, jcc)));
            assert!(prog.mcond_at_jcc.iter().any(|fact| fact == &(jcc,)));
            assert!(prog
                .mcond_emit_addr
                .iter()
                .any(|fact| fact == &(cmp, jcc, jcc)));
            assert!(!prog
                .mcond_emit_addr
                .iter()
                .any(|fact| fact == &(cmp, jcc, cmp)));
            // The condition re-reads the compared register at the jump.
            assert!(prog.reg_use.iter().any(|fact| fact == &(jcc, Mreg::AX)));
        });
    }

    #[test]
    fn asm_shadow_that_redefines_a_compared_register_keeps_compare_keying() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cmp = 0x900;
            let shadow_mov = 0x904;
            let jcc = 0x908;

            prog.pcmp.push((cmp, "cmp_lhs", "cmp_rhs"));
            prog.op_register.push(("cmp_lhs", "RAX"));
            prog.op_immediate.push(("cmp_rhs", 0, 8));
            prog.pjcc.push((jcc, TestCond::CondE, "target"));
            prog.flags_and_jump_pair.push((cmp, jcc, "cmp-to-jcc"));

            prog.next.push((cmp, shadow_mov));
            prog.next.push((shadow_mov, jcc));
            prog.code_in_block.push((cmp, 0xa00));
            prog.code_in_block.push((shadow_mov, 0xa00));
            prog.code_in_block.push((jcc, 0xa00));
            // Same shape, but the shadow overwrites the compared register:
            // reading it at the jump would test the wrong value.
            prog.unrefinedinstruction.push((
                shadow_mov, 4, "", "MOV", "mov_src", "mov_dst", "0", "0", 0, 0,
            ));
            prog.reg_def.push((shadow_mov, Mreg::AX));

            prog.run();

            assert!(!prog.shadowed_safe.iter().any(|fact| fact == &(cmp, jcc)));
            assert!(prog
                .mcond_emit_addr
                .iter()
                .any(|fact| fact == &(cmp, jcc, cmp)));
            assert!(!prog
                .mcond_emit_addr
                .iter()
                .any(|fact| fact == &(cmp, jcc, jcc)));
        });
    }

    #[test]
    fn asm_structural_sub_reaching_defs_union_and_kill_at_merge() {
        on_large_stack(|| {
            fn run_case(kill_preserving_arm: bool) -> bool {
                let mut prog = AsmPassProgram::default();
                let sub = 0x900;
                let kill_arm = 0x800;
                let preserving_arm = 0x700;
                let use_addr = 0x100;

                prog.psub.push((sub, "sub_dst", "sub_one"));
                prog.op_register.push(("sub_dst", "RAX"));
                prog.op_immediate.push(("sub_one", 1, 8));
                prog.ddisasm_cfg_edge.push((sub, kill_arm, "branch"));
                prog.ddisasm_cfg_edge
                    .push((sub, preserving_arm, "fallthrough"));
                prog.ddisasm_cfg_edge
                    .push((kill_arm, use_addr, "fallthrough"));
                prog.ddisasm_cfg_edge
                    .push((preserving_arm, use_addr, "fallthrough"));
                prog.reg_def.push((kill_arm, Mreg::AX));
                if kill_preserving_arm {
                    prog.reg_def.push((preserving_arm, Mreg::AX));
                }
                prog.reg_use.push((use_addr, Mreg::AX));

                prog.run();

                prog.sub_result_live
                    .iter()
                    .any(|fact| fact == &(sub, Mreg::AX))
            }

            // At a merge, one surviving path is enough for may-reaching-defs;
            // redefining the destination on every path kills the SUB.
            assert!(run_case(false));
            assert!(!run_case(true));
        });
    }

    #[test]
    fn and_result_write_precedes_its_relocated_branch_condition() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [and_addr, jcc_addr, block] = synthetic_ids();

            prog.pand.push((and_addr, "mask_dst", "mask_imm"));
            prog.op_register.push(("mask_dst", "R12D"));
            prog.op_immediate.push(("mask_imm", 4, 4));
            // Only the structural instruction edge establishes the
            // producer/consumer sequence.
            prog.next.push((and_addr, jcc_addr));
            prog.code_in_block.push((and_addr, block));
            prog.code_in_block.push((jcc_addr, block));
            prog.pjcc.push((jcc_addr, TestCond::CondNe, "taken_target"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    and_addr,
                    MachInst::Mop(Operation::Oandimm(4), Arc::new(vec![Mreg::R12]), Mreg::R12),
                )
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == and_addr && matches!(inst, MachInst::Mop(Operation::Oandlimm(4), _, _))
            }));
            assert!(!prog
                .mach_inst
                .iter()
                .any(|(node, inst)| *node == and_addr && matches!(inst, MachInst::Mcond(..))));
            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    jcc_addr,
                    MachInst::Mcond(
                        Condition::Ccompimm(Comparison::Cne, 0),
                        Arc::new(vec![Mreg::R12]),
                        "taken_target",
                    ),
                )
            }));
            assert!(prog.mcond_at_jcc.iter().any(|fact| fact == &(jcc_addr,)));
        });
    }

    #[test]
    fn low_byte_boolean_reduction_prefers_full_value_then_masks_a_bypass() {
        on_large_stack(|| {
            let mut straight = AsmPassProgram::default();
            let [jcc, combine, rhs_set, lhs_set, gap, func, block] = synthetic_ids();

            // Execution order deliberately disagrees with numeric node IDs.
            // Only the structural CFG carries the two SETcc facts to the OR.
            straight.func_span.push(("f", func, 0x100));
            straight.next.extend([
                (func, lhs_set),
                (lhs_set, gap),
                (gap, rhs_set),
                (rhs_set, combine),
                (combine, jcc),
            ]);
            for node in [func, lhs_set, gap, rhs_set, combine, jcc] {
                straight.instr_in_function.push((node, func));
                straight.code_in_block.push((node, block));
            }
            straight.psetcc.extend([
                (lhs_set, TestCond::CondBe, "lhs"),
                (rhs_set, TestCond::CondBe, "rhs"),
            ]);
            straight.por.push((combine, "dst", "src"));
            straight.op_register.extend([
                ("lhs", "AL"),
                ("rhs", "DL"),
                ("dst", "AL"),
                ("src", "DL"),
            ]);
            straight.reg_def.extend([
                (lhs_set, Mreg::AX),
                (rhs_set, Mreg::DX),
                (combine, Mreg::AX),
            ]);
            straight.pjcc.push((jcc, TestCond::CondE, "safe"));

            straight.run();

            assert!(straight.mach_inst.iter().any(|fact| {
                fact == &(
                    combine,
                    MachInst::Mop(Operation::Oor, Arc::new(vec![Mreg::AX, Mreg::DX]), Mreg::AX),
                )
            }));
            assert!(straight.mach_inst.iter().any(|fact| {
                fact == &(
                    jcc,
                    MachInst::Mcond(
                        Condition::Ccompimm(Comparison::Ceq, 0),
                        Arc::new(vec![Mreg::AX]),
                        "safe",
                    ),
                )
            }));
            assert!(straight.mcond_at_jcc.iter().any(|fact| fact == &(jcc,)));

            let mut bypassed = AsmPassProgram::default();
            let [bypass_jcc, bypass_combine, bypass_rhs, join, bypass, bypass_lhs, bypass_func] =
                synthetic_ids();
            bypassed.func_span.push(("g", bypass_func, 0x100));
            for node in [
                bypass_func,
                bypass_lhs,
                bypass,
                join,
                bypass_rhs,
                bypass_combine,
                bypass_jcc,
            ] {
                bypassed.instr_in_function.push((node, bypass_func));
            }
            bypassed.ddisasm_cfg_edge.extend([
                (bypass_func, bypass_lhs, "branch"),
                (bypass_func, bypass, "fallthrough"),
                (bypass_lhs, join, "fallthrough"),
                (bypass, join, "fallthrough"),
                (join, bypass_rhs, "fallthrough"),
                (bypass_rhs, bypass_combine, "fallthrough"),
                (bypass_combine, bypass_jcc, "fallthrough"),
            ]);
            bypassed.psetcc.extend([
                (bypass_lhs, TestCond::CondBe, "bypass_lhs"),
                (bypass_rhs, TestCond::CondBe, "bypass_rhs"),
            ]);
            bypassed
                .por
                .push((bypass_combine, "bypass_dst", "bypass_src"));
            bypassed.op_register.extend([
                ("bypass_lhs", "AL"),
                ("bypass_rhs", "DL"),
                ("bypass_dst", "AL"),
                ("bypass_src", "DL"),
            ]);
            bypassed.reg_def.extend([
                (bypass_lhs, Mreg::AX),
                (bypass_rhs, Mreg::DX),
                (bypass_combine, Mreg::AX),
            ]);
            bypassed.pjcc.push((bypass_jcc, TestCond::CondE, "unsafe"));

            bypassed.run();

            // The bypass prevents must-proving AL as a full-register boolean,
            // but ZF still exactly tests the written byte lane. The fallback
            // therefore masks AL instead of dropping the branch.
            assert!(bypassed.mach_inst.iter().any(|fact| {
                fact == &(
                    bypass_jcc,
                    MachInst::Mcond(
                        Condition::Cmaskzero(0xff),
                        Arc::new(vec![Mreg::AX]),
                        "unsafe",
                    ),
                )
            }));
        });
    }

    #[test]
    fn partial_width_logical_zf_branch_masks_the_written_lane() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [jcc, gap, logical, func, block] = synthetic_ids();

            // Numeric order deliberately disagrees with execution order. The
            // MOV models a flag-transparent byte store between OR and JNE.
            for node in [logical, gap, jcc] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, block));
            }
            prog.next.extend([(logical, gap), (gap, jcc)]);
            prog.por.push((logical, "partial_dst", "partial_src"));
            prog.op_register
                .extend([("partial_dst", "SIL"), ("partial_src", "DL")]);
            prog.unrefinedinstruction
                .push((gap, 1, "", "MOV", "", "", "", "", 0, 0));
            prog.pjcc.push((jcc, TestCond::CondNe, "nonzero_lane"));

            prog.run();

            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    jcc,
                    MachInst::Mcond(
                        Condition::Cmasknotzero(0xff),
                        Arc::new(vec![Mreg::SI]),
                        "nonzero_lane",
                    ),
                )
            }));
            assert!(prog.mcond_at_jcc.iter().any(|fact| fact == &(jcc,)));
            assert!(prog.reg_use.iter().any(|fact| fact == &(jcc, Mreg::SI)));
        });
    }

    #[test]
    fn memory_flag_reads_are_preserved_as_nontrampoline_nodes() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let cmp = 0x900;
            let test = 0x100;

            prog.pcmp.push((cmp, "cmp_mem", "cmp_imm"));
            prog.ptest.push((test, "test_imm", "test_mem"));
            prog.op_indirect
                .push(("cmp_mem", "", "RCX", "NONE", 1, 0, 1));
            prog.op_indirect
                .push(("test_mem", "", "RDX", "NONE", 1, 8, 4));

            prog.run();

            assert!(prog
                .node_unlowered_side_effect
                .iter()
                .any(|fact| fact == &(cmp,)));
            assert!(prog
                .node_unlowered_side_effect
                .iter()
                .any(|fact| fact == &(test,)));
        });
    }

    #[test]
    fn asm_stack_state_follows_cfg_and_mov_stack_reads_remain_loads() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x900;
            let store = 0x300;
            let reload = 0x200;
            let read_without_local_def = 0x100;

            prog.func_span.push(("f", func, 0xa00));
            for node in [func, store, reload, read_without_local_def] {
                prog.instr_in_function.push((node, func));
            }

            // Deliberately descending addresses and no physical `next` edge:
            // only the structural inter-block CFG can carry the frame state.
            prog.stack_delta.push((func, -32));
            prog.ddisasm_cfg_edge.push((func, store, "branch"));
            prog.ddisasm_cfg_edge.push((store, reload, "fallthrough"));
            prog.ddisasm_cfg_edge
                .push((reload, read_without_local_def, "fallthrough"));

            prog.pmov.push((store, "store_mem", "store_src"));
            prog.op_register.push(("store_src", "RAX"));
            prog.op_indirect
                .push(("store_mem", "", "RSP", "NONE", 1, 56, 8));

            prog.pmov.push((reload, "reload_dst", "reload_mem"));
            prog.op_register.push(("reload_dst", "RBX"));
            prog.op_indirect
                .push(("reload_mem", "", "RSP", "NONE", 1, 56, 8));

            // A memory-reading MOV is still a load when no local instruction
            // stored the slot: a callee may have initialized it through &slot.
            prog.pmov
                .push((read_without_local_def, "external_dst", "external_mem"));
            prog.op_register.push(("external_dst", "RCX"));
            prog.op_indirect
                .push(("external_mem", "", "RSP", "NONE", 1, 72, 8));

            prog.run();

            assert!(prog
                .mach_inst
                .iter()
                .any(|fact| { fact == &(store, MachInst::Msetstack(Mreg::AX, 56, Typ::Tany64)) }));
            assert!(prog
                .mach_inst
                .iter()
                .any(|fact| { fact == &(reload, MachInst::Mgetstack(56, Typ::Tany64, Mreg::BX)) }));
            assert!(prog.mach_inst.iter().any(|fact| {
                fact == &(
                    read_without_local_def,
                    MachInst::Mgetstack(72, Typ::Tany64, Mreg::CX),
                )
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == read_without_local_def
                    && matches!(
                        inst,
                        MachInst::Mop(
                            Operation::Olea(Addressing::Ainstack(72))
                                | Operation::Oleal(Addressing::Ainstack(72)),
                            _,
                            _
                        )
                    )
            }));
        });
    }

    #[test]
    fn stack_probe_back_edge_does_not_erase_later_frame_spill_and_reload() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let [func, probe_sub, probe_touch, probe_latch, spill, reload] = synthetic_ids();
            let [entry_block, probe_block, spill_block, reload_block] =
                [0x100, 0x200, 0x300, 0x400];

            prog.func_span.push(("f", func, 0x1000));
            for (node, block) in [
                (func, entry_block),
                (probe_sub, probe_block),
                (probe_touch, probe_block),
                (probe_latch, probe_block),
                (spill, spill_block),
                (reload, reload_block),
            ] {
                prog.instr_in_function.push((node, func));
                prog.code_in_block.push((node, block));
                prog.block_in_function.push((block, func));
            }

            prog.ddisasm_cfg_edge.push((func, probe_sub, "fallthrough"));
            prog.next.push((probe_sub, probe_touch));
            prog.next.push((probe_touch, probe_latch));
            prog.ddisasm_cfg_edge
                .push((probe_latch, probe_sub, "branch"));
            prog.ddisasm_cfg_edge
                .push((probe_latch, spill, "fallthrough"));
            prog.ddisasm_cfg_edge.push((spill, reload, "fallthrough"));
            prog.stack_delta.push((probe_sub, -4096));

            prog.pmov.push((spill, "spill_slot", "spill_src"));
            prog.op_register.push(("spill_src", "RDX"));
            prog.op_indirect
                .push(("spill_slot", "", "RSP", "NONE", 1, 8, 8));
            prog.pmov.push((reload, "reload_dst", "reload_slot"));
            prog.op_register.push(("reload_dst", "RDI"));
            prog.op_indirect
                .push(("reload_slot", "", "RSP", "NONE", 1, 8, 8));

            prog.run();

            assert!(prog.stack_offset.iter().any(|fact| {
                let fact = fact.read().unwrap();
                fact.0 == func && fact.1 == spill && exact_stack_offset(&fact.2 .0) == Some(-4096)
            }));
            assert!(prog
                .mach_inst
                .iter()
                .any(|fact| { fact == &(spill, MachInst::Msetstack(Mreg::DX, 8, Typ::Tany64),) }));
            assert!(prog
                .mach_inst
                .iter()
                .any(|fact| { fact == &(reload, MachInst::Mgetstack(8, Typ::Tany64, Mreg::DI),) }));
            assert!(prog
                .stack_offset_backedge_rescued_access
                .iter()
                .any(|fact| fact == &(func, spill)));
            assert!(prog
                .stack_offset_backedge_rescued_access
                .iter()
                .any(|fact| fact == &(func, reload)));
        });
    }

    #[test]
    fn immediate_sp_store_uses_the_same_raw_slot_as_an_sp_lea() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x9000;
            let store = 0x1000;

            prog.func_span.push(("f", func, 0xa000));
            prog.instr_in_function.push((func, func));
            prog.instr_in_function.push((store, func));
            // Structural execution order deliberately descends numerically.
            prog.ddisasm_cfg_edge.push((func, store, "fallthrough"));
            prog.stack_delta.push((func, -216));

            prog.pmov.push((store, "slot", "four"));
            prog.op_immediate.push(("four", 4, 0));
            prog.op_indirect
                .push(("slot", "NONE", "RSP", "NONE", 1, 16, 4));

            prog.run();

            assert!(prog
                .mach_imm_stack_init
                .iter()
                .any(|fact| fact == &(store, 16, 4, Typ::Tint)));
            assert!(!prog
                .mach_imm_stack_init
                .iter()
                .any(|fact| fact == &(store, -200, 4, Typ::Tint)));
        });
    }

    #[test]
    fn asm_stack_state_disagreement_becomes_unknown_at_merge() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x900;
            let left = 0x800;
            let right = 0x700;
            let merge = 0x100;

            prog.func_span.push(("f", func, 0xa00));
            for node in [func, left, right, merge] {
                prog.instr_in_function.push((node, func));
            }

            prog.ddisasm_cfg_edge.push((func, left, "branch"));
            prog.ddisasm_cfg_edge.push((func, right, "fallthrough"));
            prog.ddisasm_cfg_edge.push((left, merge, "fallthrough"));
            prog.ddisasm_cfg_edge.push((right, merge, "fallthrough"));
            prog.stack_delta.push((left, -8));

            prog.pmov.push((merge, "load_dst", "load_mem"));
            prog.op_register.push(("load_dst", "RAX"));
            prog.op_indirect
                .push(("load_mem", "", "RSP", "NONE", 1, 24, 8));

            prog.run();

            assert!(prog.stack_offset.iter().any(|fact| {
                let fact = fact.read().unwrap();
                fact.0 == func && fact.1 == merge && fact.2 .0.is_empty()
            }));
            assert!(!prog.mach_inst.iter().any(|(node, inst)| {
                *node == merge && matches!(inst, MachInst::Mgetstack(_, _, _))
            }));
        });
    }

    #[test]
    fn memory_push_keeps_a_balanced_loop_frame_exact() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func = 0x900;
            let store = 0x800;
            let mem_push = 0x700;
            let cleanup = 0x600;
            let latch = 0x500;

            prog.func_span.push(("f", func, 0xa00));
            for node in [func, store, mem_push, cleanup, latch] {
                prog.instr_in_function.push((node, func));
            }
            prog.ddisasm_cfg_edge.push((func, store, "fallthrough"));
            prog.ddisasm_cfg_edge.push((store, mem_push, "fallthrough"));
            prog.ddisasm_cfg_edge
                .push((mem_push, cleanup, "fallthrough"));
            prog.ddisasm_cfg_edge.push((cleanup, latch, "fallthrough"));
            prog.ddisasm_cfg_edge.push((latch, store, "branch"));

            prog.stack_delta.push((func, -32));
            prog.ppush.push((mem_push, "arg_mem"));
            prog.op_indirect
                .push(("arg_mem", "", "RSP", "NONE", 1, 24, 8));
            prog.stack_delta.push((cleanup, 8));

            prog.pmov.push((store, "wide_slot", "wide_value"));
            prog.op_register.push(("wide_value", "XMM3"));
            prog.op_indirect
                .push(("wide_slot", "", "RSP", "NONE", 1, 48, 16));

            prog.run();

            assert!(prog.stack_delta.iter().any(|fact| fact == &(mem_push, -8)));
            assert!(prog.stack_offset.iter().any(|fact| {
                let fact = fact.read().unwrap();
                fact.0 == func && fact.1 == store && exact_stack_offset(&fact.2 .0) == Some(-32)
            }));
            assert!(prog
                .mach_inst
                .iter()
                .any(|fact| { fact == &(store, MachInst::Msetstack(Mreg::X3, 48, Typ::Tany64),) }));
        });
    }

    #[test]
    fn asm_function_ownership_follows_blocks_across_nonmonotonic_shared_boundaries() {
        on_large_stack(|| {
            let mut prog = AsmPassProgram::default();
            let func_a = 0x100;
            let func_b = 0x500;
            let node_a = 0x110;
            let node_b_cold = 0x120;
            let node_shared = 0x130;
            let unassigned = 0x140;

            prog.block_in_function.push((0xa0, func_a));
            // A cold/shared layout need not order a block after its function
            // entry.  Ownership is the CFG-derived fact, not that ordering.
            prog.block_in_function.push((0xb0, func_b));
            prog.block_in_function.push((0xc0, func_a));
            prog.block_in_function.push((0xc0, func_b));
            prog.code_in_block.push((node_a, 0xa0));
            prog.code_in_block.push((node_b_cold, 0xb0));
            prog.code_in_block.push((node_shared, 0xc0));
            prog.code_in_block.push((unassigned, 0xd0));

            // Physical adjacency crosses from A into B's cold block, then a
            // legitimately shared block, then an unassigned block.  The old
            // range-bounded `next` recursion invented A ownership for B's
            // block and owners for the unassigned block.
            prog.next.push((node_a, node_b_cold));
            prog.next.push((node_b_cold, node_shared));
            prog.next.push((node_shared, unassigned));
            prog.func_span.push(("a", func_a, 0x200));
            prog.func_span.push(("b", func_b, 0x600));

            prog.run();

            let owners = |node| {
                prog.instr_in_function
                    .iter()
                    .filter_map(|(n, f)| (*n == node).then_some(*f))
                    .collect::<BTreeSet<_>>()
            };
            assert_eq!(owners(node_a), BTreeSet::from([func_a]));
            assert_eq!(owners(node_b_cold), BTreeSet::from([func_b]));
            assert_eq!(owners(node_shared), BTreeSet::from([func_a, func_b]));
            assert!(owners(unassigned).is_empty());
        });
    }

    #[test]
    fn asm_structural_dataflow_scheduler_metadata_is_complete() {
        let pass = AsmPass;
        for relation in [
            "block_in_function",
            "code_in_block",
            "next",
            "ddisasm_cfg_edge",
            "flags_and_jump_pair",
            "unrefinedinstruction",
            "decoded_reg_def",
        ] {
            assert!(
                pass.inputs().contains(&relation),
                "missing scheduler input {relation}"
            );
        }
        for relation in ["reg_def", "reg_use"] {
            assert!(
                pass.outputs().contains(&relation),
                "missing scheduler output {relation}"
            );
        }
        assert!(pass.outputs().contains(&"instr_in_function"));
        assert!(!pass.inputs().contains(&"ddisasm_function_entry"));
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddressingError {
    NeedsSymbolResolution {
        address: i64,
    },
    UnknownRegister {
        register: Ireg,
    },
    UnsupportedPattern {
        addrmode: Addrmode,
    },
    #[allow(dead_code)]
    InvalidRegisterCombination {
        base: Option<Ireg>,
        index: Option<(Ireg, i64)>,
    },
}

impl std::fmt::Display for AddressingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddressingError::NeedsSymbolResolution { address } => {
                write!(f, "Address 0x{:x} needs symbol resolution", address)
            }
            AddressingError::UnknownRegister { register } => {
                write!(f, "Unknown register: {:?}", register)
            }
            AddressingError::UnsupportedPattern { addrmode } => {
                write!(f, "Unsupported addrmode pattern: {:?}", addrmode)
            }
            AddressingError::InvalidRegisterCombination { base, index } => {
                write!(
                    f,
                    "Invalid register combination: base={:?}, index={:?}",
                    base, index
                )
            }
        }
    }
}

#[inline]

// Returns true for valid general-purpose registers (excludes Unknown and RIP).
fn is_valid_gpr(r: Ireg) -> bool {
    !matches!(r, Ireg::Unknown | Ireg::RIP)
}

// Map a 64-bit GPR name to its 32-bit alias (RAX->EAX); pass through 32-bit/unknown. Used by mod-synth dividend-holder check to equate EAX with EDI after `MOVSXD rax, edi`.
pub fn reg_low32_alias(s: &str) -> &str {
    match s {
        "RAX" => "EAX",
        "RBX" => "EBX",
        "RCX" => "ECX",
        "RDX" => "EDX",
        "RDI" => "EDI",
        "RSI" => "ESI",
        "RBP" => "EBP",
        "RSP" => "ESP",
        "R8" => "R8D",
        "R9" => "R9D",
        "R10" => "R10D",
        "R11" => "R11D",
        "R12" => "R12D",
        "R13" => "R13D",
        "R14" => "R14D",
        "R15" => "R15D",
        other => other,
    }
}

// Check if register name is an 8-bit GPR.
pub fn is_reg_8(name: &str) -> bool {
    matches!(
        name,
        "AL" | "BL"
            | "CL"
            | "DL"
            | "AH"
            | "BH"
            | "CH"
            | "DH"
            | "SIL"
            | "DIL"
            | "SPL"
            | "BPL"
            | "R8B"
            | "R9B"
            | "R10B"
            | "R11B"
            | "R12B"
            | "R13B"
            | "R14B"
            | "R15B"
    )
}

// True for the legacy high-8 sub-registers AH/BH/CH/DH, which collapse to their parent Ireg, so a mask test through one must use M<<8 against the parent to stay equivalent.
pub fn is_reg_high8(name: &str) -> bool {
    matches!(name, "AH" | "BH" | "CH" | "DH")
}

// Adjust a TEST/AND mask immediate for a high-8 register operand, shifting it into the parent register's bit positions; other registers keep the mask unchanged.
pub fn high8_mask_adjust(reg_name: &str, mask: i64) -> i64 {
    if is_reg_high8(reg_name) {
        mask << 8
    } else {
        mask
    }
}

// ZF after a byte/word logical operation describes only the written lane.
// The recovered Mreg names the architectural parent register, so express that
// exact lane as a mask rather than comparing stale upper bits against zero.
fn partial_logical_result_mask(reg_name: &str) -> Option<i64> {
    if is_reg_8(reg_name) {
        Some(high8_mask_adjust(reg_name, 0xff))
    } else if is_reg_16(reg_name) {
        Some(0xffff)
    } else {
        None
    }
}

// Check if register name is a 16-bit GPR.
pub fn is_reg_16(name: &str) -> bool {
    matches!(
        name,
        "AX" | "BX"
            | "CX"
            | "DX"
            | "SI"
            | "DI"
            | "SP"
            | "BP"
            | "R8W"
            | "R9W"
            | "R10W"
            | "R11W"
            | "R12W"
            | "R13W"
            | "R14W"
            | "R15W"
    )
}

// Conditions for which a jcc after an add tests the signed RESULT against zero exactly: ZF and the signed conditions qualify, unsigned CF-based ones do not, since CF is carry-out.
fn arith_result_testcond_ok(c: TestCond) -> bool {
    matches!(
        c,
        TestCond::CondE
            | TestCond::CondNe
            | TestCond::CondL
            | TestCond::CondLe
            | TestCond::CondG
            | TestCond::CondGe
    )
}

// Returns true if the mnemonic modifies CPU flags; conservative (true when uncertain); used by gap-bridging rules to detect flag-safe instructions between CMP/TEST and CMOV.
fn is_flag_setting(mnem: &str) -> bool {
    !matches!(
        mnem,
        "MOV"
            | "MOVZX"
            | "MOVSX"
            | "MOVSXD"
            | "MOVABS"
            | "LEA"
            | "NOP"
            | "ENDBR64"
            | "ENDBR32"
            | "PUSH"
            | "POP"
            | "XCHG"
            | "BSWAP"
            | "VZEROUPPER"
            | "VZEROALL"
            | "MOVAPS"
            | "MOVUPS"
            | "MOVAPD"
            | "MOVUPD"
            | "VMOVAPS"
            | "VMOVUPS"
            | "VMOVAPD"
            | "VMOVUPD"
            | "MOVSS"
            | "MOVSD"
            | "MOVDQA"
            | "MOVDQU"
            | "VMOVSS"
            | "VMOVSD"
            | "VMOVDQA"
            | "VMOVDQU"
            | "MOVQ"
            | "MOVD"
            | "MOVHPS"
            | "MOVLPS"
            | "VMOVQ"
            | "VMOVD"
            | "CMOVE"
            | "CMOVNE"
            | "CMOVZ"
            | "CMOVNZ"
            | "CMOVB"
            | "CMOVC"
            | "CMOVNAE"
            | "CMOVAE"
            | "CMOVNC"
            | "CMOVNB"
            | "CMOVBE"
            | "CMOVNA"
            | "CMOVA"
            | "CMOVNBE"
            | "CMOVL"
            | "CMOVNGE"
            | "CMOVGE"
            | "CMOVNL"
            | "CMOVLE"
            | "CMOVNG"
            | "CMOVG"
            | "CMOVNLE"
            | "CMOVS"
            | "CMOVNS"
            | "CMOVP"
            | "CMOVPE"
            | "CMOVNP"
            | "CMOVPO"
    )
}

// Returns the absolute address if the addrmode requires symbol resolution (RIP-relative or absolute).
pub fn addrmode_needs_symbol_resolution(am: &Addrmode) -> Option<i64> {
    match am {
        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Const(n),
        } if *n != 0 => Some(*n),

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(n),
        } if *n != 0 => Some(*n),

        // Scaled index with no base: absolute displacement needs symbol resolution
        Addrmode {
            base: None,
            index: Some(_),
            disp: Displacement::Const(n),
        } if *n != 0 => Some(*n),

        _ => None,
    }
}

/// Return the absolute data-address displacement from the one-dynamic-register
/// x86 form `[gpr + absolute]`.  Whether that integer really names image data
/// is deliberately decided by the Ascent rule joining the loader's section map
/// and `raw_image_addresses_are_absolute`; this helper only recognizes shape.
fn absolute_based_data_target(am: &Addrmode) -> Option<Address> {
    match am {
        Addrmode {
            base: Some(base),
            index: None,
            disp: Displacement::Const(displacement),
        } if is_valid_gpr(*base) && !matches!(base, Ireg::RSP | Ireg::RBP) && *displacement > 0 => {
            Some(*displacement as Address)
        }
        _ => None,
    }
}

/// Match the raw x86 memory operand back to its canonical Addrmode while
/// retaining the architectural address-register view discarded by Ireg/Mreg
/// canonicalization.  LP64 `[rdi+disp]` is eligible; address-size-overridden
/// `[edi+disp]` is not.
fn pointer_width_absolute_based_operand(
    am: &Addrmode,
    base: &str,
    index: &str,
    displacement: i64,
) -> Option<(Address, Mreg)> {
    if x86_gpr_view_width(base) != Some(8)
        || !(index == "NONE" || index.is_empty())
        || am.base != Some(Ireg::from(base))
        || am.index.is_some()
        || am.disp != Displacement::Const(displacement)
    {
        return None;
    }
    Some((absolute_based_data_target(am)?, Mreg::x86(base)))
}

// Reverse of CompCert's transl_addressing (see x86/Asmgen.v).
pub fn transl_addressing_rev(
    am: Addrmode,
    resolved_symbol: Option<(Ident, i64)>,
) -> Result<(Addressing, Vec<Mreg>), String> {
    transl_addressing_rev_inner(am, resolved_symbol).map_err(|e| e.to_string())
}

fn transl_addressing_rev_inner(
    am: Addrmode,
    resolved_symbol: Option<(Ident, i64)>,
) -> Result<(Addressing, Vec<Mreg>), AddressingError> {
    match am {
        Addrmode {
            base: Some(Ireg::RSP),
            index: None,
            disp: Displacement::Const(n),
        } => Ok((Addressing::Ainstack(n), vec![])),

        Addrmode {
            base: Some(Ireg::RBP),
            index: None,
            disp: Displacement::Const(n),
        } => Ok((Addressing::Ainstack(n), vec![])),

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } => Ok((Addressing::Aglobal(ident, ofs), vec![])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } => Ok((Addressing::Aglobal(ident, ofs), vec![])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Const(n),
        } => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::NeedsSymbolResolution { address: n })
            }
        }

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(n),
        } if n != 0 => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::NeedsSymbolResolution { address: n })
            }
        }

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(0),
        } => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::UnsupportedPattern { addrmode: am })
            }
        }

        Addrmode {
            base: Some(r1),
            index: None,
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && r1 != Ireg::RSP => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Abased(ident, offset), vec![r1.into()]))
            } else {
                Ok((Addressing::Aindexed(n), vec![r1.into()]))
            }
        }

        Addrmode {
            base: Some(r1),
            index: Some((r2, 1)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && is_valid_gpr(r2) => {
            Ok((Addressing::Aindexed2(n), vec![r1.into(), r2.into()]))
        }

        Addrmode {
            base: None,
            index: Some((r1, sc)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Abasedscaled(sc, ident, offset), vec![r1.into()]))
            } else {
                Ok((Addressing::Ascaled(sc, n), vec![r1.into()]))
            }
        }

        Addrmode {
            base: Some(r1),
            index: Some((r2, sc)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && is_valid_gpr(r2) && sc != 1 => Ok((
            Addressing::Aindexed2scaled(sc, n),
            vec![r1.into(), r2.into()],
        )),

        Addrmode {
            base: Some(r1),
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) => Ok((Addressing::Abased(ident, ofs), vec![r1.into()])),

        Addrmode {
            base: None,
            index: Some((r1, sc)),
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) => Ok((Addressing::Abasedscaled(sc, ident, ofs), vec![r1.into()])),

        Addrmode {
            base: Some(r1),
            index: Some((r2, sc)),
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) && is_valid_gpr(r2) => {
            if sc == 1 {
                log::debug!(
                    "Addressing base({:?}) + index({:?}) + symbol({}, {}): using Abased, index discarded",
                    r1, r2, ident, ofs
                );
                Ok((Addressing::Abased(ident, ofs), vec![r1.into()]))
            } else {
                log::warn!(
                    "Unsupported addressing: base({:?}) + {}*index({:?}) + symbol({}, {}). \
                     No CompCert mode can represent this pattern.",
                    r1,
                    sc,
                    r2,
                    ident,
                    ofs
                );
                Err(AddressingError::UnsupportedPattern { addrmode: am })
            }
        }

        Addrmode {
            base: Some(r1),
            index: Some((Ireg::Unknown, _)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) => Ok((Addressing::Aindexed(n), vec![r1.into()])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: Some((r1, sc)),
            disp,
        } if is_valid_gpr(r1) => match disp {
            Displacement::Symbol { ident, ofs } => {
                if sc == 1 {
                    Ok((Addressing::Abased(ident, ofs), vec![r1.into()]))
                } else {
                    Ok((Addressing::Abasedscaled(sc, ident, ofs), vec![r1.into()]))
                }
            }
            Displacement::Const(n) => {
                if let Some((ident, offset)) = resolved_symbol {
                    if sc == 1 {
                        Ok((Addressing::Abased(ident, offset), vec![r1.into()]))
                    } else {
                        Ok((Addressing::Abasedscaled(sc, ident, offset), vec![r1.into()]))
                    }
                } else {
                    if sc == 1 {
                        Ok((Addressing::Aindexed(n), vec![r1.into()]))
                    } else {
                        Ok((Addressing::Ascaled(sc, n), vec![r1.into()]))
                    }
                }
            }
        },

        Addrmode {
            base: Some(Ireg::Unknown),
            ..
        } => Err(AddressingError::UnknownRegister {
            register: Ireg::Unknown,
        }),

        _ => Err(AddressingError::UnsupportedPattern { addrmode: am }),
    }
}
