// ARM32 decoding into the same DB relations as x86 and AArch64, plus the normalizations ARM32 needs and the other two frontends do not: literal pools are carved out of the instruction stream, PC-as-destination is classified as a control transfer, predication is turned back into either a select or a real branch, and LDM/STM is expanded into per-register transfers.
// ARM32 has two instruction sets, A32 and Thumb, that may alternate within one section. The set a byte is encoded in is recovered here and never leaves this file: mach_inst is arch-neutral, so nothing above the decoder learns that Thumb exists.

use std::collections::{BTreeMap, HashSet};

use capstone::arch::arm::{ArmCC, ArmOperand, ArmOperandType, ArmShift};
use capstone::prelude::*;
use object::{Object, ObjectSection};

use crate::arm32::mach::A32Mreg;
use crate::decompile::disassembly::branch::{self, PcSource};
use crate::decompile::disassembly::instruction::{is_executable_section, DecodedInsn};
use crate::decompile::disassembly::operand::*;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;

/// Which of ARM32's two instruction sets a run of code bytes is encoded in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IsaMode {
    Arm,
    Thumb,
}

impl IsaMode {
    /// The value the PC reads as while executing at `addr`. A32 is two 4-byte instructions of prefetch ahead; Thumb is one word ahead and then word-ALIGNED, which is what makes a literal-pool reference from an odd halfword land on the right word.
    fn pc_base(self, addr: u64) -> u64 {
        match self {
            IsaMode::Arm => addr.wrapping_add(8),
            IsaMode::Thumb => addr.wrapping_add(4) & !3,
        }
    }

    /// The state a BLX switches to.
    fn toggled(self) -> Self {
        match self {
            IsaMode::Arm => IsaMode::Thumb,
            IsaMode::Thumb => IsaMode::Arm,
        }
    }

    /// Instruction alignment: A32 is fixed 4-byte, Thumb is a sequence of 2-byte halfwords.
    fn alignment(self) -> usize {
        match self {
            IsaMode::Arm => 4,
            IsaMode::Thumb => 2,
        }
    }

    /// The AAPCS frame pointer for this state: R11 in ARM state, R7 in Thumb state, where the 16-bit encodings cannot reach the high registers.
    fn frame_reg(self) -> &'static str {
        match self {
            IsaMode::Arm => "R11",
            IsaMode::Thumb => "R7",
        }
    }

    fn tag(self) -> u8 {
        match self {
            IsaMode::Arm => 1,
            IsaMode::Thumb => 2,
        }
    }

    fn from_tag(t: u8) -> Option<Self> {
        match t {
            1 => Some(IsaMode::Arm),
            2 => Some(IsaMode::Thumb),
            _ => None,
        }
    }
}

/// One capstone handle per instruction set; a segment is decoded with the handle its recovered mode names.
struct Engines {
    arm: Capstone,
    thumb: Capstone,
}

impl Engines {
    fn new() -> Self {
        let build = |mode| {
            Capstone::new()
                .arm()
                .mode(mode)
                .detail(true)
                .build()
                .expect("Failed to create capstone arm engine")
        };
        Engines {
            arm: build(arch::arm::ArchMode::Arm),
            thumb: build(arch::arm::ArchMode::Thumb),
        }
    }

    fn get(&self, mode: IsaMode) -> &Capstone {
        match mode {
            IsaMode::Arm => &self.arm,
            IsaMode::Thumb => &self.thumb,
        }
    }
}

/// Condition-code spelling for the normalized mnemonic; AL and the invalid code are unconditional and answer None.
fn cc_name(cc: ArmCC) -> Option<&'static str> {
    Some(match cc {
        ArmCC::ARM_CC_EQ => "EQ",
        ArmCC::ARM_CC_NE => "NE",
        ArmCC::ARM_CC_HS => "HS",
        ArmCC::ARM_CC_LO => "LO",
        ArmCC::ARM_CC_MI => "MI",
        ArmCC::ARM_CC_PL => "PL",
        ArmCC::ARM_CC_VS => "VS",
        ArmCC::ARM_CC_VC => "VC",
        ArmCC::ARM_CC_HI => "HI",
        ArmCC::ARM_CC_LS => "LS",
        ArmCC::ARM_CC_GE => "GE",
        ArmCC::ARM_CC_LT => "LT",
        ArmCC::ARM_CC_GT => "GT",
        ArmCC::ARM_CC_LE => "LE",
        _ => return None,
    })
}

/// The condition that holds exactly when `cc` does not; the guard a split predicated instruction branches on.
fn invert_cc(cc: &str) -> Option<&'static str> {
    Some(match cc {
        "EQ" => "NE",
        "NE" => "EQ",
        // HS/CS and LO/CC are two spellings of one pair of conditions; capstone prints either, so both must map.
        "HS" | "CS" => "LO",
        "LO" | "CC" => "HS",
        "MI" => "PL",
        "PL" => "MI",
        "VS" => "VC",
        "VC" => "VS",
        "HI" => "LS",
        "LS" => "HI",
        "GE" => "LT",
        "LT" => "GE",
        "GT" => "LE",
        "LE" => "GT",
        _ => return None,
    })
}

/// Capstone's mnemonic minus the condition suffix, with the VFP data-type suffix joined by '_' so '.' is left free as the condition separator. Thumb-2's `.W`/`.N` tail names the ENCODING width, not the operation, and is dropped: left in, `B.W` would read as a conditional branch and `LDR.W` as an unknown opcode.
fn opcode_stem(raw: &str, cond: Option<&str>) -> String {
    let (head, ty) = match raw.split_once('.') {
        Some((h, t)) => (h, Some(t)),
        None => (raw, None),
    };
    let head = match cond {
        Some(cc) if head.ends_with(cc) && head.len() > cc.len() => &head[..head.len() - cc.len()],
        _ => head,
    };
    match ty {
        Some("W") | Some("N") => head.to_string(),
        Some(t) => format!("{head}_{t}"),
        None => head.to_string(),
    }
}

/// An IT block header: `IT` followed by up to three T/E letters. It carries no operation -- capstone has already folded its condition onto the instructions it covers, which is where the guard/select reversal picks the predication up.
fn is_it_block(stem: &str) -> bool {
    stem.len() <= 5 && stem.starts_with("IT") && stem[2..].bytes().all(|c| c == b'T' || c == b'E')
}

fn leak(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

fn reg_of(cs: &Capstone, op: &ArmOperand) -> Option<A32Mreg> {
    match op.op_type {
        ArmOperandType::Reg(r) => Some(A32Mreg::from(capstone_reg_name(cs, r))),
        _ => None,
    }
}

/// Canonical name of a register operand slot, or "NONE"; goes through A32Mreg so a raw-string test like base == "SP" cannot silently never match.
fn reg_or_none(cs: &Capstone, reg: RegId) -> &'static str {
    if reg.0 == 0 {
        return "NONE";
    }
    A32Mreg::from(capstone_reg_name(cs, reg)).name()
}

/// Byte width of a load/store access. Integer A32 encodes the width in the
/// opcode; VLDR/VSTR use the transferred S/D register view for 4/8 bytes.
fn access_size(stem: &str, transferred: Option<A32Mreg>) -> usize {
    match stem {
        "LDRB" | "STRB" | "LDRSB" | "LDRBT" | "STRBT" | "LDREXB" | "STREXB" | "SWPB" => 1,
        "LDRH" | "STRH" | "LDRSH" | "LDRHT" | "STRHT" | "LDREXH" | "STREXH" => 2,
        "LDRD" | "STRD" | "LDREXD" | "STREXD" => 8,
        "VLDR" | "VSTR" if transferred.is_some_and(|reg| reg.is_double()) => 8,
        _ => 4,
    }
}

fn is_load_stem(stem: &str) -> bool {
    stem.starts_with("LDR") || stem.starts_with("VLDR")
}

fn is_store_stem(stem: &str) -> bool {
    stem.starts_with("STR")
        || stem.starts_with("VSTR")
        || stem.starts_with("VST")
        || stem.starts_with("STC")
        || stem.starts_with("SWP")
}

fn register_view_bytes(reg: A32Mreg) -> Option<usize> {
    if reg.is_single() {
        Some(4)
    } else if reg.is_double() {
        Some(8)
    } else if reg.is_quad() {
        Some(16)
    } else if reg.is_gp() {
        Some(4)
    } else {
        None
    }
}

fn fixed_memory_write_bytes(
    cs: &Capstone,
    stem: &str,
    ops: &[ArmOperand],
    vector_size_bits: i32,
    op_str: &str,
) -> Option<usize> {
    let mem_pos = ops
        .iter()
        .position(|op| matches!(op.op_type, ArmOperandType::Mem(_)))?;
    if stem.starts_with("STC") {
        return None;
    }
    // VSTM/VPUSH are multi-register transfers; expand_multi_transfer emits
    // their one total-width fact after resolving the register list.
    if stem.starts_with("VSTM") {
        return None;
    }
    if stem.starts_with("VST") && !stem.starts_with("VSTR") && !stem.starts_with("VSTM") {
        // Capstone 5 exposes a NEON lane in `cs_arm.neon_lane`, but
        // capstone-rs 0.13 does not carry that field into ArmOperand.  Keep
        // the structured operand as the primary source and use the decoded
        // register-list spelling only to recover that omitted lane marker.
        let lane_store = op_str
            .split_once('{')
            .and_then(|(_, tail)| tail.split_once('}'))
            .is_some_and(|(registers, _)| registers.contains('['));
        let lane_bytes = usize::try_from(vector_size_bits)
            .ok()
            .filter(|bits| *bits > 0 && *bits % 8 == 0)
            .map(|bits| bits / 8);
        return ops[..mem_pos].iter().try_fold(0usize, |total, op| {
            let reg = reg_of(cs, op)?;
            let width = if lane_store || op.vector_index.is_some() {
                lane_bytes?
            } else {
                register_view_bytes(reg)?
            };
            Some(total.saturating_add(width))
        });
    }
    is_store_stem(stem).then(|| access_size(stem, ops.first().and_then(|op| reg_of(cs, op))))
}

/// The LDM/STM family, including its PUSH/POP aliases; A32 carries whole prologues and epilogues in these.
fn multi_transfer_kind(stem: &str) -> Option<(bool, MultiMode, bool)> {
    // (is_load, addressing mode, base is implicitly SP with writeback)
    Some(match stem {
        "PUSH" | "VPUSH" => (false, MultiMode::Db, true),
        "POP" | "VPOP" => (true, MultiMode::Ia, true),
        "LDM" | "LDMIA" | "LDMFD" | "VLDMIA" => (true, MultiMode::Ia, false),
        "LDMIB" | "LDMED" => (true, MultiMode::Ib, false),
        "LDMDA" | "LDMFA" => (true, MultiMode::Da, false),
        "LDMDB" | "LDMEA" | "VLDMDB" => (true, MultiMode::Db, false),
        "STM" | "STMIA" | "STMEA" | "VSTMIA" => (false, MultiMode::Ia, false),
        "STMIB" | "STMFA" => (false, MultiMode::Ib, false),
        "STMDA" | "STMED" => (false, MultiMode::Da, false),
        "STMDB" | "STMFD" | "VSTMDB" => (false, MultiMode::Db, false),
        _ => return None,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MultiMode {
    Ia,
    Ib,
    Da,
    Db,
}

impl MultiMode {
    /// Offset of the LOWEST-addressed transferred register from the base, given the register count and slot width. In every mode the lowest-numbered register takes the lowest address.
    fn first_offset(&self, count: i64, width: i64) -> i64 {
        match self {
            MultiMode::Ia => 0,
            MultiMode::Ib => width,
            MultiMode::Da => -(count * width) + width,
            MultiMode::Db => -(count * width),
        }
    }

    /// How much writeback moves the base register.
    fn writeback_delta(&self, count: i64, width: i64) -> i64 {
        match self {
            MultiMode::Ia | MultiMode::Ib => count * width,
            MultiMode::Da | MultiMode::Db => -(count * width),
        }
    }
}

// One decoded A32 instruction after normalization, in the form the DB relations want. A predicated instruction expands to two of these: the guard branch and the unconditional operation.
struct Emitted {
    address: u64,
    size: usize,
    mnemonic: &'static str,
    op_str: &'static str,
    pc_source: PcSource,
    op_ids: [&'static str; 4],
}

/// Everything the decoder accumulates, kept in one struct because a single capstone instruction can contribute to eight relations at once.
#[derive(Default)]
struct Facts {
    op_registers: Vec<(&'static str, &'static str)>,
    op_immediates: Vec<(&'static str, i64, usize)>,
    op_indirects: Vec<(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        i64,
        i64,
        usize,
    )>,
    reg_defs: Vec<(u64, Mreg)>,
    reg_uses: Vec<(u64, Mreg)>,
    stack_defs: Vec<(u64, &'static str, i64)>,
    stack_uses: Vec<(u64, &'static str, i64)>,
    adjusts_stack: Vec<(u64, &'static str, i64)>,
    stack_base_moves: Vec<(u64, &'static str, &'static str)>,
    stack_base_move_offsets: Vec<(u64, &'static str, &'static str, i64)>,
    multi_transfers: Vec<(u64, bool, &'static str, &'static str, i64, usize)>,
    frame_setups: Vec<(u64,)>,
    literal_values: Vec<(u64, i64)>,
    pc_transfers: Vec<(u64, bool)>,
    shifted_operands: Vec<(&'static str, &'static str, i64)>,
    inplace_dests: Vec<(u64,)>,
    unmodelled: Vec<(u64,)>,
    memory_writes: Vec<(u64, usize)>,
    memory_write_unknown: Vec<(u64, &'static str)>,
    emitted: Vec<Emitted>,
}

pub fn disassemble_sections(db: &mut DecompileDB, obj: &object::File) -> Vec<DecodedInsn> {
    let engines = Engines::new();

    // Every section's bytes, for reading literal-pool constants back out of the image.
    let mut image: Vec<(u64, u64, &[u8])> = Vec::new();
    for section in obj.sections() {
        if let Ok(data) = section.data() {
            let start = section.address();
            if start != 0 && !data.is_empty() {
                image.push((start, start + data.len() as u64, data));
            }
        }
    }

    // A literal-pool word is never an ordinary symbol, so an ordinary symbol at a candidate address vetoes the detection. The ARM MAPPING symbols ($a/$t/$d) are excluded from the veto: a pool word carries a $d, which is the opposite of evidence against it. Bit 0 of a symbol value is the callee's instruction set, not part of the address, so it is cleared before comparing.
    let symbol_addrs: HashSet<u64> = named_symbols(obj)
        .filter(|(_, name)| !name.starts_with('$'))
        .map(|(a, _)| a & !1)
        .collect();
    let mapping = mapping_symbols(obj);
    let modes = recover_modes(obj, &engines, &mapping);

    let mut facts = Facts::default();

    for section in obj.sections() {
        if !is_executable_section(&section) {
            continue;
        }
        let Ok(data) = section.data() else { continue };
        let base_addr = section.address();
        let end_addr = base_addr + data.len() as u64;

        // A PC-relative load names its pool word relative to a base the instruction set decides, so the scan runs once per recovered mode run rather than once per section.
        let mut pools: BTreeMap<u64, u64> = BTreeMap::new();
        for (run_start, run_end, mode) in modes.runs(base_addr, end_addr) {
            let found = literal_pool_ranges(
                engines.get(mode),
                mode,
                data,
                (run_start, run_end),
                base_addr,
                end_addr,
                &symbol_addrs,
            );
            for (start, end) in found {
                let e = pools.entry(start).or_insert(end);
                *e = (*e).max(end);
            }
        }
        // Mapping symbols are the ARM ELF ABI's own declaration of which bytes in an executable section are data; where they survive, they cover pools no PC-relative load happened to reveal.
        for (start, end) in mapped_data_ranges(&mapping, base_addr, end_addr) {
            let e = pools.entry(start).or_insert(end);
            *e = (*e).max(end);
        }

        // Decode the complement of the pool ranges, further split at every instruction-set boundary. Working segment by segment rather than filtering afterwards is what keeps this correct for a variable-width encoding: Thumb re-syncs at each segment start instead of inheriting the pool's misalignment.
        for (seg_start, seg_end) in complement(base_addr, end_addr, &pools) {
            for (run_start, run_end, mode) in modes.runs(seg_start, seg_end) {
                let off = (run_start - base_addr) as usize;
                let len = (run_end - run_start) as usize;
                let cs = engines.get(mode);
                sweep(cs, mode, &data[off..off + len], run_start, |insn| {
                    decode_one(cs, mode, insn, &image, &mut facts)
                });
            }
        }
    }

    facts.emitted.sort_by_key(|e| e.address);

    let mut instructions: Vec<(
        u64,
        usize,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        usize,
        usize,
    )> = Vec::with_capacity(facts.emitted.len());
    let mut decoded: Vec<DecodedInsn> = Vec::with_capacity(facts.emitted.len());
    for e in &facts.emitted {
        instructions.push((
            e.address,
            e.size,
            "",
            e.mnemonic,
            e.op_ids[0],
            e.op_ids[1],
            e.op_ids[2],
            e.op_ids[3],
            0,
            0,
        ));
        decoded.push(DecodedInsn {
            address: e.address,
            size: e.size,
            mnemonic: e.mnemonic,
            op_str: e.op_str,
            pc_source: e.pc_source,
        });
    }

    // Adjacency is checked rather than assumed: a pool or a section end breaks the chain, and a split predicated instruction contributes two adjacent entries whose sizes still sum to the encoded width.
    let mut nexts: Vec<(u64, u64)> = Vec::with_capacity(decoded.len());
    for w in decoded.windows(2) {
        if w[0].address + w[0].size as u64 == w[1].address {
            nexts.push((w[0].address, w[1].address));
        }
    }

    db.rel_set(
        "unrefinedinstruction",
        instructions.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "next",
        nexts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_register",
        facts
            .op_registers
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_immediate",
        facts
            .op_immediates
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_indirect",
        facts
            .op_indirects
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_def",
        facts
            .stack_defs
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_use",
        facts
            .stack_uses
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "reg_def",
        facts
            .reg_defs
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "reg_use",
        facts
            .reg_uses
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "adjusts_stack",
        facts
            .adjusts_stack
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_base_move",
        facts
            .stack_base_moves
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_base_move_offset",
        facts
            .stack_base_move_offsets
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_multi_transfer",
        facts
            .multi_transfers
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_frame_setup",
        facts
            .frame_setups
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_literal_value",
        facts
            .literal_values
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_pc_transfer",
        facts
            .pc_transfers
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_shifted_operand",
        facts
            .shifted_operands
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_inplace_dest",
        facts
            .inplace_dests
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "arm_unmodelled",
        facts
            .unmodelled
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_memory_write_bytes",
        facts
            .memory_writes
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_memory_write_unknown",
        facts
            .memory_write_unknown
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    decoded
}

/// Every named symbol in the image, static and dynamic.
fn named_symbols<'a>(obj: &'a object::File) -> impl Iterator<Item = (u64, &'a str)> + 'a {
    use object::ObjectSymbol;
    obj.symbols()
        .chain(obj.dynamic_symbols())
        .filter_map(|s| s.name().ok().map(|n| (s.address(), n)))
}

/// What an ARM ELF mapping symbol declares about the bytes it opens.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum MapKind {
    Code(u8),
    Data,
}

/// The ARM ELF mapping symbols in address order: `$d` opens data, `$a` and `$t` open A32 and Thumb code. The `.N` suffix linkers append is part of the name, so the kind is the first two characters.
fn mapping_symbols(obj: &object::File) -> Vec<(u64, MapKind)> {
    let mut v: Vec<(u64, MapKind)> = named_symbols(obj)
        .filter_map(|(addr, name)| match name.get(..2) {
            Some("$d") => Some((addr, MapKind::Data)),
            Some("$a") => Some((addr, MapKind::Code(IsaMode::Arm.tag()))),
            Some("$t") => Some((addr, MapKind::Code(IsaMode::Thumb.tag()))),
            _ => None,
        })
        .collect();
    v.sort();
    v.dedup();
    v
}

/// Where the run a mapping symbol opens ends: at the next mapping symbol of any kind, or at the section end.
fn mapping_run_end(mapping: &[(u64, MapKind)], i: usize, end: u64) -> u64 {
    mapping
        .get(i + 1)
        .map(|(next, _)| *next)
        .filter(|next| *next > mapping[i].0)
        .unwrap_or(end)
        .min(end)
}

/// Data ranges inside [start, end) declared by the mapping symbols: each `$d` runs until the next mapping symbol of any kind, or the section end.
fn mapped_data_ranges(mapping: &[(u64, MapKind)], start: u64, end: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    for (i, (addr, kind)) in mapping.iter().enumerate() {
        if *kind != MapKind::Data || *addr < start || *addr >= end {
            continue;
        }
        let stop = mapping_run_end(mapping, i, end);
        if stop > *addr {
            out.push((*addr, stop));
        }
    }
    out
}

/// Read one ULEB128 out of `d` at `p`, advancing `p`.
fn uleb(d: &[u8], p: &mut usize) -> u64 {
    let (mut v, mut shift) = (0u64, 0u32);
    while *p < d.len() {
        let b = d[*p];
        *p += 1;
        v |= ((b & 0x7f) as u64) << shift;
        shift += 7;
        if b & 0x80 == 0 || shift >= 64 {
            break;
        }
    }
    v
}

/// Skip one NUL-terminated string at `p`.
fn skip_ntbs(d: &[u8], p: &mut usize) {
    while *p < d.len() && d[*p] != 0 {
        *p += 1;
    }
    *p += 1;
}

// The ARM ABI's build attributes are the producer's own declaration of which instruction sets the image's code uses, so a file that permits one and forbids the other cannot contain the other. That is a statement about the bytes, not a guess about them, which makes it the strongest mode evidence available on a stripped image -- and stripped M-profile firmware, which has no ARM state at all, is exactly where mapping symbols are gone.
fn declared_isa(obj: &object::File) -> Option<IsaMode> {
    let section = obj.section_by_name(".ARM.attributes")?;
    let data = section.data().ok()?;
    if data.first() != Some(&b'A') {
        return None;
    }
    // Tag numbers from the ABI addenda: 7 = CPU_arch_profile, 8 = ARM_ISA_use, 9 = THUMB_ISA_use.
    let (mut profile, mut arm_isa, mut thumb_isa) = (None, None, None);
    let mut sub = 1usize;
    while sub + 4 <= data.len() {
        let len = u32::from_le_bytes(data[sub..sub + 4].try_into().ok()?) as usize;
        if len < 5 || sub + len > data.len() {
            break;
        }
        let body = &data[sub..sub + len];
        sub += len;
        let mut p = 4usize;
        let vendor_start = p;
        skip_ntbs(body, &mut p);
        if body.get(vendor_start..p.saturating_sub(1)) != Some(b"aeabi") {
            continue;
        }
        // Attribute sub-subsections: a scope tag, a byte length covering both, then tag/value pairs. Only the whole-file scope (tag 1) describes the image.
        while p < body.len() {
            let scope = body[p];
            p += 1;
            if p + 4 > body.len() {
                break;
            }
            let sz = u32::from_le_bytes(body[p..p + 4].try_into().ok()?) as usize;
            p += 4;
            if sz < 5 {
                break;
            }
            let end = (p + sz - 5).min(body.len());
            if scope != 1 {
                p = end;
                continue;
            }
            while p < end {
                let tag = uleb(body, &mut p);
                // Value encoding: tags 4, 5 and 67 are strings, tag 32 is an integer then a string, and above 32 an odd tag is a string and an even one an integer.
                match tag {
                    4 | 5 | 67 => skip_ntbs(body, &mut p),
                    32 => {
                        uleb(body, &mut p);
                        skip_ntbs(body, &mut p);
                    }
                    t if t > 32 && t % 2 == 1 => skip_ntbs(body, &mut p),
                    t => {
                        let v = uleb(body, &mut p);
                        match t {
                            7 => profile = Some(v),
                            8 => arm_isa = Some(v),
                            9 => thumb_isa = Some(v),
                            _ => {}
                        }
                    }
                }
            }
            p = end;
        }
    }
    // The Microcontroller profile executes Thumb only; there is no ARM state to switch to.
    if profile == Some(b'M' as u64) {
        return Some(IsaMode::Thumb);
    }
    match (arm_isa, thumb_isa) {
        (Some(0), Some(t)) if t > 0 => Some(IsaMode::Thumb),
        (Some(a), Some(0)) if a > 0 => Some(IsaMode::Arm),
        _ => None,
    }
}

/// Per-byte instruction-set assignment over the executable sections, plus the mode any byte with no evidence takes.
struct ModeMap {
    default: IsaMode,
    sections: Vec<(u64, Vec<u8>)>,
}

impl ModeMap {
    fn tags_for(&self, addr: u64) -> Option<(&Vec<u8>, usize)> {
        for (base, tags) in &self.sections {
            if addr >= *base && addr < *base + tags.len() as u64 {
                return Some((tags, (addr - base) as usize));
            }
        }
        None
    }

    fn mode_at(&self, addr: u64) -> IsaMode {
        self.tags_for(addr)
            .and_then(|(tags, off)| IsaMode::from_tag(tags[off]))
            .unwrap_or(self.default)
    }

    /// Split [start, end) into maximal runs of one mode.
    fn runs(&self, start: u64, end: u64) -> Vec<(u64, u64, IsaMode)> {
        let mut out: Vec<(u64, u64, IsaMode)> = Vec::new();
        let mut addr = start;
        while addr < end {
            let m = self.mode_at(addr);
            match out.last_mut() {
                Some(last) if last.2 == m && last.1 == addr => last.1 = addr + 1,
                _ => out.push((addr, addr + 1, m)),
            }
            addr += 1;
        }
        out
    }
}

/// Instruction-set claims in descending order of strength. Every tier is drained to a fixpoint before the next one starts, so a weaker claim can only reach bytes no stronger one did.
struct ModeSeeds {
    /// The loader's own entry state and the interworking bit of a declared function symbol: both name the mode of a known code address.
    declared: Vec<(u64, IsaMode)>,
    /// A word in data that looks like a function pointer. Sound where the word really is one -- a vector table, a vtable -- and a guess where it is only an integer that happens to fall in the code range, hence last.
    inferred: Vec<(u64, IsaMode)>,
}

// Mode is recovered, never assumed. In descending order of strength: the ARM ELF mapping symbols, which state it per address; the build attributes, which state it for the whole image; and the interworking bit that the ELF entry point, every STT_FUNC symbol value and every code pointer stored in data all carry in bit 0. From those seeds it travels along the CFG -- B and BL preserve the state, BLX toggles it -- which is a structural derivation: an address is claimed only by decoding an instruction that transfers to it.
fn recover_modes(obj: &object::File, engines: &Engines, mapping: &[(u64, MapKind)]) -> ModeMap {
    let mut sections: Vec<(u64, Vec<u8>)> = Vec::new();
    let mut exec: Vec<(u64, u64)> = Vec::new();
    for section in obj.sections() {
        if !is_executable_section(&section) {
            continue;
        }
        let Ok(data) = section.data() else { continue };
        if data.is_empty() {
            continue;
        }
        sections.push((section.address(), vec![0u8; data.len()]));
        exec.push((section.address(), section.address() + data.len() as u64));
    }

    let declared = declared_isa(obj);
    let entry_mode = match obj.entry() {
        0 => None,
        e if e & 1 == 1 => Some(IsaMode::Thumb),
        _ => Some(IsaMode::Arm),
    };
    // A byte with no evidence of its own takes the ISA the file declares, and failing that the one the loader enters in; A32 is the fallback because it is the state a processor without the interworking bit starts in.
    let default = declared.or(entry_mode).unwrap_or(IsaMode::Arm);
    let mut map = ModeMap { default, sections };

    // Mapping symbols first: they declare the mode of every byte they cover.
    for (i, (addr, kind)) in mapping.iter().enumerate() {
        let MapKind::Code(tag) = kind else { continue };
        let Some((_, base_end)) = exec.iter().find(|(s, e)| addr >= s && addr < e).copied() else {
            continue;
        };
        let stop = mapping_run_end(mapping, i, base_end);
        for (base, tags) in map.sections.iter_mut() {
            if *addr < *base || *addr >= *base + tags.len() as u64 {
                continue;
            }
            let from = (*addr - *base) as usize;
            let to = ((stop - *base) as usize).min(tags.len());
            for t in &mut tags[from..to] {
                if *t == 0 {
                    *t = *tag;
                }
            }
        }
    }

    // A file that permits only one instruction set settles every remaining byte, so there is nothing left to propagate.
    if declared.is_none() {
        let seeds = collect_mode_seeds(obj, &exec, entry_mode);
        propagate_modes(engines, obj, &mut map, &seeds);
    }
    map
}

/// Interworking-bit evidence: bit 0 of the entry point, of every STT_FUNC symbol value, and of every code pointer stored in data. Per ELF for the ARM Architecture that bit IS the callee's instruction set, so a set bit is exact evidence of Thumb and a clear one of A32.
fn collect_mode_seeds(
    obj: &object::File,
    exec: &[(u64, u64)],
    entry_mode: Option<IsaMode>,
) -> ModeSeeds {
    use object::ObjectSymbol;
    let in_exec = |a: u64| exec.iter().any(|(s, e)| a >= *s && a < *e);
    let mut declared: Vec<(u64, IsaMode)> = Vec::new();
    let mut inferred: Vec<(u64, IsaMode)> = Vec::new();

    if let Some(m) = entry_mode {
        let target = obj.entry() & !1;
        if in_exec(target) {
            declared.push((target, m));
        }
    }

    for sym in obj.symbols().chain(obj.dynamic_symbols()) {
        if sym.kind() != object::SymbolKind::Text {
            continue;
        }
        let v = sym.address();
        let target = v & !1;
        if v != 0 && in_exec(target) {
            declared.push((
                target,
                if v & 1 == 1 {
                    IsaMode::Thumb
                } else {
                    IsaMode::Arm
                },
            ));
        }
    }

    // A pointer-sized word in non-executable memory whose value points into code is a function pointer -- a vector table entry, a vtable slot, a jump table entry. Only a SET bit 0 counts, since it is meaningless for anything but an ARM32 code address, and only inside a RUN of at least two adjacent such slots: a table of function pointers is what carries this evidence, while a lone word that happens to look like one is as likely to be an integer.
    for section in obj.sections() {
        if is_executable_section(&section) || section.address() == 0 {
            continue;
        }
        let Ok(data) = section.data() else { continue };
        let mut run: Vec<u64> = Vec::new();
        for off in (0..data.len().saturating_sub(3)).step_by(4) {
            let v = u32::from_le_bytes(data[off..off + 4].try_into().unwrap()) as u64;
            if v & 1 == 1 && in_exec(v & !1) {
                run.push(v & !1);
                continue;
            }
            if run.len() >= 2 {
                inferred.extend(run.iter().map(|t| (*t, IsaMode::Thumb)));
            }
            run.clear();
        }
        if run.len() >= 2 {
            inferred.extend(run.iter().map(|t| (*t, IsaMode::Thumb)));
        }
    }

    for v in [&mut declared, &mut inferred] {
        v.sort();
        v.dedup();
    }
    ModeSeeds { declared, inferred }
}

/// Follow control flow from each seed, tagging the bytes every reached instruction occupies with the mode it decoded in. An address is claimed only by decoding an instruction that transfers to it; nothing here compares addresses to decide what reaches what.
fn propagate_modes(engines: &Engines, obj: &object::File, map: &mut ModeMap, seeds: &ModeSeeds) {
    let mut bodies: Vec<(u64, &[u8])> = Vec::new();
    for section in obj.sections() {
        if !is_executable_section(&section) {
            continue;
        }
        if let Ok(data) = section.data() {
            if !data.is_empty() {
                bodies.push((section.address(), data));
            }
        }
    }

    for tier in [&seeds.declared, &seeds.inferred] {
        propagate_tier(engines, &bodies, map, tier);
    }
}

// Sweep a run of bytes, RESYNCHRONIZING past anything that does not decode. capstone stops at the first undecodable byte and reports nothing after it, so a single constant, alignment pad or jump table sitting in a code section would otherwise silence the rest of that section -- which on a 300KB firmware image means losing all of it. Resuming at the next instruction slot is sound because both instruction sets are fixed-alignment: A32 instructions start every 4 bytes and Thumb halfwords every 2, so no real instruction can begin at a skipped offset.
fn sweep(
    cs: &Capstone,
    mode: IsaMode,
    data: &[u8],
    addr: u64,
    mut visit: impl FnMut(&capstone::Insn),
) {
    let step = mode.alignment();
    let mut off = 0usize;
    while off < data.len() {
        let run_start = addr + off as u64;
        let Ok(insns) = cs.disasm_all(&data[off..], run_start) else {
            break;
        };
        let mut consumed = 0usize;
        for insn in insns.as_ref() {
            visit(insn);
            consumed = (insn.address() - run_start) as usize + insn.len();
        }
        if consumed == 0 {
            off += step;
            continue;
        }
        off += consumed;
        // Stopping short of the end means capstone hit a byte pattern it cannot decode; step over one slot and pick the stream back up.
        if off < data.len() {
            off += step;
        }
    }
}

/// Whether an address lies inside one of the executable section bodies.
fn in_section(bodies: &[(u64, &[u8])], addr: u64) -> bool {
    bodies
        .iter()
        .any(|(b, d)| addr >= *b && addr < *b + d.len() as u64)
}

/// Drain one tier of seeds to a fixpoint. Bytes an earlier tier already claimed are left alone, which is what makes the tier order a strength order.
fn propagate_tier(
    engines: &Engines,
    bodies: &[(u64, &[u8])],
    map: &mut ModeMap,
    tier: &[(u64, IsaMode)],
) {
    let mut work: Vec<(u64, IsaMode)> = tier.to_vec();
    while let Some((addr, mode)) = work.pop() {
        let Some((base, data)) = bodies
            .iter()
            .find(|(b, d)| addr >= *b && addr < *b + d.len() as u64)
        else {
            continue;
        };
        let off = (addr - base) as usize;
        let Some((_, tags)) = map.sections.iter_mut().find(|(b, _)| *b == *base) else {
            continue;
        };
        if tags[off] != 0 {
            continue;
        }
        let cs = engines.get(mode);
        let Ok(insns) = cs.disasm_count(&data[off..], addr, 1) else {
            continue;
        };
        let Some(insn) = insns.as_ref().first() else {
            continue;
        };
        let size = insn.len();
        if size == 0 || off + size > tags.len() {
            continue;
        }
        for t in &mut tags[off..off + size] {
            *t = mode.tag();
        }

        let Ok(detail) = cs.insn_detail(insn) else {
            continue;
        };
        let arch_detail = detail.arch_detail();
        let Some(a) = arch_detail.arm() else { continue };
        let ops: Vec<ArmOperand> = a.operands().collect();
        let raw = insn.mnemonic().unwrap_or("").to_ascii_uppercase();
        let cond = cc_name(a.cc());
        let stem = opcode_stem(&raw, cond);

        // A direct branch or call names its target; BL keeps the state and BLX toggles it, which is the whole of ARM32 interworking that is decidable without dataflow.
        let imm = ops.iter().find_map(|o| match o.op_type {
            ArmOperandType::Imm(v) if v >= 0 => Some(v as u64),
            _ => None,
        });
        match stem.as_str() {
            "B" | "BL" | "CBZ" | "CBNZ" => {
                if let Some(t) = imm {
                    work.push((t, mode));
                }
            }
            "BLX" => {
                if let Some(t) = imm {
                    work.push((t & !1, mode.toggled()));
                }
            }
            _ => {}
        }

        // `BX Rm` and `BLX Rm` take the new state from bit 0 of a register VALUE, which is a dataflow question in general. It is decidable exactly when the value is a constant the code loads out of a literal pool: a pool word pointing into executable memory with bit 0 set is a Thumb entry, and nothing else in ARM32 spells an odd code address. An EVEN such word is deliberately not read as an A32 entry -- it is just as likely to be the address of a table that happens to live in the code section.
        if is_load_stem(&stem) {
            for op in &ops {
                let Some(target) = pc_relative_target(cs, mode, addr, op) else {
                    continue;
                };
                let Some(word) = read_field(data, *base, target, 4) else {
                    continue;
                };
                if word & 1 == 1 && in_section(bodies, word & !1) {
                    work.push((word & !1, IsaMode::Thumb));
                }
            }
        }

        // Fall-through, unless the transfer is unconditional and never comes back. A PC-writing form (BX, POP {..,PC}, a table branch) has no statically known target at all.
        let writes_pc = matches!(stem.as_str(), "BX" | "BXJ" | "TBB" | "TBH")
            || ops.iter().any(|o| {
                reg_of(cs, o) == Some(A32Mreg::PC)
                    && o.access.map_or(false, |acc| acc.is_writable())
            });
        let terminal = writes_pc || matches!(stem.as_str(), "B" | "UDF" | "BKPT" | "HLT" | "TRAP");
        if !terminal || cond.is_some() {
            work.push((addr + size as u64, mode));
        }
    }
}

/// Read a little-endian word of `size` bytes out of the loaded image.
fn read_le(image: &[(u64, u64, &[u8])], addr: u64, size: usize) -> Option<i64> {
    for (start, end, data) in image {
        if addr >= *start && addr + size as u64 <= *end {
            let off = (addr - start) as usize;
            let mut v: u64 = 0;
            for i in (0..size).rev() {
                v = (v << 8) | data[off + i] as u64;
            }
            return Some(match size {
                4 => v as u32 as i32 as i64,
                _ => v as i64,
            });
        }
    }
    None
}

/// Address a PC-relative memory operand refers to, or None when the operand is not PC-relative. The base the PC reads as differs between the two instruction sets, so it comes from the mode the bytes were decoded in.
fn pc_relative_target(cs: &Capstone, mode: IsaMode, addr: u64, op: &ArmOperand) -> Option<u64> {
    let ArmOperandType::Mem(mem) = &op.op_type else {
        return None;
    };
    if reg_or_none(cs, mem.base()) != "PC" {
        return None;
    }
    // An indexed [PC, Rm] form is a jump table, not a single constant.
    if reg_or_none(cs, mem.index()) != "NONE" {
        return None;
    }
    let disp = mem.disp() as i64;
    let disp = if op.subtracted { -disp.abs() } else { disp };
    mode.pc_base(addr).checked_add_signed(disp)
}

// Data that sits INSIDE a code section, which a linear sweep would otherwise decode as garbage instructions: literal pools, and the branch tables Thumb's TBB/TBH read. Neither is recognizable from the bytes themselves -- they are arbitrary constants -- so both are found through the instruction that refers to them.
#[allow(clippy::too_many_arguments)]
fn literal_pool_ranges(
    cs: &Capstone,
    mode: IsaMode,
    sec_data: &[u8],
    scan: (u64, u64),
    base_addr: u64,
    end_addr: u64,
    symbol_addrs: &HashSet<u64>,
) -> BTreeMap<u64, u64> {
    let mut ranges: BTreeMap<u64, u64> = BTreeMap::new();
    let (scan_addr, scan_end) = scan;
    let from = (scan_addr - base_addr) as usize;
    let to = (scan_end - base_addr) as usize;
    sweep(cs, mode, &sec_data[from..to], scan_addr, |insn| {
        let addr = insn.address();
        let Ok(detail) = cs.insn_detail(insn) else {
            return;
        };
        let arch_detail = detail.arch_detail();
        let Some(a) = arch_detail.arm() else { return };
        let raw = insn.mnemonic().unwrap_or("").to_ascii_uppercase();
        let stem = opcode_stem(&raw, cc_name(a.cc()));
        let ops: Vec<ArmOperand> = a.operands().collect();

        if matches!(stem.as_str(), "TBB" | "TBH") {
            if let Some((start, end)) =
                table_branch_range(cs, &stem, &ops, addr, sec_data, base_addr, end_addr)
            {
                let e = ranges.entry(start).or_insert(end);
                *e = (*e).max(end);
            }
            return;
        }

        if !is_load_stem(&stem) {
            return;
        }
        let size = access_size(&stem, ops.first().and_then(|op| reg_of(cs, op))) as u64;
        for op in &ops {
            let Some(target) = pc_relative_target(cs, mode, addr, op) else {
                continue;
            };
            // A pool word is aligned, lives inside this section, and is never a symbol; each condition rejects a garbage-decoded byte pattern that happened to look like a PC-relative load.
            if target % 4 != 0 || target < base_addr || target + size > end_addr {
                continue;
            }
            if symbol_addrs.contains(&target) {
                continue;
            }
            let entry = ranges.entry(target).or_insert(target + size);
            *entry = (*entry).max(target + size);
        }
    });
    ranges
}

/// Read an unsigned little-endian field of `size` bytes at `addr` out of one section's bytes.
fn read_field(sec_data: &[u8], base_addr: u64, addr: u64, size: usize) -> Option<u64> {
    let off = addr.checked_sub(base_addr)? as usize;
    let bytes = sec_data.get(off..off + size)?;
    Some(
        bytes
            .iter()
            .rev()
            .fold(0u64, |acc, b| (acc << 8) | *b as u64),
    )
}

// `TBB [PC, Rn]` / `TBH [PC, Rn, LSL #1]` read a table of halfword offsets laid out immediately after the instruction, inside the code. The table's extent is not encoded anywhere, but it is pinned by its own contents: every entry names a target past the end of the table it belongs to, so the smallest target seen so far bounds how far the table can run. That is a statement about the table's layout, not about what reaches what.
#[allow(clippy::too_many_arguments)]
fn table_branch_range(
    cs: &Capstone,
    stem: &str,
    ops: &[ArmOperand],
    addr: u64,
    sec_data: &[u8],
    base_addr: u64,
    end_addr: u64,
) -> Option<(u64, u64)> {
    let mem = ops.iter().find_map(|o| match &o.op_type {
        ArmOperandType::Mem(m) => Some(m),
        _ => None,
    })?;
    if reg_or_none(cs, mem.base()) != "PC" || reg_or_none(cs, mem.index()) == "NONE" {
        return None;
    }
    let width: u64 = if stem == "TBB" { 1 } else { 2 };
    // A table branch reads the PC as the address of the instruction plus four, with no rounding.
    let start = addr + 4;
    let mut end = u64::MAX;
    let mut pos = start;
    while pos < end && pos + width <= end_addr {
        let entry = read_field(sec_data, base_addr, pos, width as usize)?;
        let target = start.checked_add(2 * entry)?;
        // An entry that lands inside the table it belongs to, or outside the section, is not a table entry: the run of real entries has ended.
        if target <= pos + width || target > end_addr {
            break;
        }
        end = end.min(target);
        pos += width;
    }
    if end == u64::MAX || end <= start {
        return None;
    }
    Some((start, end))
}

/// The half-open sub-ranges of [start, end) not covered by any pool.
fn complement(start: u64, end: u64, pools: &BTreeMap<u64, u64>) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut cur = start;
    for (&ps, &pe) in pools {
        if pe <= cur {
            continue;
        }
        if ps > cur {
            out.push((cur, ps.min(end)));
        }
        cur = cur.max(pe);
        if cur >= end {
            break;
        }
    }
    if cur < end {
        out.push((cur, end));
    }
    out.retain(|(a, b)| b > a);
    out
}

/// Where this instruction's new PC comes from, when it writes the PC at all. The distinction the CFG needs is return versus jump table, so the test is structural: the saved return address arrives from LR or from a stack slot, anything else is computed.
fn pc_source_of(
    cs: &Capstone,
    stem: &str,
    ops: &[ArmOperand],
    writes_pc: bool,
    multi_base: Option<&str>,
) -> PcSource {
    if !writes_pc {
        return PcSource::NotWritten;
    }
    match stem {
        // BX/BLX Rm: a return exactly when Rm is the link register.
        "BX" | "BXJ" => {
            return match ops.first().and_then(|o| reg_of(cs, o)) {
                Some(A32Mreg::LR) => PcSource::SavedReturnAddress,
                _ => PcSource::Computed,
            }
        }
        _ => {}
    }
    // POP {..,PC} / LDM SP!, {..,PC}: the return address comes off the stack.
    if let Some(base) = multi_base {
        return if base == "SP" {
            PcSource::SavedReturnAddress
        } else {
            PcSource::Computed
        };
    }
    // MOV PC, LR.
    if ops.len() >= 2 {
        if let Some(A32Mreg::LR) = reg_of(cs, &ops[1]) {
            return PcSource::SavedReturnAddress;
        }
        // LDR PC, [SP, #n] / LDR PC, [SP], #4 restores a spilled return address; LDR PC, [PC, Rm, LSL#2] is a jump table.
        if let ArmOperandType::Mem(mem) = &ops[1].op_type {
            if reg_or_none(cs, mem.base()) == "SP" && reg_or_none(cs, mem.index()) == "NONE" {
                return PcSource::SavedReturnAddress;
            }
        }
    }
    PcSource::Computed
}

/// The shift kind of a register operand, when it carries one; LSL is reported separately because it is the only kind the shared Addressing alphabet can scale by.
fn shift_parts(shift: ArmShift) -> Option<(&'static str, i64)> {
    Some(match shift {
        ArmShift::Lsl(n) => ("LSL", n as i64),
        ArmShift::Lsr(n) => ("LSR", n as i64),
        ArmShift::Asr(n) => ("ASR", n as i64),
        ArmShift::Ror(n) => ("ROR", n as i64),
        ArmShift::Rrx(n) => ("RRX", n as i64),
        _ => return None,
    })
}

fn decode_one(
    cs: &Capstone,
    mode: IsaMode,
    insn: &capstone::Insn,
    image: &[(u64, u64, &[u8])],
    facts: &mut Facts,
) {
    let addr = insn.address();
    let size = insn.len();
    let raw = insn.mnemonic().unwrap_or("").to_ascii_uppercase();
    let op_str: &'static str = leak(insn.op_str().unwrap_or("").to_ascii_uppercase());

    let Ok(detail) = cs.insn_detail(insn) else {
        return;
    };
    let arch_detail = detail.arch_detail();
    let Some(a) = arch_detail.arm() else { return };
    let ops: Vec<ArmOperand> = a.operands().collect();
    let cond = cc_name(a.cc());
    let stem = opcode_stem(&raw, cond);
    let writeback = a.writeback();
    let vector_size_bits = a.vector_size();

    // Thumb's IT header states the predicate of the instructions that follow it, and capstone has already applied that predicate to each of them. The header itself computes nothing, so it is emitted as a bare node -- keeping the instruction stream contiguous, which the fall-through chain depends on -- and contributes no operation, no condition and no register traffic.
    if is_it_block(&stem) {
        facts.emitted.push(Emitted {
            address: addr,
            size,
            mnemonic: leak(stem),
            op_str,
            pc_source: PcSource::NotWritten,
            op_ids: [NO_OP; 4],
        });
        return;
    }

    let multi = multi_transfer_kind(&stem);
    let multi_base: Option<&'static str> = multi.map(|(_, _, sp_implicit)| {
        if sp_implicit {
            "SP"
        } else {
            ops.first()
                .and_then(|o| reg_of(cs, o))
                .map(|r| r.name())
                .unwrap_or("NONE")
        }
    });

    // ARM32 writes R15 as an ordinary destination; capstone reports that as a written register operand, and for LDM/POP as PC in the transfer list. Thumb's table branches reach their target the same way, through a PC write the operand list does not spell.
    let writes_pc = matches!(stem.as_str(), "BX" | "BXJ" | "TBB" | "TBH")
        || ops.iter().enumerate().any(|(i, o)| {
            reg_of(cs, o) == Some(A32Mreg::PC)
                && (o.access.map_or(false, |acc| acc.is_writable())
                    || (multi.map_or(false, |(is_load, _, _)| is_load) && i > 0))
        });
    let pc_source = pc_source_of(cs, &stem, &ops, writes_pc, multi_base);

    // A predicated instruction is if-converted code. Reversing it needs a select when both candidate values already sit in registers and there is no memory effect, and a real branch otherwise -- a conditional load, store or computed value has no faithful select form.
    // A predicated plain B is already an ordinary conditional branch and is left alone; a predicated BL/BX is not, and is split like any other predicated instruction.
    let keep_as_select = cond.is_some() && is_select_shaped(cs, &stem, &ops);
    // The guard branches on the INVERTED predicate, so a condition with no inverse cannot be split. Deciding that here, rather than when the guard is emitted, is what stops an unguardable predicated instruction from being emitted as an unconditional one.
    let guard_cc = cond
        .filter(|_| !keep_as_select && stem != "B")
        .and_then(invert_cc);
    let split = guard_cc.is_some();

    // Address the real operation lands at. Nothing here assumes a width: the guard takes one byte at `addr` and the operation the rest, which works for any encoding of two bytes or more, so a 2-byte Thumb instruction splits exactly as a 4-byte A32 one does.
    let (guard_addr, body_addr, body_size) = if split {
        (Some(addr), addr + 1, size - 1)
    } else {
        (None, addr, size)
    };

    // A predicated instruction that could be neither turned into a select nor guarded is a loss the frontend must not hide: its effect would otherwise be emitted as unconditional.
    if cond.is_some() && !keep_as_select && !split && stem != "B" {
        facts.unmodelled.push((addr,));
    }

    if let (Some(gaddr), Some(cc)) = (guard_addr, guard_cc) {
        // The guard skips the operation when the predicate fails, so it branches on the INVERTED condition to the instruction after the whole encoded instruction.
        let target = alloc_op_id();
        facts
            .op_immediates
            .push((target, (addr + size as u64) as i64, 0));
        facts.emitted.push(Emitted {
            address: gaddr,
            size: 1,
            mnemonic: leak(format!("B.{cc}")),
            op_str,
            pc_source: PcSource::NotWritten,
            op_ids: [target, NO_OP, NO_OP, NO_OP],
        });
    }

    // The condition survives on exactly the instructions that were NOT split: a conditional branch (B.NE) and a kept select (MOV.GT) both still consume the flags, and cfg.rs pairs them with their flag setter through the dotted spelling.
    let mnemonic: &'static str = match cond {
        Some(cc) if !split => leak(format!("{stem}.{cc}")),
        _ => leak(stem.clone()),
    };

    let mut op_ids: [&'static str; 4] = [NO_OP; 4];
    let transferred = ops.first().and_then(|op| reg_of(cs, op));
    let mem_size = access_size(&stem, transferred);
    // Multi-register transfers publish one total-width fact from their
    // expansion below; treating their memory operand as a second scalar store
    // would double-count the instruction.
    let memory_write_bytes = multi
        .is_none()
        .then(|| fixed_memory_write_bytes(cs, &stem, &ops, vector_size_bits, op_str))
        .flatten();
    let memory_write_unknown = stem.starts_with("STC").then_some("coprocessor-store-width");

    for (i, op) in ops.iter().enumerate() {
        match &op.op_type {
            ArmOperandType::Reg(reg_id) => {
                let name = capstone_reg_name(cs, *reg_id);
                let reg = A32Mreg::from(name);
                if i < 4 {
                    let id = alloc_op_id();
                    facts.op_registers.push((id, reg.name()));
                    op_ids[i] = id;
                    if let Some((kind, amount)) = shift_parts(op.shift) {
                        facts.shifted_operands.push((id, kind, amount));
                    }
                }
                // The PC is control state, not a value: a POP that restores it is a return, and an ADD that computes it is a jump, both already recorded as arm_pc_transfer. Recording it as an ordinary def or use would put control flow into the dataflow graph.
                if reg == A32Mreg::Unknown || reg == A32Mreg::PC {
                    continue;
                }
                let mreg = Mreg::a32(reg);
                // capstone reports A32 operand access directly, unlike arm64; the register list of an LDM/POP is written and of an STM/PUSH read, which its access flags already say.
                if op.access.map_or(false, |acc| acc.is_writable()) {
                    facts.reg_defs.push((body_addr, mreg));
                }
                if op.access.map_or(false, |acc| acc.is_readable()) {
                    facts.reg_uses.push((body_addr, mreg));
                }
            }
            ArmOperandType::Imm(v) => {
                if i < 4 {
                    let id = alloc_op_id();
                    facts.op_immediates.push((id, *v as i64, 0));
                    op_ids[i] = id;
                }
            }
            ArmOperandType::Mem(mem) => {
                let base = reg_or_none(cs, mem.base());
                let index = reg_or_none(cs, mem.index());
                // The scale of an indexed access lives on the operand's shifter ([Rn, Rm, LSL #2]); only LSL is a scale, so any other shift kind leaves the addressing unmodelled rather than silently wrong.
                let (scale, modelled) = match op.shift {
                    ArmShift::Invalid => (1i64, true),
                    ArmShift::Lsl(n) => (1i64 << n, true),
                    _ => (1i64, false),
                };
                if !modelled {
                    facts.unmodelled.push((body_addr,));
                    continue;
                }
                let disp = mem.disp() as i64;
                let disp = if op.subtracted { -disp.abs() } else { disp };

                // A PC-relative load reads a literal pool word: resolve it here, where the image is in hand, so the frontend can materialize a constant instead of a load from code.
                if base == "PC" && index == "NONE" {
                    if let Some(target) = pc_relative_target(cs, mode, addr, op) {
                        if let Some(v) = read_le(image, target, mem_size) {
                            facts.literal_values.push((body_addr, v));
                        }
                    }
                }

                if i < 4 {
                    let id = alloc_op_id();
                    facts
                        .op_indirects
                        .push((id, "NONE", base, index, scale, disp, mem_size));
                    op_ids[i] = id;
                }

                for r in [base, index] {
                    let reg = A32Mreg::from(r);
                    if reg != A32Mreg::Unknown && reg != A32Mreg::PC {
                        facts.reg_uses.push((body_addr, Mreg::a32(reg)));
                    }
                }
                // Pre- and post-index addressing writes the base back.
                if writeback && base != "NONE" {
                    let reg = A32Mreg::from(base);
                    if reg != A32Mreg::Unknown {
                        facts.reg_defs.push((body_addr, Mreg::a32(reg)));
                    }
                }
                // Frame-relative access. The AAPCS frame pointer is R11 in ARM state and R7 in Thumb state, where the 16-bit encodings cannot reach the high registers.
                if is_frame_setup(base, writeback) {
                    facts.frame_setups.push((body_addr,));
                } else if (base == "SP" || base == mode.frame_reg()) && index == "NONE" {
                    if is_store_stem(&stem) {
                        facts.stack_defs.push((body_addr, base, disp));
                    } else {
                        facts.stack_uses.push((body_addr, base, disp));
                    }
                }
            }
            _ => {}
        }
    }

    if let Some(bytes) = memory_write_bytes {
        facts.memory_writes.push((body_addr, bytes));
    }
    if let Some(reason) = memory_write_unknown {
        facts.memory_write_unknown.push((body_addr, reason));
    }

    // Thumb's 16-bit data-processing encodings have no room for a separate destination: `ADD Rd, Rm` means `Rd := Rd + Rm`, which capstone reports as a two-operand form whose first operand is read AND written. Publishing that here keeps the arch-neutral rules working from operand slots alone.
    if !ops.is_empty()
        && matches!(ops[0].op_type, ArmOperandType::Reg(_))
        && ops[0]
            .access
            .map_or(false, |acc| acc.is_readable() && acc.is_writable())
    {
        facts.inplace_dests.push((body_addr,));
    }

    if let Some((is_load, mmode, sp_implicit)) = multi {
        expand_multi_transfer(
            cs,
            mode,
            body_addr,
            &stem,
            &ops,
            is_load,
            mmode,
            sp_implicit,
            writeback,
            facts,
        );
    } else {
        // SP movement: explicit SUB/ADD SP, plus pre/post-index writeback on an SP-based access, which is how ARM32 spells a single-slot push or pop.
        if let Some(delta) = sp_adjustment(cs, &stem, &ops) {
            facts.adjusts_stack.push((body_addr, "SP", delta));
        } else if writeback {
            if let Some(delta) = writeback_adjustment(cs, &ops) {
                facts.adjusts_stack.push((body_addr, "SP", delta));
            }
        }
        // Frame-pointer establish/teardown matched by SHAPE (<frame reg> := <frame reg> + <imm>), as on AArch64, since the offset is load-bearing.
        frame_pointer_move(cs, mode, body_addr, &stem, &ops, facts);
    }

    // A PC write with no branch mnemonic is a control transfer the mach layer must still see; the decoder is the only place that knows which kind.
    if writes_pc && !matches!(stem.as_str(), "BL" | "BLX") {
        facts
            .pc_transfers
            .push((body_addr, pc_source == PcSource::SavedReturnAddress));
    }

    // BL and BLX write the link register; the call-return-address model depends on it and capstone reports it only through regs_write.
    if matches!(stem.as_str(), "BL" | "BLX") {
        facts.reg_defs.push((body_addr, Mreg::a32(A32Mreg::LR)));
    }
    if matches!(stem.as_str(), "BX" | "BXJ") && pc_source == PcSource::SavedReturnAddress {
        facts.reg_uses.push((body_addr, Mreg::a32(A32Mreg::LR)));
    }

    facts.emitted.push(Emitted {
        address: body_addr,
        size: body_size,
        mnemonic,
        op_str,
        pc_source,
        op_ids,
    });
}

/// The exact shape a select can reverse: `MOV<cc> Rd, Rm` writes one register a value that already sits in another, with no memory effect. Anything else predicated needs the branch back.
fn is_select_shaped(cs: &Capstone, stem: &str, ops: &[ArmOperand]) -> bool {
    if stem != "MOV" || ops.len() != 2 {
        return false;
    }
    let (Some(d), Some(s)) = (reg_of(cs, &ops[0]), reg_of(cs, &ops[1])) else {
        return false;
    };
    d.is_gp() && s.is_gp() && d != A32Mreg::PC && s != A32Mreg::PC
}

/// Explicit stack-pointer arithmetic: `SUB/ADD SP, SP, #imm`, and the two-operand `SUB/ADD SP, #imm` that Thumb's 16-bit encoding spells it with.
fn sp_adjustment(cs: &Capstone, stem: &str, ops: &[ArmOperand]) -> Option<i64> {
    if !matches!(stem, "SUB" | "ADD") || ops.len() < 2 {
        return None;
    }
    if reg_of(cs, &ops[0])? != A32Mreg::SP {
        return None;
    }
    let imm = match (&ops[1].op_type, ops.get(2).map(|o| &o.op_type)) {
        (ArmOperandType::Imm(v), None) => *v,
        (ArmOperandType::Reg(_), Some(ArmOperandType::Imm(v)))
            if reg_of(cs, &ops[1]) == Some(A32Mreg::SP) =>
        {
            *v
        }
        _ => return None,
    };
    Some(if stem == "SUB" {
        -(imm as i64)
    } else {
        imm as i64
    })
}

/// SP movement from pre/post-index writeback on an SP-based single access, e.g. `STR LR, [SP, #-4]!` and `LDR PC, [SP], #4`.
fn writeback_adjustment(cs: &Capstone, ops: &[ArmOperand]) -> Option<i64> {
    let mem_pos = ops
        .iter()
        .position(|o| matches!(o.op_type, ArmOperandType::Mem(_)))?;
    let ArmOperandType::Mem(mem) = &ops[mem_pos].op_type else {
        return None;
    };
    if reg_or_none(cs, mem.base()) != "SP" {
        return None;
    }
    // Post-index carries its delta in a trailing immediate operand; pre-index carries it in the memory operand's displacement.
    match ops.get(mem_pos + 1).map(|o| &o.op_type) {
        Some(ArmOperandType::Imm(v)) => Some(*v as i64),
        _ => Some(mem.disp() as i64),
    }
}

/// `MOV Rfp, SP` / `ADD Rfp, SP, #n` establishes the frame pointer, and the reverse tears it down; the frame register is R11 in ARM state and R7 in Thumb state.
fn frame_pointer_move(
    cs: &Capstone,
    mode: IsaMode,
    addr: u64,
    stem: &str,
    ops: &[ArmOperand],
    facts: &mut Facts,
) {
    if !matches!(stem, "MOV" | "ADD" | "SUB") || ops.len() < 2 {
        return;
    }
    let (Some(dst), Some(src)) = (reg_of(cs, &ops[0]), reg_of(cs, &ops[1])) else {
        return;
    };
    let frame_reg = |r: A32Mreg| r == A32Mreg::SP || r.name() == mode.frame_reg();
    if !frame_reg(dst) || !frame_reg(src) || dst == src {
        return;
    }
    let offset = match ops.get(2).map(|o| &o.op_type) {
        None => 0,
        Some(ArmOperandType::Imm(v)) => {
            if stem == "SUB" {
                -(*v as i64)
            } else {
                *v as i64
            }
        }
        // A register or shifted third operand is real arithmetic, not a frame establish.
        Some(_) => return,
    };
    facts
        .stack_base_move_offsets
        .push((addr, src.name(), dst.name(), offset));
    // The offsetless relation means exactly dst := src, which every consumer relies on, so it is emitted only for the genuinely zero-offset case.
    if offset == 0 {
        facts.stack_base_moves.push((addr, src.name(), dst.name()));
    }
}

/// Expand an LDM/STM (or its PUSH/POP alias) into one transfer per register at its own slot, so the stack pass sees ordinary slot loads and stores.
#[allow(clippy::too_many_arguments)]
// True when a memory access measures its offset against an SP that the same instruction writes back: PUSH/POP, the STMDB SP! / LDMIA SP! forms they encode as, and the single-register `STR Rt, [SP, #-4]!` push. Such an offset names a different frame origin than every other reference in the body -- `push {r7,lr}` puts the saved r7 eight bytes below the entry SP, while the `add r7,sp,#0` two instructions later calls the settled SP offset zero -- so lowering it to Ainstack yields a slot no stack_var ever covers, which reaches the C backend as a dereference of a bare integer. These are also exactly the callee-save spills and the return-address slot CompCert's Stacking emits, and reversing Stacking removes them: x86's asm_pass makes the same call, giving PUSH/POP a stack_delta and no memory operand. The stack adjustment carries the whole frame effect.
fn is_frame_setup(base: &str, writeback: bool) -> bool {
    writeback && A32Mreg::from(base) == A32Mreg::SP
}

fn expand_multi_transfer(
    cs: &Capstone,
    isa: IsaMode,
    addr: u64,
    stem: &str,
    ops: &[ArmOperand],
    is_load: bool,
    mode: MultiMode,
    sp_implicit: bool,
    writeback: bool,
    facts: &mut Facts,
) {
    // PUSH/POP have no base operand: the base is SP and writeback is implied. LDM/STM put the base in operand 0.
    let (base, list): (A32Mreg, &[ArmOperand]) = if sp_implicit {
        (A32Mreg::SP, ops)
    } else {
        match ops.split_first() {
            Some((b, rest)) => match reg_of(cs, b) {
                Some(r) => (r, rest),
                None => return,
            },
            None => return,
        }
    };
    let regs: Vec<A32Mreg> = list.iter().filter_map(|o| reg_of(cs, o)).collect();
    if regs.is_empty() {
        return;
    }
    // A VFP double-precision list moves 8 bytes per register; every other list moves 4.
    let width: i64 = if regs.iter().all(|r| r.is_double()) {
        8
    } else {
        4
    };
    let count = regs.len() as i64;
    let first = mode.first_offset(count, width);
    let base_name = base.name();
    let frame_setup = is_frame_setup(base_name, writeback || sp_implicit);
    if frame_setup {
        facts.frame_setups.push((addr,));
    }
    if !is_load {
        facts.memory_writes.push((addr, (count * width) as usize));
    }

    for (seq, reg) in regs.iter().enumerate() {
        let offset = first + seq as i64 * width;
        facts
            .multi_transfers
            .push((addr, is_load, reg.name(), base_name, offset, seq));
        if frame_setup {
            continue;
        }
        if base == A32Mreg::SP || base_name == isa.frame_reg() {
            if is_load {
                facts.stack_uses.push((addr, base_name, offset));
            } else {
                facts.stack_defs.push((addr, base_name, offset));
            }
        }
    }

    facts.reg_uses.push((addr, Mreg::a32(base)));
    if writeback || sp_implicit {
        facts.reg_defs.push((addr, Mreg::a32(base)));
        let delta = mode.writeback_delta(count, width);
        if base == A32Mreg::SP {
            facts.adjusts_stack.push((addr, "SP", delta));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vfp_store_width_follows_the_transferred_register_view() {
        assert_eq!(access_size("VSTR", Some(A32Mreg::S0)), 4);
        assert_eq!(access_size("VSTR", Some(A32Mreg::D0)), 8);
        assert_eq!(access_size("STRD", Some(A32Mreg::R0)), 8);
        assert_eq!(access_size("STREXB", Some(A32Mreg::R0)), 1);
        assert_eq!(access_size("SWPB", Some(A32Mreg::R0)), 1);
    }

    fn decoded_store_width(bytes: &[u8]) -> usize {
        let cs = Capstone::new()
            .arm()
            .mode(arch::arm::ArchMode::Arm)
            .detail(true)
            .build()
            .unwrap();
        let insns = cs.disasm_all(bytes, 0).unwrap();
        let insn = insns.iter().next().unwrap();
        let detail = cs.insn_detail(insn).unwrap();
        let arch_detail = detail.arch_detail();
        let arm = arch_detail.arm().unwrap();
        let raw = insn.mnemonic().unwrap().to_ascii_uppercase();
        let stem = opcode_stem(&raw, cc_name(arm.cc()));
        let ops: Vec<_> = arm.operands().collect();
        fixed_memory_write_bytes(
            &cs,
            &stem,
            &ops,
            arm.vector_size(),
            insn.op_str().unwrap_or(""),
        )
        .unwrap()
    }

    #[test]
    fn neon_structure_store_width_uses_registers_and_lanes() {
        assert_eq!(decoded_store_width(&[0x0f, 0x07, 0x00, 0xf4]), 8);
        assert_eq!(decoded_store_width(&[0x0f, 0x0a, 0x00, 0xf4]), 16);
        assert_eq!(decoded_store_width(&[0x2f, 0x00, 0x80, 0xf4]), 1);
        assert_eq!(decoded_store_width(&[0x4f, 0x05, 0x80, 0xf4]), 4);
    }

    #[test]
    fn opcode_stem_strips_only_the_condition_capstone_reported() {
        assert_eq!(opcode_stem("ADDGT", Some("GT")), "ADD");
        assert_eq!(opcode_stem("EORSNE", Some("NE")), "EORS");
        // MOVS and MULS end in condition-code letters but are unconditional.
        assert_eq!(opcode_stem("MOVS", None), "MOVS");
        assert_eq!(opcode_stem("MULS", None), "MULS");
        assert_eq!(opcode_stem("BLS", Some("LS")), "B");
        assert_eq!(opcode_stem("BL", None), "BL");
        // The VFP data-type suffix is rejoined with '_' so '.' stays free for the condition.
        assert_eq!(opcode_stem("VADDNE.F32", Some("NE")), "VADD_F32");
        assert_eq!(opcode_stem("VADD.F32", None), "VADD_F32");
    }

    // Thumb-2's .W/.N tail names the ENCODING width, not the operation. Left in, `B.W` reads as a conditional branch to the CFG and `LDR.W` as an opcode with no rule.
    #[test]
    fn opcode_stem_drops_the_thumb2_width_qualifier() {
        assert_eq!(opcode_stem("B.W", None), "B");
        assert_eq!(opcode_stem("B.N", None), "B");
        assert_eq!(opcode_stem("BNE.W", Some("NE")), "B");
        assert_eq!(opcode_stem("LDR.W", None), "LDR");
        assert_eq!(opcode_stem("MOVNE.W", Some("NE")), "MOV");
        assert_eq!(opcode_stem("ADDLO.W", Some("LO")), "ADD");
    }

    // The IT header itself computes nothing; every other mnemonic must decode as an operation.
    #[test]
    fn it_headers_are_recognized_and_nothing_else_is() {
        for m in [
            "IT", "ITT", "ITE", "ITTT", "ITTE", "ITET", "ITEE", "ITTTT", "ITEEE",
        ] {
            assert!(is_it_block(m), "{m}");
        }
        for m in ["ITEEEE", "ADD", "B", "LDR", "MOV", "TBB", "TST", "STR"] {
            assert!(!is_it_block(m), "{m}");
        }
    }

    // The PC reads two 4-byte instructions ahead in A32 and one word ahead, word-ALIGNED, in Thumb. Getting the Thumb rounding wrong moves every literal-pool reference made from an odd halfword by two bytes.
    #[test]
    fn the_pc_read_base_differs_between_the_instruction_sets() {
        assert_eq!(IsaMode::Arm.pc_base(0x1000), 0x1008);
        assert_eq!(IsaMode::Arm.pc_base(0x1004), 0x100c);
        assert_eq!(IsaMode::Thumb.pc_base(0x1000), 0x1004);
        // An instruction at an odd halfword rounds DOWN to the containing word.
        assert_eq!(IsaMode::Thumb.pc_base(0x1002), 0x1004);
        assert_eq!(IsaMode::Thumb.pc_base(0x1006), 0x1008);
        assert_eq!(IsaMode::Arm.alignment(), 4);
        assert_eq!(IsaMode::Thumb.alignment(), 2);
        assert_eq!(IsaMode::Arm.toggled(), IsaMode::Thumb);
        assert_eq!(IsaMode::Thumb.toggled(), IsaMode::Arm);
    }

    // A byte with no evidence of its own takes the default; a tagged run is reported as one segment, not one per byte.
    #[test]
    fn mode_runs_merge_and_fall_back_to_the_default() {
        let mut tags = vec![0u8; 16];
        for t in &mut tags[4..12] {
            *t = IsaMode::Thumb.tag();
        }
        let map = ModeMap {
            default: IsaMode::Arm,
            sections: vec![(0x1000, tags)],
        };
        assert_eq!(
            map.runs(0x1000, 0x1010),
            vec![
                (0x1000, 0x1004, IsaMode::Arm),
                (0x1004, 0x100c, IsaMode::Thumb),
                (0x100c, 0x1010, IsaMode::Arm),
            ]
        );
        // Outside any tracked section every byte is the default.
        assert_eq!(
            map.runs(0x2000, 0x2008),
            vec![(0x2000, 0x2008, IsaMode::Arm)]
        );
        assert_eq!(map.mode_at(0x1005), IsaMode::Thumb);
        assert_eq!(map.mode_at(0x1000), IsaMode::Arm);
    }

    // Every condition capstone can report must have an inverse, or the guard for a predicated instruction cannot be built and its effect is lost.
    #[test]
    fn every_condition_has_an_inverse() {
        for cc in branch::ARM_CONDITION_CODES {
            let inv = invert_cc(cc).unwrap_or_else(|| panic!("{cc} has no inverse"));
            assert_ne!(inv, cc);
            assert!(
                branch::is_arm_condition(inv),
                "{inv} must itself be a condition"
            );
            // HS/CS and LO/CC are one pair under two spellings, so the round trip lands on a synonym rather than the original spelling; inverting twice more must be stable.
            let back = invert_cc(inv).unwrap();
            assert_eq!(invert_cc(back).unwrap(), inv, "{cc} -> {inv} -> {back}");
        }
    }

    // A condition capstone reports but the frontend cannot invert must not silently become an unconditional instruction.
    #[test]
    fn cc_name_covers_exactly_the_invertible_conditions() {
        for cc in branch::ARM_CONDITION_CODES {
            assert!(invert_cc(cc).is_some(), "{cc}");
        }
    }

    // The lowest-numbered register always takes the lowest address, in every addressing mode.
    #[test]
    fn multi_transfer_offsets_match_the_addressing_mode() {
        // PUSH {r4,r5,fp,lr} = STMDB SP!: four words below the old SP.
        assert_eq!(MultiMode::Db.first_offset(4, 4), -16);
        assert_eq!(MultiMode::Db.writeback_delta(4, 4), -16);
        // POP {r4,r5,fp,pc} = LDMIA SP!: four words at and above the old SP.
        assert_eq!(MultiMode::Ia.first_offset(4, 4), 0);
        assert_eq!(MultiMode::Ia.writeback_delta(4, 4), 16);
        assert_eq!(MultiMode::Ib.first_offset(4, 4), 4);
        assert_eq!(MultiMode::Da.first_offset(4, 4), -12);
        assert_eq!(MultiMode::Da.writeback_delta(4, 4), -16);
    }

    #[test]
    fn push_and_pop_are_ldm_stm_aliases() {
        assert_eq!(
            multi_transfer_kind("PUSH"),
            Some((false, MultiMode::Db, true))
        );
        assert_eq!(
            multi_transfer_kind("POP"),
            Some((true, MultiMode::Ia, true))
        );
        assert_eq!(
            multi_transfer_kind("STMFD"),
            Some((false, MultiMode::Db, false))
        );
        assert_eq!(
            multi_transfer_kind("LDMFD"),
            Some((true, MultiMode::Ia, false))
        );
        assert_eq!(multi_transfer_kind("ADD"), None);
    }

    #[test]
    fn pool_complement_skips_exactly_the_pool_words() {
        let mut pools = BTreeMap::new();
        pools.insert(0x1020u64, 0x1024u64);
        pools.insert(0x1034u64, 0x1038u64);
        assert_eq!(
            complement(0x1000, 0x1040, &pools),
            vec![(0x1000, 0x1020), (0x1024, 0x1034), (0x1038, 0x1040)]
        );
        // A pool at the very end leaves no trailing segment.
        let mut tail = BTreeMap::new();
        tail.insert(0x1038u64, 0x1040u64);
        assert_eq!(complement(0x1000, 0x1040, &tail), vec![(0x1000, 0x1038)]);
        assert_eq!(
            complement(0x1000, 0x1040, &BTreeMap::new()),
            vec![(0x1000, 0x1040)]
        );
    }
}
