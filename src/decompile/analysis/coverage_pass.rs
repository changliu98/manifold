//! Instruction-coverage audit: the completeness dual of the adequacy audit.
//!
//! The adequacy audit asks what the candidate sets CANNOT express. This one
//! asks the opposite question: of every machine instruction the disassembler
//! decoded inside a recovered function, whose effect actually reached the
//! selected output? An instruction whose effect vanished silently -- no rule
//! matched it, its store produced no relation, its branch was deleted -- leaves
//! no trace anywhere, and nothing else in the pipeline reports absence.
//!
//! PC preservation is what makes the audit possible: node ids ARE instruction
//! addresses (plus the two synth bits), and every IR level keys its statements
//! by those node ids. So "did this instruction survive" is a lookup at one key
//! across a dozen relations, and the LAST level at which the key still had an
//! artifact is the vanish point.
//!
//! Every instruction lands in exactly one of three buckets:
//!
//!   * REPRESENTED -- a non-trivial statement at its node (or at one of its two
//!     synth sub-nodes) survives into the selected tree of a function that is
//!     actually printed. Tree assembly folds a node's statement into a parent
//!     and drops the key, so a node whose key is gone but whose statement is
//!     present as a subtree still counts. Assembly also rewrites an absorbed
//!     branch's goto ARMS (inlining bodies, break/continue forms) while never
//!     rewriting its comparison, so a branch candidate whose exact condition
//!     still guards a selected Sifthenelse counts as well.
//!   * JUSTIFIED-ABSENT -- absent for a named, checkable reason, each counted on
//!     its own: nop/padding, frame bookkeeping, a compare folded into a branch
//!     that KEPT the comparison, a copy the SSA renaming absorbed (checked --
//!     the web is referenced), canary code, a trimmed idiom, a jump-table
//!     implementation, a production-recorded RTL dead store or eliminated
//!     copy, a recorded Clight dead-variable store, a PLT thunk, a deliberately
//!     skipped library function.
//!   * UNACCOUNTED -- everything else. These are the defect candidates, and when
//!     a classification is uncertain the instruction lands here: the queue must
//!     over-approximate defects, never under-report them.
//!
//! The RTL optimizer publishes its actual production dead-store and
//! copy-elimination decisions. They justify only a node whose deepest artifact
//! is the pre-optimization RTL candidate; an unrelated surviving sub-node or a
//! later loss therefore remains UNACCOUNTED.
//!
//! Diagnostic only. It reads; it writes no relation any other pass sees.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::abi::StackGuardSlot;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::{
    CBlockItem, CExpr, CStmt, ForInit, Initializer, TopLevelDecl, TranslationUnit, VarDecl,
};
use crate::decompile::passes::clight_select::select::SelectedFunction;
use crate::decompile::passes::pass::IRPass;
use crate::util::{
    is_synthetic_node, MULTI_SYNTH_NODE_BIT, MULTI_SYNTH_STAGE_SHIFT, SYNTH_NODE_BIT,
    SYNTH_NODE_BIT2,
};
use crate::x86::types::{
    Address, ClightBinaryOp, ClightExpr, ClightFloatSize, ClightIntSize, ClightStmt, ClightType,
    Ident, Node, RTLInst, Symbol,
};

/// The raw decode tuple: (addr, size, prefix, mnemonic, op1..op4, 0, 0).
/// Position 2 is the PREFIX and position 3 the MNEMONIC.
type InsnTuple = (
    Address,
    usize,
    &'static str,
    &'static str,
    Symbol,
    Symbol,
    Symbol,
    Symbol,
    usize,
    usize,
);

/// The deepest IR level at which a node still had an artifact. Ordered: a
/// larger value is a later death, and `Selected` means it never died.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Layer {
    /// Decoded, but no Mach instruction: no lifting rule matched the mnemonic.
    AsmOnly,
    Mach,
    Linear,
    Ltl,
    /// RTL as the RTL pass produced it, before the optimizer ran.
    RtlCandidate,
    /// RTL after the optimizer. A node present at `RtlCandidate` and missing
    /// here may have an exact `dead_store` or `copy_eliminated` explanation;
    /// otherwise its removal remains unaccounted.
    Rtl,
    Cminor,
    /// Csharpminor as cshminor_pass produced it, before structuring.
    CshminorCandidate,
    /// Csharpminor after structuring rewrote it.
    Cshminor,
    /// A Clight candidate existed, but never reached the per-function export.
    ClightCandidate,
    /// A non-trivial candidate statement reached selection.
    Clight,
    /// The selected tree of a printed function carries the statement.
    Selected,
}

impl Layer {
    pub fn label(self) -> &'static str {
        match self {
            Layer::AsmOnly => "asm-only",
            Layer::Mach => "mach",
            Layer::Linear => "linear",
            Layer::Ltl => "ltl",
            Layer::RtlCandidate => "rtl-pre-opt",
            Layer::Rtl => "rtl",
            Layer::Cminor => "cminor",
            Layer::CshminorCandidate => "cshminor-pre-struct",
            Layer::Cshminor => "cshminor",
            Layer::ClightCandidate => "clight-cand",
            Layer::Clight => "clight",
            Layer::Selected => "selected",
        }
    }
}

/// A named, checkable reason an instruction has no statement of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Justification {
    /// The owning function is a PLT/GOT thunk or an external stub.
    PltThunk,
    /// The owning function is on the skip list (CRT/gnulib) or is section-local,
    /// so it is never printed by design.
    SkippedFunction,
    /// The canary/VLA idiom recognizer deliberately elided this instruction.
    TrimmedIdiom,
    /// Stack-protector bookkeeping: the canary load, its compare, or the fail tail.
    StackCanary,
    /// Jump-table implementation scaffolding the Csharpminor pass replaced with
    /// a single `Sswitch`.
    JumpTableImpl,
    /// An RTL Iop/Iload definition production DSE proved dead and replaced
    /// with Inop.
    DeadStore,
    /// An RTL Omove production copy propagation substituted at every use and
    /// replaced with Inop.
    CopyEliminated,
    /// The Clight pass recorded this store as writing a dead variable from a
    /// pure right-hand side.
    DeadVarStore,
    /// A nop, padding, or a CET landing pad: semantically nothing to represent.
    NopPadding,
    /// Prologue/epilogue frame bookkeeping on the stack/frame/callee-saved registers.
    FrameSetup,
    /// A flag-setting compare folded into a consuming branch that kept a real
    /// comparison in its selected condition.
    CompareFolded,
    /// A register-to-register copy absorbed by SSA renaming: checked, not
    /// assumed -- the value web this instruction defines is referenced by a
    /// selected statement.
    CopyAbsorbed,
    /// A `ret` whose function returns through a different node's `Sreturn`.
    ReturnFolded,
    /// A conditional jump fused into the flag-setting instruction it reads:
    /// the branch's condition is in that instruction's selected statement.
    BranchFolded,
    /// A value the RTL optimizer recorded as inlined at its use: a web it
    /// proved constant (`single_def_const`) or a single-use temp it folded
    /// (`emit_inline_temp`). The materializing instruction has no statement of
    /// its own because its value is spelled where it is read.
    ValueInlined,
}

impl Justification {
    pub fn label(self) -> &'static str {
        match self {
            Justification::PltThunk => "plt-thunk",
            Justification::SkippedFunction => "skipped-function",
            Justification::TrimmedIdiom => "trimmed-idiom",
            Justification::StackCanary => "stack-canary",
            Justification::JumpTableImpl => "jump-table-impl",
            Justification::DeadStore => "dead-store",
            Justification::CopyEliminated => "copy-eliminated",
            Justification::DeadVarStore => "dead-var-store",
            Justification::NopPadding => "nop-padding",
            Justification::FrameSetup => "frame-setup",
            Justification::CompareFolded => "compare-folded",
            Justification::CopyAbsorbed => "copy-absorbed",
            Justification::ReturnFolded => "return-folded",
            Justification::BranchFolded => "branch-folded",
            Justification::ValueInlined => "value-inlined",
        }
    }

    pub fn all() -> [Justification; 15] {
        [
            Justification::PltThunk,
            Justification::SkippedFunction,
            Justification::TrimmedIdiom,
            Justification::StackCanary,
            Justification::JumpTableImpl,
            Justification::DeadStore,
            Justification::CopyEliminated,
            Justification::DeadVarStore,
            Justification::NopPadding,
            Justification::FrameSetup,
            Justification::CompareFolded,
            Justification::CopyAbsorbed,
            Justification::ReturnFolded,
            Justification::BranchFolded,
            Justification::ValueInlined,
        ]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Represented,
    Justified(Justification),
    Unaccounted,
}

/// One audited instruction.
#[derive(Debug, Clone)]
pub struct InsnVerdict {
    pub node: Node,
    pub func: Address,
    pub func_name: String,
    pub mnemonic: &'static str,
    pub shape: String,
    pub vanish: Layer,
    pub verdict: Verdict,
    /// The node had an RTL instruction, but only `Inop`: the lifting kept the
    /// control-flow edge and dropped the effect.
    pub rtl_inop_only: bool,
    /// No function owning this node was printed.
    pub func_unprinted: bool,
    /// Explicit source-level bytes this decoded instruction writes to memory.
    pub required_write_bytes: usize,
    /// Bytes represented by selected Clight assignments in the node family,
    /// capped at the decoded requirement.
    pub represented_write_bytes: usize,
    /// Raw selected width before matching it against the decoded obligation.
    pub selected_write_bytes: usize,
    /// Architectural memory write with no sound fixed byte width.
    pub unknown_write_reason: Option<&'static str>,
}

// Operand and mnemonic shape

/// One decoded memory operand. The segment override is kept because it is what
/// separates the stack-protector slot from an ordinary access.
#[derive(Debug, Clone, Copy)]
struct MemOperand {
    seg: &'static str,
    base: &'static str,
    index: &'static str,
    disp: i64,
    size: usize,
}

/// The stack-protector slot, as the target ABI places it: `%fs:0x28` on x86-64,
/// `%gs:0x14` on i386, and nothing at all on AArch64/ARM, which reach their
/// cookie through the thread pointer with no fixed displacement to match.
/// Deliberately narrow -- any other segment-relative access is thread-local
/// program data whose loss is a real defect, not bookkeeping.
fn is_canary_slot(slot: Option<StackGuardSlot>, m: &MemOperand) -> bool {
    slot.is_some_and(|s| m.seg == s.segment && m.disp == s.offset)
}

enum BaseClass {
    None,
    Sp,
    Bp,
    Ip,
    Gen,
}

fn base_class_of(base: &str) -> BaseClass {
    match base {
        "NONE" => BaseClass::None,
        "RSP" | "ESP" | "SP" => BaseClass::Sp,
        "RBP" | "EBP" | "BP" => BaseClass::Bp,
        "RIP" | "EIP" => BaseClass::Ip,
        _ => BaseClass::Gen,
    }
}

/// Register file, not width: the family key must not split `%eax` from `%rax`.
fn reg_class(name: &str) -> &'static str {
    if name.starts_with("XMM") || name.starts_with("YMM") || name.starts_with("ZMM") {
        "vec"
    } else if name.starts_with("ST") || name.starts_with("MM") {
        "x87"
    } else if matches!(name, "CS" | "DS" | "ES" | "FS" | "GS" | "SS") {
        "seg"
    } else {
        "gpr"
    }
}

/// Operand kind, coarse enough to group families and fine enough that the
/// memory shape distinguishing an SSE high-lane store from a scalar one
/// survives: the access width and the base-register class are both in the key.
fn operand_shape(
    id: Symbol,
    regs: &HashMap<Symbol, &'static str>,
    imms: &HashSet<Symbol>,
    mems: &HashMap<Symbol, MemOperand>,
) -> Option<String> {
    if id == "0" {
        return None;
    }
    if let Some(name) = regs.get(id) {
        return Some(format!("r:{}", reg_class(name)));
    }
    if imms.contains(id) {
        return Some("imm".to_string());
    }
    if let Some(m) = mems.get(id) {
        let (base, index, size) = (m.base, m.index, m.size);
        let base_class = match base_class_of(base) {
            BaseClass::None => "abs",
            BaseClass::Sp => "sp",
            BaseClass::Bp => "bp",
            BaseClass::Ip => "ip",
            BaseClass::Gen => "gen",
        };
        let idx = if index == "NONE" { "" } else { "+i" };
        return Some(format!("m{}[{}{}]", size, base_class, idx));
    }
    None
}

/// Instructions whose entire architectural effect is nothing a C program can
/// observe. `CLD`/`STD` are deliberately absent: they set the direction flag
/// that string instructions read.
fn is_nop_mnemonic(m: &str) -> bool {
    matches!(
        m,
        "NOP"
            | "NOPW"
            | "NOPL"
            | "NOPQ"
            | "FNOP"
            | "ENDBR64"
            | "ENDBR32"
            | "INT3"
            | "PAUSE"
            | "VZEROUPPER"
            | "VZEROALL"
            | "LFENCE"
            | "MFENCE"
            | "SFENCE"
            | "PREFETCH"
            | "PREFETCHT0"
            | "PREFETCHT1"
            | "PREFETCHT2"
            | "PREFETCHNTA"
            | "PREFETCHW"
    )
}

fn is_compare_mnemonic(m: &str) -> bool {
    matches!(
        m,
        "CMP"
            | "TEST"
            | "CMPB"
            | "CMPW"
            | "CMPL"
            | "CMPQ"
            | "UCOMISS"
            | "UCOMISD"
            | "COMISS"
            | "COMISD"
            | "VUCOMISS"
            | "VUCOMISD"
            | "VCOMISS"
            | "VCOMISD"
            | "PTEST"
            | "VPTEST"
            | "BT"
    )
}

/// A conditional control transfer: every `J<cc>` but the unconditional `JMP`,
/// plus the `SET<cc>` family. These are the instructions asm_pass fuses into
/// the flag-setting instruction they read, which then carries the condition.
fn is_conditional_branch(m: &str) -> bool {
    (m.starts_with('J') && m != "JMP" && m != "JMPQ") || m.starts_with("SET")
}

fn is_copy_mnemonic(m: &str) -> bool {
    matches!(
        m,
        "MOV"
            | "MOVQ"
            | "MOVD"
            | "MOVAPS"
            | "MOVAPD"
            | "MOVDQA"
            | "MOVDQU"
            | "MOVSS"
            | "MOVSD"
            | "MOVUPS"
            | "MOVUPD"
            | "VMOVAPS"
            | "VMOVAPD"
            | "VMOVDQA"
            | "VMOVDQU"
    )
}

fn is_frame_register(name: &str) -> bool {
    matches!(
        name,
        "RBP"
            | "EBP"
            | "RSP"
            | "ESP"
            | "RBX"
            | "EBX"
            | "R12"
            | "R13"
            | "R14"
            | "R15"
            | "R12D"
            | "R13D"
            | "R14D"
            | "R15D"
    )
}

// Statement shape

/// A statement that exists but says nothing is not representation. `Sskip`, a
/// label wrapping nothing, and an all-skip sequence are placeholders.
fn is_trivial_stmt(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sskip => true,
        ClightStmt::Slabel(_, inner) => is_trivial_stmt(inner),
        ClightStmt::Ssequence(items) => items.iter().all(is_trivial_stmt),
        _ => false,
    }
}

/// Does this statement carry a real comparison? A branch whose condition
/// collapsed to a constant did NOT keep the compare it consumed, so a compare
/// feeding it is lost, not folded.
fn stmt_has_comparison(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sifthenelse(cond, a, b) => {
            expr_has_comparison(cond) || stmt_has_comparison(a) || stmt_has_comparison(b)
        }
        ClightStmt::Sswitch(e, cases) => {
            expr_has_comparison(e) || cases.iter().any(|(_, c)| stmt_has_comparison(c))
        }
        ClightStmt::Sset(_, e) => expr_has_comparison(e),
        ClightStmt::Sassign(l, r) => expr_has_comparison(l) || expr_has_comparison(r),
        ClightStmt::Ssequence(items) => items.iter().any(stmt_has_comparison),
        ClightStmt::Slabel(_, inner) => stmt_has_comparison(inner),
        ClightStmt::Sloop(a, b) => stmt_has_comparison(a) || stmt_has_comparison(b),
        ClightStmt::Sreturn(Some(e)) => expr_has_comparison(e),
        ClightStmt::Scall(_, f, args) => {
            expr_has_comparison(f) || args.iter().any(expr_has_comparison)
        }
        _ => false,
    }
}

fn expr_has_comparison(e: &ClightExpr) -> bool {
    match e {
        ClightExpr::Ebinop(op, l, r, _) => {
            matches!(
                op,
                ClightBinaryOp::Oeq
                    | ClightBinaryOp::One
                    | ClightBinaryOp::Olt
                    | ClightBinaryOp::Ogt
                    | ClightBinaryOp::Ole
                    | ClightBinaryOp::Oge
            ) || expr_has_comparison(l)
                || expr_has_comparison(r)
        }
        ClightExpr::Ederef(i, _)
        | ClightExpr::Eaddrof(i, _)
        | ClightExpr::Eunop(_, i, _)
        | ClightExpr::Ecast(i, _)
        | ClightExpr::Efield(i, _, _) => expr_has_comparison(i),
        ClightExpr::Econdition(c, a, b, _) => {
            expr_has_comparison(c) || expr_has_comparison(a) || expr_has_comparison(b)
        }
        _ => false,
    }
}

fn stmt_returns(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sreturn(_) => true,
        ClightStmt::Slabel(_, inner) => stmt_returns(inner),
        ClightStmt::Ssequence(items) => items.iter().any(stmt_returns),
        ClightStmt::Sifthenelse(_, a, b) => stmt_returns(a) || stmt_returns(b),
        ClightStmt::Sloop(a, b) => stmt_returns(a) || stmt_returns(b),
        ClightStmt::Sswitch(_, cases) => cases.iter().any(|(_, c)| stmt_returns(c)),
        _ => false,
    }
}

/// Short label for a statement's outermost form, `None` for placeholders.
/// Shared with the MANIFOLD_DUMP_CFG diagnostic in the elevator.
pub fn stmt_kind_label(stmt: &ClightStmt) -> Option<&'static str> {
    let s = strip_labels(stmt);
    if is_trivial_stmt(s) {
        return None;
    }
    Some(match s {
        ClightStmt::Sifthenelse(..) => "ite",
        ClightStmt::Scall(..) => "call",
        ClightStmt::Sset(..) => "set",
        ClightStmt::Sassign(..) => "assign",
        ClightStmt::Sreturn(..) => "return",
        ClightStmt::Sgoto(..) => "goto",
        ClightStmt::Sswitch(..) => "switch",
        ClightStmt::Ssequence(..) => "seq",
        ClightStmt::Sloop(..) => "loop",
        _ => "other",
    })
}

/// Peel the `Slabel` wrappers a Clight candidate carries. Every candidate is
/// exported label-wrapped, and assembly drops the label when it inlines the
/// statement into a parent, so the two sides only compare equal unstripped.
fn strip_labels(stmt: &ClightStmt) -> &ClightStmt {
    match stmt {
        ClightStmt::Slabel(_, inner) => strip_labels(inner),
        _ => stmt,
    }
}

/// The same comparison spelled with the inverse operator: loop assembly may
/// flip branch polarity to spell an exact outside edge as `if (c) break`, so
/// `t >= 0 -> goto out` can survive as `t < 0 -> break`.
/// Operands must match exactly; only the top-level operator inverts.
fn inverse_condition(e: &ClightExpr) -> Option<ClightExpr> {
    let ClightExpr::Ebinop(op, l, r, ty) = e else {
        return None;
    };
    let inv = match op {
        ClightBinaryOp::Oeq => ClightBinaryOp::One,
        ClightBinaryOp::One => ClightBinaryOp::Oeq,
        ClightBinaryOp::Olt => ClightBinaryOp::Oge,
        ClightBinaryOp::Oge => ClightBinaryOp::Olt,
        ClightBinaryOp::Ole => ClightBinaryOp::Ogt,
        ClightBinaryOp::Ogt => ClightBinaryOp::Ole,
        _ => return None,
    };
    Some(ClightExpr::Ebinop(inv, l.clone(), r.clone(), ty.clone()))
}

/// Every statement in the tree rooted here, itself included. Tree assembly
/// nests a node's selected statement inside a parent and drops its key, so
/// subtree membership is how an absorbed statement is found again.
fn collect_subtrees<'a>(stmt: &'a ClightStmt, out: &mut HashSet<&'a ClightStmt>) {
    out.insert(stmt);
    match stmt {
        ClightStmt::Ssequence(items) => items.iter().for_each(|s| collect_subtrees(s, out)),
        ClightStmt::Slabel(_, inner) => collect_subtrees(inner, out),
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            collect_subtrees(a, out);
            collect_subtrees(b, out);
        }
        ClightStmt::Sswitch(_, cases) => cases.iter().for_each(|(_, c)| collect_subtrees(c, out)),
        _ => {}
    }
}

fn clight_type_byte_size(ty: &ClightType, pointer_size: usize) -> Option<usize> {
    match ty {
        ClightType::Tint(ClightIntSize::I8 | ClightIntSize::IBool, _, _) => Some(1),
        ClightType::Tint(ClightIntSize::I16, _, _) => Some(2),
        ClightType::Tint(ClightIntSize::I32, _, _) => Some(4),
        ClightType::Tlong(_, _) => Some(8),
        ClightType::Tint128(_, _) => Some(16),
        ClightType::Tfloat(ClightFloatSize::F32, _) => Some(4),
        ClightType::Tfloat(ClightFloatSize::F64, _) => Some(8),
        ClightType::Tpointer(_, _) => Some(pointer_size),
        ClightType::Tarray(inner, count, _) if *count >= 0 => {
            clight_type_byte_size(inner, pointer_size)
                .and_then(|size| size.checked_mul(*count as usize))
        }
        _ => None,
    }
}

/// Bytes written by one Clight candidate to storage that still represents a
/// decoded machine-memory obligation.
///
/// An ordinary `Sset` writes an SSA temporary and contributes nothing.  A
/// proven stack variable is different: reversing Stacking deliberately raises
/// a physical frame-cell store into an `Sset` of that cell's canonical local.
/// `stack_var_types` identifies exactly those destinations and supplies the
/// selected declaration width.  Keeping the identity explicit is important:
/// counting every typed `Sset` would let an unrelated register computation
/// satisfy a memory write at the same provenance node.
pub(crate) fn stmt_selected_write_bytes(
    stmt: &ClightStmt,
    pointer_size: usize,
    stack_var_types: &HashMap<Ident, ClightType>,
) -> usize {
    match strip_labels(stmt) {
        ClightStmt::Sassign(lhs, _) => {
            let ty = crate::decompile::passes::csh_pass::clight_expr_type(lhs);
            clight_type_byte_size(&ty, pointer_size).unwrap_or(0)
        }
        ClightStmt::Sset(dst, _) => stack_var_types
            .get(dst)
            .and_then(|ty| clight_type_byte_size(ty, pointer_size))
            .unwrap_or(0),
        ClightStmt::Ssequence(items) => items.iter().fold(0usize, |total, stmt| {
            total.saturating_add(stmt_selected_write_bytes(
                stmt,
                pointer_size,
                stack_var_types,
            ))
        }),
        ClightStmt::Sifthenelse(_, yes, no) => {
            stmt_selected_write_bytes(yes, pointer_size, stack_var_types)
                .max(stmt_selected_write_bytes(no, pointer_size, stack_var_types))
        }
        ClightStmt::Sloop(yes, no) => stmt_selected_write_bytes(yes, pointer_size, stack_var_types)
            .saturating_add(stmt_selected_write_bytes(no, pointer_size, stack_var_types)),
        ClightStmt::Sswitch(_, cases) => cases
            .iter()
            .map(|(_, stmt)| stmt_selected_write_bytes(stmt, pointer_size, stack_var_types))
            .max()
            .unwrap_or(0),
        _ => 0,
    }
}

/// Context-free spelling used by focused `Sassign` width tests.  Production
/// selection calls `stmt_selected_write_bytes` with its proven stack locals.
pub(crate) fn stmt_memory_write_bytes(stmt: &ClightStmt, pointer_size: usize) -> usize {
    stmt_selected_write_bytes(stmt, pointer_size, &HashMap::new())
}

/// A statement-level syntactic witness whose exact presence can be checked on
/// both sides of post-emission AST rewriting. This is deliberately labelled an
/// exact-persistence diagnostic, not semantic preservation: local renaming and
/// control-structure rewrites can change a witness without removing its effect.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum EmittedStmtWitness {
    Expr(CExpr),
    Initializer(String, Initializer),
    Return(Option<CExpr>),
    Goto(String),
    Break,
    Continue,
    Condition(CExpr),
}

type EmittedWitnessKey = (String, EmittedStmtWitness);
type EmittedWitnessMultiset = HashMap<EmittedWitnessKey, usize>;

/// Checkpoints that are materialized while the emitted C tree is still being
/// rewritten.  `GotoElide` is deliberately absent: coverage reads the final TU
/// after that last writer, so its output is the fourth and final checkpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PostEmitCheckpoint {
    ClightEmitFinalize,
    ForLoop,
    VarReduce,
}

impl PostEmitCheckpoint {
    fn index(self) -> usize {
        match self {
            Self::ClightEmitFinalize => 0,
            Self::ForLoop => 1,
            Self::VarReduce => 2,
        }
    }
}

pub(crate) const POST_EMIT_STAGE_LABELS: [&str; 4] = [
    "clight-emit-finalize",
    "forloop",
    "var-reduce",
    "goto-elide",
];

const STORED_POST_EMIT_CHECKPOINTS: usize = 3;

/// One baseline witness's multiplicity at the initial emitted tree and at
/// every materialized checkpoint.  Counts are capped at the baseline count:
/// exact persistence, like the old endpoint multiset intersection, treats an
/// identical extra occurrence as satisfying at most one baseline occurrence.
#[derive(Debug, Clone)]
struct EmittedWitnessTrace {
    counts: [usize; STORED_POST_EMIT_CHECKPOINTS + 1],
}

/// Compact stage-separated post-emit audit state.  This retains one set of
/// expression keys, not one TranslationUnit (or even one witness map) per
/// stage.  A checkpoint builds a temporary map, records capped multiplicities,
/// and drops it immediately.
#[derive(Debug, Clone)]
pub(crate) struct PostEmitAuditTrail {
    traces: HashMap<EmittedWitnessKey, EmittedWitnessTrace>,
    all_witness_totals: [usize; STORED_POST_EMIT_CHECKPOINTS + 1],
    recorded_checkpoints: usize,
    valid: bool,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PostEmitStageReport {
    pub stage: &'static str,
    /// All witnesses in the adjacent trees, including syntax introduced by an
    /// earlier transform.  These totals expose duplication/removal separately
    /// from baseline persistence.
    pub all_witnesses_before: usize,
    pub all_witnesses_after: usize,
    /// Baseline occurrences still exactly present on each side of this stage.
    pub baseline_exact_before: usize,
    pub baseline_exact_after: usize,
    /// Local loss/recovery of baseline syntax at this stage.
    pub newly_changed_or_removed: usize,
    pub recovered: usize,
    /// End-to-end missing baseline occurrences assigned to this stage after
    /// cancelling any later exact recovery.  These values plus `unattributed`
    /// form an exact decomposition of the endpoint deficit.
    pub endpoint_changed_or_removed: usize,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct PostEmitVisibility {
    witnesses: usize,
    final_witnesses: usize,
    exact_survived: usize,
    changed_or_removed: usize,
    unattributed_changed_or_removed: usize,
    stages: Vec<PostEmitStageReport>,
}

fn collect_decl_witnesses(decls: &[VarDecl], out: &mut Vec<EmittedStmtWitness>) {
    for decl in decls {
        let Some(init) = &decl.init else {
            continue;
        };
        match init {
            // var_reduce may move `x = rhs` from the body into x's declaration.
            // Normalize the initializer back to that effect so the move is
            // presence-preserving rather than reported as erosion.
            Initializer::Expr(expr) => out.push(EmittedStmtWitness::Expr(CExpr::assign(
                CExpr::var(decl.name.clone()),
                expr.clone(),
            ))),
            other => out.push(EmittedStmtWitness::Initializer(
                decl.name.clone(),
                other.clone(),
            )),
        }
    }
}

fn collect_emitted_witnesses(stmt: &CStmt, out: &mut Vec<EmittedStmtWitness>) {
    match stmt {
        CStmt::Empty => {}
        CStmt::Decl(decls) => collect_decl_witnesses(decls, out),
        CStmt::Expr(expr) => out.push(EmittedStmtWitness::Expr(expr.clone())),
        CStmt::Return(expr) => out.push(EmittedStmtWitness::Return(expr.clone())),
        CStmt::Goto(label) => out.push(EmittedStmtWitness::Goto(label.clone())),
        CStmt::Break => out.push(EmittedStmtWitness::Break),
        CStmt::Continue => out.push(EmittedStmtWitness::Continue),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(stmt) => collect_emitted_witnesses(stmt, out),
                    CBlockItem::Decl(decls) => collect_decl_witnesses(decls, out),
                }
            }
        }
        CStmt::If(cond, yes, no) => {
            out.push(EmittedStmtWitness::Condition(cond.clone()));
            collect_emitted_witnesses(yes, out);
            if let Some(no) = no {
                collect_emitted_witnesses(no, out);
            }
        }
        CStmt::Switch(cond, body) | CStmt::While(cond, body) => {
            out.push(EmittedStmtWitness::Condition(cond.clone()));
            collect_emitted_witnesses(body, out);
        }
        CStmt::DoWhile(body, cond) => {
            collect_emitted_witnesses(body, out);
            out.push(EmittedStmtWitness::Condition(cond.clone()));
        }
        CStmt::For(init, cond, step, body) => {
            match init {
                Some(ForInit::Expr(expr)) => {
                    out.push(EmittedStmtWitness::Expr(expr.clone()));
                }
                Some(ForInit::Decl(decls)) => collect_decl_witnesses(decls, out),
                None => {}
            }
            if let Some(cond) = cond {
                out.push(EmittedStmtWitness::Condition(cond.clone()));
            }
            if let Some(step) = step {
                out.push(EmittedStmtWitness::Expr(step.clone()));
            }
            collect_emitted_witnesses(body, out);
        }
        CStmt::Labeled(_, inner) => collect_emitted_witnesses(inner, out),
        CStmt::Sequence(items) => items
            .iter()
            .for_each(|stmt| collect_emitted_witnesses(stmt, out)),
    }
}

pub(crate) fn emitted_witness_multiset(tu: &TranslationUnit) -> EmittedWitnessMultiset {
    let mut out = HashMap::new();
    for decl in &tu.decls {
        let TopLevelDecl::FuncDef(func) = decl else {
            continue;
        };
        let mut witnesses = Vec::new();
        collect_decl_witnesses(&func.local_vars, &mut witnesses);
        collect_emitted_witnesses(&func.body, &mut witnesses);
        for witness in witnesses {
            *out.entry((func.name.clone(), witness)).or_insert(0) += 1;
        }
    }
    out
}

impl PostEmitAuditTrail {
    pub(crate) fn new(initial: &TranslationUnit) -> Self {
        let initial = emitted_witness_multiset(initial);
        let initial_total = initial.values().sum();
        let traces = initial
            .into_iter()
            .map(|(witness, count)| {
                let mut counts = [0; STORED_POST_EMIT_CHECKPOINTS + 1];
                counts[0] = count;
                (witness, EmittedWitnessTrace { counts })
            })
            .collect();
        let mut all_witness_totals = [0; STORED_POST_EMIT_CHECKPOINTS + 1];
        all_witness_totals[0] = initial_total;
        Self {
            traces,
            all_witness_totals,
            recorded_checkpoints: 0,
            valid: true,
        }
    }

    /// Record the next fixed checkpoint.  An out-of-order or duplicate call
    /// invalidates the diagnostic; coverage then reports no post-emit number
    /// instead of silently attaching churn to the wrong pass.
    pub(crate) fn record(
        &mut self,
        checkpoint: PostEmitCheckpoint,
        tu: &TranslationUnit,
    ) -> Result<(), &'static str> {
        if !self.valid || checkpoint.index() != self.recorded_checkpoints {
            self.valid = false;
            return Err("post-emit checkpoints were recorded out of order");
        }

        let witnesses = emitted_witness_multiset(tu);
        let slot = self.recorded_checkpoints + 1;
        for (witness, trace) in &mut self.traces {
            trace.counts[slot] = trace.counts[0].min(witnesses.get(witness).copied().unwrap_or(0));
        }
        self.all_witness_totals[slot] = witnesses.values().sum();
        self.recorded_checkpoints += 1;
        Ok(())
    }

    fn visibility(&self, final_tu: &TranslationUnit) -> Option<PostEmitVisibility> {
        if !self.valid || self.recorded_checkpoints != STORED_POST_EMIT_CHECKPOINTS {
            return None;
        }

        let final_witnesses = emitted_witness_multiset(final_tu);
        let final_total: usize = final_witnesses.values().sum();
        let mut stages: Vec<PostEmitStageReport> = POST_EMIT_STAGE_LABELS
            .iter()
            .map(|stage| PostEmitStageReport {
                stage,
                ..PostEmitStageReport::default()
            })
            .collect();
        let all_totals = [
            self.all_witness_totals[0],
            self.all_witness_totals[1],
            self.all_witness_totals[2],
            self.all_witness_totals[3],
            final_total,
        ];
        for (index, stage) in stages.iter_mut().enumerate() {
            stage.all_witnesses_before = all_totals[index];
            stage.all_witnesses_after = all_totals[index + 1];
        }

        let mut exact_survived = 0usize;
        for (witness, trace) in &self.traces {
            let final_count =
                trace.counts[0].min(final_witnesses.get(witness).copied().unwrap_or(0));
            let counts = [
                trace.counts[0],
                trace.counts[1],
                trace.counts[2],
                trace.counts[3],
                final_count,
            ];
            exact_survived = exact_survived.saturating_add(final_count);

            // Local churn is measured against baseline occurrences so a syntax
            // introduced by one pass cannot masquerade as selected persistence
            // in the next pass.
            for index in 0..stages.len() {
                let before = counts[index];
                let after = counts[index + 1];
                stages[index].baseline_exact_before =
                    stages[index].baseline_exact_before.saturating_add(before);
                stages[index].baseline_exact_after =
                    stages[index].baseline_exact_after.saturating_add(after);
                if after < before {
                    stages[index].newly_changed_or_removed = stages[index]
                        .newly_changed_or_removed
                        .saturating_add(before - after);
                } else {
                    stages[index].recovered =
                        stages[index].recovered.saturating_add(after - before);
                }
            }

            // Attribute only the endpoint deficit.  A later exact recovery
            // cancels the newest outstanding loss first, so stage attribution
            // is additive and never double-counts transient rewrite churn.
            let mut outstanding = [0usize; 4];
            let mut current = counts[0];
            for index in 0..stages.len() {
                let after = counts[index + 1];
                if after < current {
                    outstanding[index] = outstanding[index].saturating_add(current - after);
                } else if after > current {
                    let mut recovery = after - current;
                    for earlier in (0..=index).rev() {
                        let cancelled = recovery.min(outstanding[earlier]);
                        outstanding[earlier] -= cancelled;
                        recovery -= cancelled;
                        if recovery == 0 {
                            break;
                        }
                    }
                    debug_assert_eq!(recovery, 0);
                }
                current = after;
            }
            debug_assert_eq!(
                outstanding.iter().sum::<usize>(),
                counts[0].saturating_sub(final_count)
            );
            for (stage, count) in stages.iter_mut().zip(outstanding) {
                stage.endpoint_changed_or_removed =
                    stage.endpoint_changed_or_removed.saturating_add(count);
            }
        }

        let witnesses = self.all_witness_totals[0];
        let changed_or_removed = witnesses.saturating_sub(exact_survived);
        let attributed: usize = stages
            .iter()
            .map(|stage| stage.endpoint_changed_or_removed)
            .sum();
        Some(PostEmitVisibility {
            witnesses,
            final_witnesses: final_total,
            exact_survived,
            changed_or_removed,
            unattributed_changed_or_removed: changed_or_removed.saturating_sub(attributed),
            stages,
        })
    }
}

fn post_emit_visibility(db: &DecompileDB) -> PostEmitVisibility {
    let (Some(trail), Some(final_tu)) = (
        db.cast_post_emit_audit_trail.as_ref(),
        db.cast_optimized_translation_unit.as_ref(),
    ) else {
        return PostEmitVisibility::default();
    };
    trail.visibility(final_tu).unwrap_or_default()
}

/// Every variable identifier a statement mentions. An `Ident` is the same
/// numeric space as an `RTLReg`, so these are value-web references.
fn stmt_idents(stmt: &ClightStmt, out: &mut Vec<Ident>) {
    match stmt {
        ClightStmt::Sset(id, rhs) => {
            out.push(*id);
            expr_idents(rhs, out);
        }
        ClightStmt::Sassign(lhs, rhs) => {
            expr_idents(lhs, out);
            expr_idents(rhs, out);
        }
        ClightStmt::Sifthenelse(cond, a, b) => {
            expr_idents(cond, out);
            stmt_idents(a, out);
            stmt_idents(b, out);
        }
        ClightStmt::Ssequence(items) => items.iter().for_each(|i| stmt_idents(i, out)),
        ClightStmt::Slabel(_, inner) => stmt_idents(inner, out),
        ClightStmt::Sloop(a, b) => {
            stmt_idents(a, out);
            stmt_idents(b, out);
        }
        ClightStmt::Sreturn(Some(e)) => expr_idents(e, out),
        ClightStmt::Sswitch(e, cases) => {
            expr_idents(e, out);
            cases.iter().for_each(|(_, c)| stmt_idents(c, out));
        }
        ClightStmt::Scall(dst, f, args) => {
            if let Some(d) = dst {
                out.push(*d);
            }
            expr_idents(f, out);
            args.iter().for_each(|a| expr_idents(a, out));
        }
        ClightStmt::Sbuiltin(dst, _, _, args) => {
            if let Some(d) = dst {
                out.push(*d);
            }
            args.iter().for_each(|a| expr_idents(a, out));
        }
        _ => {}
    }
}

fn expr_idents(e: &ClightExpr, out: &mut Vec<Ident>) {
    match e {
        ClightExpr::Etempvar(id, _) | ClightExpr::Evar(id, _) => out.push(*id),
        ClightExpr::Ederef(i, _)
        | ClightExpr::Eaddrof(i, _)
        | ClightExpr::Eunop(_, i, _)
        | ClightExpr::Ecast(i, _)
        | ClightExpr::Efield(i, _, _) => expr_idents(i, out),
        ClightExpr::Ebinop(_, l, r, _) => {
            expr_idents(l, out);
            expr_idents(r, out);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            expr_idents(c, out);
            expr_idents(a, out);
            expr_idents(b, out);
        }
        _ => {}
    }
}

/// A value-web id packs the node that defined it above the machine-register
/// discriminant, so the defining node reads straight back out of the id.
fn web_def_node(reg: u64) -> Node {
    crate::decompile::passes::rtl_pass::simd_dword_reg_event(reg).unwrap_or_else(|| {
        (reg & !(1u64 << 63)) >> crate::decompile::passes::rtl_pass::MREG_DISCRIMINANT_BITS
    })
}

/// A node and its two synth sub-nodes: an RMW fused into one address emits its
/// op at synth1 and its store at synth2, so evidence at either is evidence for
/// the instruction.
fn node_family(base: Node) -> Vec<Node> {
    let mut family = Vec::with_capacity(11);
    family.push(base);
    family.extend(
        (1u64..=7).map(|stage| base | MULTI_SYNTH_NODE_BIT | (stage << MULTI_SYNTH_STAGE_SHIFT)),
    );
    family.extend([
        base | SYNTH_NODE_BIT,
        base | SYNTH_NODE_BIT2,
        base | SYNTH_NODE_BIT | SYNTH_NODE_BIT2,
    ]);
    family
}

// The report

#[derive(Debug, Default, Clone)]
pub struct CoverageReport {
    pub universe: usize,
    pub represented: usize,
    pub justified: BTreeMap<&'static str, usize>,
    pub unaccounted: usize,
    /// Vanish-point histogram over the whole universe.
    pub vanish: BTreeMap<&'static str, usize>,
    /// Vanish-point histogram over the UNACCOUNTED set only.
    pub unaccounted_vanish: BTreeMap<&'static str, usize>,
    /// Nodes whose RTL form is nothing but `Inop`.
    pub rtl_inop_only: usize,
    /// Unaccounted instructions in a function that was never printed at all.
    pub unaccounted_in_unprinted: usize,
    /// Explicit decoded memory-effect bytes, split by audit outcome. This is a
    /// second denominator: instruction presence cannot hide a partial store.
    pub write_bytes_required: usize,
    pub write_bytes_represented: usize,
    pub write_bytes_justified: usize,
    pub write_bytes_unaccounted: usize,
    pub partial_write_instructions: usize,
    /// Selected fixed-width assignments exceeding the decoded obligation.
    pub write_bytes_overrepresented: usize,
    pub over_write_instructions: usize,
    /// Dynamic/scalable/special write obligations are counted separately from
    /// the fixed-byte denominator and split by the instruction verdict.
    pub unknown_write_instructions: usize,
    pub unknown_write_represented: usize,
    pub unknown_write_justified: usize,
    pub unknown_write_unaccounted: usize,
    /// Exact syntactic witnesses before and after post-emit rewrites. A changed
    /// witness is optimizer churn, not by itself proof of semantic erosion.
    pub post_emit_witnesses: usize,
    pub post_emit_final_witnesses: usize,
    pub post_emit_exact_survived: usize,
    pub post_emit_changed_or_removed: usize,
    /// Endpoint losses assigned to the exact writer stage where their latest
    /// unrecovered disappearance occurred.  `unattributed` must remain zero;
    /// a nonzero value means the checkpoint chain is incomplete.
    pub post_emit_stages: Vec<PostEmitStageReport>,
    pub post_emit_unattributed_changed_or_removed: usize,
    pub verdicts: Vec<InsnVerdict>,
}

impl CoverageReport {
    pub fn justified_total(&self) -> usize {
        self.justified.values().sum()
    }

    /// Coverage is measured against what the pipeline is actually on the hook
    /// for: the universe minus the instructions whose absence has a reason.
    pub fn coverage_pct(&self) -> f64 {
        let denom = self.universe.saturating_sub(self.justified_total());
        if denom == 0 {
            return 100.0;
        }
        (self.represented as f64 / denom as f64) * 100.0
    }

    pub fn write_coverage_pct(&self) -> Option<f64> {
        let denom = self
            .write_bytes_required
            .saturating_sub(self.write_bytes_justified);
        if denom == 0 {
            return None;
        }
        Some((self.write_bytes_represented as f64 / denom as f64) * 100.0)
    }

    pub fn post_emit_exact_presence_pct(&self) -> Option<f64> {
        if self.post_emit_witnesses == 0 {
            return None;
        }
        Some((self.post_emit_exact_survived as f64 / self.post_emit_witnesses as f64) * 100.0)
    }
}

// Gathering

/// Everything the classifier needs, gathered once from the DB.
struct AuditInputs {
    /// Universe: real instruction nodes owned by some function.
    insns: BTreeMap<Node, InsnTuple>,
    node_funcs: BTreeMap<Node, BTreeSet<Address>>,
    func_names: HashMap<Address, String>,

    regs: HashMap<Symbol, &'static str>,
    imms: HashSet<Symbol>,
    mems: HashMap<Symbol, MemOperand>,
    /// Where this target keeps its stack-protector cookie, if it keeps one at a
    /// fixed segment offset at all.
    guard_slot: Option<StackGuardSlot>,

    mach: HashSet<Node>,
    linear: HashSet<Node>,
    ltl: HashSet<Node>,
    rtl_cand: HashSet<Node>,
    rtl_cand_inop: HashSet<Node>,
    rtl: HashSet<Node>,
    rtl_inop: HashSet<Node>,
    cminor: HashSet<Node>,
    csh_cand: HashSet<Node>,
    cshminor: HashSet<Node>,
    clight_cand: HashSet<Node>,
    clight: HashSet<Node>,
    selected: HashSet<Node>,
    required_write_bytes: HashMap<Node, usize>,
    selected_write_bytes: HashMap<Node, usize>,
    unknown_write_reason: HashMap<Node, &'static str>,

    /// Nodes whose selected statement carries a real comparison.
    selected_comparison: HashSet<Node>,
    /// Successor edges, unioned over the RTL/Clight/emit views.
    succ: HashMap<Node, Vec<Node>>,
    /// Value webs referenced anywhere in the selected output.
    live_webs: HashSet<u64>,
    /// Nodes that define one of those webs. Keyed by defining node so the
    /// per-instruction check is a lookup rather than a scan of every live web.
    live_def_nodes: HashSet<Node>,
    /// Per node, the (source, destination) webs of an RTL move. A node whose
    /// whole RTL form is a move is a rename, and nothing else.
    rtl_move: HashMap<Node, Vec<(u64, u64)>>,
    /// Nodes carrying an RTL candidate that is NOT a move.
    rtl_non_move: HashSet<Node>,
    /// Move edges keyed by destination web, so every candidate source chain can
    /// be walked to the value it ultimately names.  The relation is not
    /// functional: choosing one source by insertion order makes the audit
    /// nondeterministic and can falsely justify an alternative dead chain.
    move_src_of: HashMap<u64, Vec<u64>>,
    /// Physical instruction adjacency from the decoder.
    prev_by_addr: HashMap<Node, Vec<Node>>,
    /// Decoder flags analysis: compare/test address -> the Jcc addresses that
    /// consume its flags. When the Mcond is keyed at the Jcc (shadowed or
    /// secondary pairs), this is the checkable link from the bare compare to
    /// the branch that carries its comparison.
    flags_pair_of: HashMap<Node, Vec<Node>>,
    /// Webs the RTL optimizer published as inlined at their use: proved
    /// constant, or folded as a single-use temp. Its only recorded account of
    /// what it removed and why.
    inlined_webs: HashSet<u64>,
    /// Functions whose selected tree contains a return statement.
    funcs_with_return: HashSet<Address>,
    /// Function addresses actually printed into the emitted translation unit.
    printed_funcs: HashSet<Address>,

    plt_funcs: HashSet<Address>,
    external_funcs: HashSet<Address>,
    skipped_funcs: HashSet<Address>,
    trimmed: HashSet<Node>,
    jump_table_trim: HashSet<Node>,
    /// Exact nodes removed by the production RTL optimizer, retained across
    /// every copy-propagation/DSE fixpoint iteration.
    dead_store: HashSet<Node>,
    copy_eliminated: HashSet<Node>,
    dead_var_store: HashSet<Node>,
}

fn collect(db: &DecompileDB) -> AuditInputs {
    let mut node_funcs: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for (node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        // Synth nodes are artifacts of lifting, not decoded instructions; they
        // count as evidence for their base, never as universe members.
        if is_synthetic_node(*node) {
            continue;
        }
        node_funcs.entry(*node).or_default().insert(*func);
    }

    let mut insns: BTreeMap<Node, InsnTuple> = BTreeMap::new();
    for t in db.rel_iter::<InsnTuple>("unrefinedinstruction") {
        if node_funcs.contains_key(&t.0) {
            insns.insert(t.0, *t);
        }
    }
    node_funcs.retain(|n, _| insns.contains_key(n));

    let mut func_names: HashMap<Address, String> = HashMap::new();
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        func_names.entry(*addr).or_insert_with(|| name.to_string());
    }
    for (name, addr) in db.rel_iter::<(Symbol, Address)>("func_entry") {
        func_names.entry(*addr).or_insert_with(|| name.to_string());
    }

    let regs: HashMap<Symbol, &'static str> = db
        .rel_iter::<(Symbol, &'static str)>("op_register")
        .map(|(id, name)| (*id, *name))
        .collect();
    let imms: HashSet<Symbol> = db
        .rel_iter::<(Symbol, i64, usize)>("op_immediate")
        .map(|(id, _, _)| *id)
        .collect();
    let mems: HashMap<Symbol, MemOperand> = db
        .rel_iter::<(
            Symbol,
            &'static str,
            &'static str,
            &'static str,
            i64,
            i64,
            usize,
        )>("op_indirect")
        .map(|(id, seg, base, index, _scale, disp, size)| {
            (
                *id,
                MemOperand {
                    seg: *seg,
                    base: *base,
                    index: *index,
                    disp: *disp,
                    size: *size,
                },
            )
        })
        .collect();
    let mut required_write_bytes: HashMap<Node, usize> = HashMap::new();
    for (node, bytes) in db.rel_iter::<(Address, usize)>("decoded_memory_write_bytes") {
        if let Some(previous) = required_write_bytes.insert(*node, *bytes) {
            assert_eq!(
                previous, *bytes,
                "decoded_memory_write_bytes must be functional per instruction at {node:#x}"
            );
        }
    }
    let mut unknown_write_reason: HashMap<Node, &'static str> = HashMap::new();
    for (node, reason) in db.rel_iter::<(Address, &'static str)>("decoded_memory_write_unknown") {
        if let Some(previous) = unknown_write_reason.insert(*node, *reason) {
            assert_eq!(
                previous, *reason,
                "decoded_memory_write_unknown must be functional per instruction at {node:#x}"
            );
        }
    }

    let mach: HashSet<Node> = db
        .rel_iter::<(Address, crate::x86::types::MachInst)>("mach_inst")
        .map(|(n, _)| *n)
        .collect();
    let linear: HashSet<Node> = db
        .rel_iter::<(Address, crate::x86::types::LinearInst)>("linear_inst")
        .map(|(n, _)| *n)
        .collect();
    let ltl: HashSet<Node> = db
        .rel_iter::<(Node, crate::x86::types::LTLInst)>("ltl_inst")
        .map(|(n, _)| *n)
        .collect();

    let mut rtl_cand: HashSet<Node> = HashSet::new();
    let mut rtl_cand_inop: HashSet<Node> = HashSet::new();
    let mut rtl_move: HashMap<Node, Vec<(u64, u64)>> = HashMap::new();
    let mut rtl_non_move: HashSet<Node> = HashSet::new();
    let mut move_src_of: HashMap<u64, Vec<u64>> = HashMap::new();
    for (n, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst_candidate") {
        if matches!(inst, RTLInst::Inop) {
            rtl_cand_inop.insert(*n);
        } else {
            rtl_cand.insert(*n);
        }
        match inst {
            RTLInst::Iop(crate::x86::op::Operation::Omove, args, dst) if args.len() == 1 => {
                rtl_move.entry(*n).or_default().push((args[0], *dst));
                move_src_of.entry(*dst).or_default().push(args[0]);
            }
            RTLInst::Inop => {}
            _ => {
                rtl_non_move.insert(*n);
            }
        }
    }
    for sources in move_src_of.values_mut() {
        sources.sort_unstable();
        sources.dedup();
    }
    let mut rtl: HashSet<Node> = HashSet::new();
    let mut rtl_inop: HashSet<Node> = HashSet::new();
    for (n, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        if matches!(inst, RTLInst::Inop) {
            rtl_inop.insert(*n);
        } else {
            rtl.insert(*n);
        }
    }

    let cminor: HashSet<Node> = db
        .rel_iter::<(Node, crate::x86::types::CminorStmt)>("cminor_stmt")
        .map(|(n, _)| *n)
        .collect();
    let csh_cand: HashSet<Node> = db
        .rel_iter::<(Node, crate::x86::types::CsharpminorStmt)>("csharp_stmt_candidate")
        .map(|(n, _)| *n)
        .collect();
    let cshminor: HashSet<Node> = db
        .rel_iter::<(Node, crate::x86::types::CsharpminorStmt)>("csharp_stmt")
        .map(|(n, _)| *n)
        .collect();
    let clight_cand: HashSet<Node> = db
        .rel_iter::<(Node, ClightStmt)>("clight_stmt")
        .filter(|(_, s)| !is_trivial_stmt(s))
        .map(|(n, _)| *n)
        .collect();

    // Per-function Clight candidates: the export that selection consumes, and
    // the content the absorbed-statement check matches against.
    let mut clight_by_func: HashMap<Address, HashMap<Node, Vec<&ClightStmt>>> = HashMap::new();
    let mut clight: HashSet<Node> = HashSet::new();
    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        if is_trivial_stmt(stmt) {
            continue;
        }
        clight.insert(*node);
        clight_by_func
            .entry(*addr)
            .or_default()
            .entry(*node)
            .or_default()
            .push(stmt);
    }

    let printed_names: HashSet<&str> = match db.cast_optimized_translation_unit.as_ref() {
        Some(tu) => tu
            .decls
            .iter()
            .filter_map(|d| match d {
                TopLevelDecl::FuncDef(f) => Some(f.name.as_str()),
                _ => None,
            })
            .collect(),
        None => HashSet::new(),
    };

    let mut selected: HashSet<Node> = HashSet::new();
    let mut selected_comparison: HashSet<Node> = HashSet::new();
    let mut live_webs: HashSet<u64> = HashSet::new();
    let mut live_def_nodes: HashSet<Node> = HashSet::new();
    let mut funcs_with_return: HashSet<Address> = HashSet::new();
    let mut printed_funcs: HashSet<Address> = HashSet::new();
    let mut selected_write_bytes: HashMap<Node, usize> = HashMap::new();
    for func in &db.cast_selected_functions {
        if !printed_names.contains(func.name.as_str()) {
            continue;
        }
        printed_funcs.insert(func.address);
        record_selected(
            func,
            clight_by_func.get(&func.address),
            &mut selected,
            &mut selected_comparison,
            &mut live_webs,
            &mut live_def_nodes,
            &mut funcs_with_return,
        );
        for (node, bytes) in &func.selected_write_bytes {
            if !selected.contains(node) {
                continue;
            }
            selected_write_bytes
                .entry(*node)
                .and_modify(|old| *old = (*old).max(*bytes))
                .or_insert(*bytes);
        }
    }

    let mut succ: HashMap<Node, Vec<Node>> = HashMap::new();
    for name in ["rtl_succ", "clight_succ", "emit_next"] {
        for (a, b) in db.rel_iter::<(Node, Node)>(name) {
            succ.entry(*a).or_default().push(*b);
        }
    }
    for v in succ.values_mut() {
        v.sort_unstable();
        v.dedup();
    }

    let mut prev_by_addr: HashMap<Node, Vec<Node>> = HashMap::new();
    for (a, b) in db.rel_iter::<(Address, Address)>("next") {
        prev_by_addr.entry(*b).or_default().push(*a);
    }

    let mut flags_pair_of: HashMap<Node, Vec<Node>> = HashMap::new();
    for (cmp, jcc, _) in db.rel_iter::<(Address, Address, &'static str)>("flags_and_jump_pair") {
        flags_pair_of.entry(*cmp).or_default().push(*jcc);
    }

    let mut inlined_webs: HashSet<u64> = HashSet::new();
    for (reg, _) in db.rel_iter::<(u64, crate::x86::types::Constant)>("single_def_const") {
        inlined_webs.insert(*reg);
    }
    for reg in db.rel_iter::<u64>("emit_inline_temp") {
        inlined_webs.insert(*reg);
    }

    let mut plt_funcs: HashSet<Address> = HashSet::new();
    for name in ["plt_entry", "plt_block"] {
        for (addr, _) in db.rel_iter::<(Address, Symbol)>(name) {
            plt_funcs.insert(*addr);
        }
    }
    let external_funcs: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_external_function")
        .map(|(a,)| *a)
        .collect();

    let skipped_funcs: HashSet<Address> = func_names
        .iter()
        .filter(|(_, name)| name.starts_with('.') || db.should_skip_function(name.as_str()))
        .map(|(addr, _)| *addr)
        .collect();

    let trimmed: HashSet<Node> = db
        .rel_iter::<(Address,)>("trim_instruction")
        .map(|(a,)| *a)
        .collect();
    let jump_table_trim: HashSet<Node> = db
        .rel_iter::<(Node,)>("trim_jump_table_impl")
        .map(|(n,)| *n)
        .collect();
    let dead_store: HashSet<Node> = db
        .rel_iter::<(Node,)>("dead_store")
        .map(|(n,)| *n)
        .collect();
    let copy_eliminated: HashSet<Node> = db
        .rel_iter::<(Node,)>("copy_eliminated")
        .map(|(n,)| *n)
        .collect();
    let dead_var_store: HashSet<Node> = db
        .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
        .map(|(_, n, _)| *n)
        .collect();

    AuditInputs {
        insns,
        node_funcs,
        func_names,
        regs,
        imms,
        mems,
        guard_slot: db
            .target_abi
            .as_ref()
            .and_then(|abi| abi.stack_guard_slot()),
        mach,
        linear,
        ltl,
        rtl_cand,
        rtl_cand_inop,
        rtl,
        rtl_inop,
        cminor,
        csh_cand,
        cshminor,
        clight_cand,
        clight,
        selected,
        required_write_bytes,
        selected_write_bytes,
        unknown_write_reason,
        selected_comparison,
        succ,
        live_webs,
        live_def_nodes,
        rtl_move,
        rtl_non_move,
        move_src_of,
        prev_by_addr,
        flags_pair_of,
        inlined_webs,
        funcs_with_return,
        printed_funcs,
        plt_funcs,
        external_funcs,
        skipped_funcs,
        trimmed,
        jump_table_trim,
        dead_store,
        copy_eliminated,
        dead_var_store,
    }
}

/// Read one printed function's selected tree. Two things survive selection: a
/// node that still keys a non-trivial statement, and a solver-selected node
/// whose statement tree assembly folded into a parent. Candidate equality is
/// considered only for nodes with exact selection provenance: two nodes can
/// legitimately offer identical values while only one was selected.
fn record_selected(
    func: &SelectedFunction,
    candidates: Option<&HashMap<Node, Vec<&ClightStmt>>>,
    selected: &mut HashSet<Node>,
    selected_comparison: &mut HashSet<Node>,
    live_webs: &mut HashSet<u64>,
    live_def_nodes: &mut HashSet<Node>,
    funcs_with_return: &mut HashSet<Address>,
) {
    let mut subtrees: HashSet<&ClightStmt> = HashSet::new();
    for (node, stmt) in &func.statements {
        collect_subtrees(stmt, &mut subtrees);
        if is_trivial_stmt(stmt) {
            continue;
        }
        selected.insert(*node);
        if stmt_has_comparison(stmt) {
            selected_comparison.insert(*node);
        }
        if stmt_returns(stmt) {
            funcs_with_return.insert(func.address);
        }
        let mut idents = Vec::new();
        stmt_idents(stmt, &mut idents);
        for i in idents {
            live_webs.insert(i as u64);
            live_def_nodes.insert(web_def_node(i as u64));
        }
    }

    // Conditions guarding every selected branch subtree.  Tree assembly
    // rewrites an absorbed branch's ARMS by design -- a goto arm becomes the
    // inlined body it named, a loop exit becomes a break form -- while the
    // comparison itself is never rewritten by assembly.  A candidate branch
    // whose exact condition still guards a selected Sifthenelse therefore kept
    // its comparison; whole-statement equality would call every arm-rewritten
    // branch lost.
    let selected_conditions: HashSet<&ClightExpr> = subtrees
        .iter()
        .filter_map(|stmt| match stmt {
            ClightStmt::Sifthenelse(cond, _, _) => Some(cond),
            _ => None,
        })
        .collect();

    let Some(candidates) = candidates else {
        return;
    };
    for (node, cands) in candidates {
        if selected.contains(node) || !func.selected_candidate_nodes.contains(node) {
            continue;
        }
        for cand in cands {
            let stripped = strip_labels(cand);
            let matched = subtrees.contains(stripped)
                || matches!(stripped, ClightStmt::Sifthenelse(cond, _, _)
                    if selected_conditions.contains(cond)
                        || inverse_condition(cond)
                            .is_some_and(|inv| selected_conditions.contains(&inv)));
            if !matched {
                continue;
            }
            selected.insert(*node);
            if stmt_has_comparison(cand) {
                selected_comparison.insert(*node);
            }
            let mut idents = Vec::new();
            stmt_idents(cand, &mut idents);
            for i in idents {
                live_webs.insert(i as u64);
                live_def_nodes.insert(web_def_node(i as u64));
            }
            break;
        }
    }
}

// Classification

impl AuditInputs {
    fn any_in(&self, set: &HashSet<Node>, base: Node) -> bool {
        node_family(base).iter().any(|n| set.contains(n))
    }

    fn represented_write_bytes(&self, base: Node) -> usize {
        node_family(base).iter().fold(0usize, |total, node| {
            total.saturating_add(self.selected_write_bytes.get(node).copied().unwrap_or(0))
        })
    }

    /// The deepest layer that still has an artifact for this instruction.
    fn vanish_point(&self, base: Node) -> Layer {
        let ladder = [
            (Layer::Selected, &self.selected),
            (Layer::Clight, &self.clight),
            (Layer::ClightCandidate, &self.clight_cand),
            (Layer::Cshminor, &self.cshminor),
            (Layer::CshminorCandidate, &self.csh_cand),
            (Layer::Cminor, &self.cminor),
            (Layer::Rtl, &self.rtl),
            (Layer::RtlCandidate, &self.rtl_cand),
            (Layer::Ltl, &self.ltl),
            (Layer::Linear, &self.linear),
            (Layer::Mach, &self.mach),
        ];
        for (layer, set) in ladder {
            if self.any_in(set, base) {
                return layer;
            }
        }
        Layer::AsmOnly
    }

    fn shape_of(&self, t: &InsnTuple) -> String {
        let parts: Vec<String> = [t.4, t.5, t.6, t.7]
            .iter()
            .filter_map(|id| operand_shape(id, &self.regs, &self.imms, &self.mems))
            .collect();
        parts.join(",")
    }

    /// A register-to-register move, i.e. an instruction whose whole effect is
    /// to rename a value. Anything that also loads, stores, or computes is
    /// excluded: a lost effect is never justified by its destination flowing.
    fn is_reg_to_reg_copy(&self, t: &InsnTuple) -> bool {
        if !is_copy_mnemonic(t.3) {
            return false;
        }
        let ops: Vec<Symbol> = [t.4, t.5, t.6, t.7]
            .into_iter()
            .filter(|id| *id != "0")
            .collect();
        ops.len() == 2 && ops.iter().all(|id| self.regs.contains_key(id))
    }

    /// Frame bookkeeping: a push/pop of a frame or callee-saved register, a
    /// `leave`, or an add/sub/mov/lea that only moves the stack or frame pointer.
    fn is_frame_setup(&self, t: &InsnTuple) -> bool {
        let ops: Vec<Symbol> = [t.4, t.5, t.6, t.7]
            .into_iter()
            .filter(|id| *id != "0")
            .collect();
        let reg_names: Vec<&'static str> = ops
            .iter()
            .filter_map(|id| self.regs.get(id).copied())
            .collect();
        match t.3 {
            "LEAVE" => true,
            "PUSH" | "POP" => {
                !ops.is_empty()
                    && reg_names.len() == ops.len()
                    && reg_names.iter().all(|r| is_frame_register(r))
            }
            "ADD" | "SUB" | "MOV" | "LEA" => {
                // Every operand must be a frame register or an immediate, and
                // the instruction must touch the stack or frame pointer.
                if reg_names.is_empty() {
                    return false;
                }
                let all_frame = ops.iter().all(|id| {
                    self.regs
                        .get(id)
                        .map(|r| is_frame_register(r))
                        .unwrap_or_else(|| self.imms.contains(id))
                });
                all_frame
                    && reg_names
                        .iter()
                        .any(|r| matches!(*r, "RSP" | "ESP" | "RBP" | "EBP"))
            }
            _ => false,
        }
    }

    /// Does this instruction touch the stack-protector slot? The canary load,
    /// and the xor/sub that checks it, both name `%fs:0x28` directly.
    fn is_canary_access(&self, t: &InsnTuple) -> bool {
        [t.4, t.5, t.6, t.7]
            .iter()
            .filter_map(|id| self.mems.get(id))
            .any(|m| is_canary_slot(self.guard_slot, m))
    }

    /// A compare is folded only when a control-flow successor kept a real
    /// comparison in its selected statement. A branch that collapsed to a
    /// constant consumed nothing, so the compare feeding it is lost, not folded.
    fn compare_is_folded(&self, base: Node) -> bool {
        // The Mcond of a shadowed or secondary pair is keyed at the Jcc's own
        // address, leaving the compare with no artifact and no IR successor
        // edges of its own. The decoder's flags analysis names the consuming
        // Jcc exactly; a paired Jcc that kept a comparison is this compare.
        if self
            .flags_pair_of
            .get(&base)
            .into_iter()
            .flatten()
            .any(|jcc| self.any_in(&self.selected_comparison, *jcc))
        {
            return true;
        }
        let mut seen: HashSet<Node> = HashSet::new();
        let mut work: Vec<Node> = node_family(base).to_vec();
        let mut steps = 0usize;
        while let Some(n) = work.pop() {
            if !seen.insert(n) || steps > 64 {
                continue;
            }
            steps += 1;
            if n != base && self.selected_comparison.contains(&n) {
                return true;
            }
            if let Some(next) = self.succ.get(&n) {
                for &s in next {
                    // Cross only into a node that produced nothing of its own;
                    // a successor with its own statement is a different
                    // instruction and its comparison belongs to it.
                    if self.selected_comparison.contains(&s) || !self.selected.contains(&s) {
                        work.push(s);
                    }
                }
            }
        }
        false
    }

    /// Does a value web defined by this instruction still get referenced?
    fn def_web_flows(&self, base: Node) -> bool {
        self.any_in(&self.live_def_nodes, base)
    }

    /// The copy-propagation signature, read off the IR rather than guessed:
    /// every RTL form this instruction has is a move, its destination web is
    /// referenced nowhere in the output, and its source web is. The rename
    /// collapsed onto its source and the value still flows through it.
    fn rename_collapsed_onto_source(&self, base: Node) -> bool {
        let family = node_family(base);
        if family.iter().any(|n| self.rtl_non_move.contains(n)) {
            return false;
        }
        let mut saw_move = false;
        for n in family {
            for &(src, dst) in self.rtl_move.get(&n).into_iter().flatten() {
                saw_move = true;
                if self.live_webs.contains(&dst) || !self.chain_reaches_live_web(src) {
                    return false;
                }
            }
        }
        saw_move
    }

    /// Walk a chain of renames to the value it names. `mov a,b; mov b,c` leaves
    /// only a's web in the output, so the immediate source of the second move
    /// is not what survives -- the chain's end is.
    fn chain_reaches_live_web(&self, start: u64) -> bool {
        fn all_sources_reach_live(
            inputs: &AuditInputs,
            web: u64,
            visiting: &mut HashSet<u64>,
            memo: &mut HashMap<u64, bool>,
        ) -> bool {
            if inputs.live_webs.contains(&web) {
                return true;
            }
            if let Some(&answer) = memo.get(&web) {
                return answer;
            }
            if !visiting.insert(web) {
                // A rename cycle with no already-live web is not evidence that
                // the value survived.  Stay conservative rather than using an
                // arbitrary edge out of the cycle.
                return false;
            }
            let answer = inputs.move_src_of.get(&web).is_some_and(|sources| {
                !sources.is_empty()
                    && sources
                        .iter()
                        .all(|source| all_sources_reach_live(inputs, *source, visiting, memo))
            });
            visiting.remove(&web);
            memo.insert(web, answer);
            answer
        }

        all_sources_reach_live(self, start, &mut HashSet::new(), &mut HashMap::new())
    }

    /// Did this instruction only materialize a value the optimizer recorded as
    /// inlined at its use? The web it defines is spelled where it is read, so
    /// the instruction has no statement -- but only when nothing still
    /// references the web as a variable.
    fn value_was_inlined(&self, base: Node) -> bool {
        if self.def_web_flows(base) {
            return false;
        }
        self.inlined_webs
            .iter()
            .any(|&w| node_family(base).contains(&web_def_node(w)))
    }

    /// Was this conditional branch fused into the instruction that set its
    /// flags? asm_pass keys the condition at the flag-setting instruction, so
    /// the branch legitimately has no artifact of its own -- but only when that
    /// instruction's selected statement really carries a comparison.
    fn branch_is_folded(&self, base: Node) -> bool {
        self.prev_by_addr
            .get(&base)
            .into_iter()
            .flatten()
            .any(|p| self.selected_comparison.contains(p))
    }
}

struct Classification {
    verdict: Verdict,
    vanish: Layer,
    rtl_inop_only: bool,
    func_unprinted: bool,
}

fn classify(inputs: &AuditInputs, base: Node, t: &InsnTuple) -> Classification {
    let vanish = inputs.vanish_point(base);
    let rtl_inop_only = !inputs.any_in(&inputs.rtl, base)
        && !inputs.any_in(&inputs.rtl_cand, base)
        && (inputs.any_in(&inputs.rtl_inop, base) || inputs.any_in(&inputs.rtl_cand_inop, base));
    let empty = BTreeSet::new();
    let funcs = inputs.node_funcs.get(&base).unwrap_or(&empty);
    let func_unprinted = !funcs.iter().any(|f| inputs.printed_funcs.contains(f));

    let mut out = Classification {
        verdict: Verdict::Unaccounted,
        vanish,
        rtl_inop_only,
        func_unprinted,
    };

    if vanish == Layer::Selected {
        out.verdict = Verdict::Represented;
        return out;
    }

    let justify = |j: Justification| Classification {
        verdict: Verdict::Justified(j),
        vanish,
        rtl_inop_only,
        func_unprinted,
    };

    // Function-level absence first: when the whole function is gone by design,
    // the instruction's absence is that decision and nothing else.
    if !funcs.is_empty()
        && funcs
            .iter()
            .all(|f| inputs.plt_funcs.contains(f) || inputs.external_funcs.contains(f))
    {
        return justify(Justification::PltThunk);
    }
    if !funcs.is_empty() && funcs.iter().all(|f| inputs.skipped_funcs.contains(f)) {
        return justify(Justification::SkippedFunction);
    }

    // A kill names one exact semantic RTL node.  An audit row names the
    // decoded instruction, so its exact node family is the base plus the two
    // synthetic children into which lifting can split that instruction.
    // Credit a published member only at the boundary where the optimizer made
    // the decision: if any sibling artifact survived farther, that later loss
    // still needs its own explanation.
    if vanish == Layer::RtlCandidate {
        if inputs.any_in(&inputs.dead_store, base) {
            return justify(Justification::DeadStore);
        }
        if inputs.any_in(&inputs.copy_eliminated, base) {
            return justify(Justification::CopyEliminated);
        }
    }

    if inputs.trimmed.contains(&base) {
        return justify(Justification::TrimmedIdiom);
    }
    if inputs.is_canary_access(t) {
        return justify(Justification::StackCanary);
    }
    if inputs.any_in(&inputs.jump_table_trim, base) {
        return justify(Justification::JumpTableImpl);
    }
    if is_nop_mnemonic(t.3) {
        return justify(Justification::NopPadding);
    }
    if inputs.is_frame_setup(t) {
        return justify(Justification::FrameSetup);
    }
    if is_compare_mnemonic(t.3) && inputs.compare_is_folded(base) {
        return justify(Justification::CompareFolded);
    }
    if (inputs.is_reg_to_reg_copy(t) && inputs.def_web_flows(base))
        || inputs.rename_collapsed_onto_source(base)
    {
        return justify(Justification::CopyAbsorbed);
    }
    if is_conditional_branch(t.3) && inputs.branch_is_folded(base) {
        return justify(Justification::BranchFolded);
    }
    if inputs.value_was_inlined(base) {
        return justify(Justification::ValueInlined);
    }
    if matches!(t.3, "RET" | "RETF" | "REPZ RET")
        && funcs.iter().any(|f| inputs.funcs_with_return.contains(f))
    {
        return justify(Justification::ReturnFolded);
    }
    // A Clight-recorded dead store describes one candidate, so it excuses the
    // node only when no live Clight candidate remains at that instruction.
    if inputs.any_in(&inputs.dead_var_store, base) && !inputs.any_in(&inputs.clight, base) {
        return justify(Justification::DeadVarStore);
    }

    out
}

pub fn audit(db: &DecompileDB) -> CoverageReport {
    let inputs = collect(db);
    let mut report = CoverageReport::default();
    let post_emit = post_emit_visibility(db);
    report.post_emit_witnesses = post_emit.witnesses;
    report.post_emit_final_witnesses = post_emit.final_witnesses;
    report.post_emit_exact_survived = post_emit.exact_survived;
    report.post_emit_changed_or_removed = post_emit.changed_or_removed;
    report.post_emit_stages = post_emit.stages;
    report.post_emit_unattributed_changed_or_removed = post_emit.unattributed_changed_or_removed;

    for (&base, t) in &inputs.insns {
        let c = classify(&inputs, base, t);
        let required_write_bytes = inputs.required_write_bytes.get(&base).copied().unwrap_or(0);
        let selected_write_bytes = (required_write_bytes > 0)
            .then(|| inputs.represented_write_bytes(base))
            .unwrap_or(0);
        let represented_write_bytes = selected_write_bytes.min(required_write_bytes);
        let unknown_write_reason = inputs.unknown_write_reason.get(&base).copied();
        report.universe += 1;
        report.write_bytes_required = report
            .write_bytes_required
            .saturating_add(required_write_bytes);
        report.unknown_write_instructions += usize::from(unknown_write_reason.is_some());
        *report.vanish.entry(c.vanish.label()).or_insert(0) += 1;
        if c.rtl_inop_only {
            report.rtl_inop_only += 1;
        }
        match c.verdict {
            Verdict::Represented => {
                report.represented += 1;
                report.unknown_write_represented += usize::from(unknown_write_reason.is_some());
                report.write_bytes_represented = report
                    .write_bytes_represented
                    .saturating_add(represented_write_bytes);
                let gap = required_write_bytes.saturating_sub(represented_write_bytes);
                report.write_bytes_unaccounted = report.write_bytes_unaccounted.saturating_add(gap);
                if gap > 0 {
                    report.partial_write_instructions += 1;
                }
                let excess = selected_write_bytes.saturating_sub(required_write_bytes);
                report.write_bytes_overrepresented =
                    report.write_bytes_overrepresented.saturating_add(excess);
                if excess > 0 {
                    report.over_write_instructions += 1;
                }
            }
            Verdict::Justified(j) => {
                *report.justified.entry(j.label()).or_insert(0) += 1;
                report.unknown_write_justified += usize::from(unknown_write_reason.is_some());
                report.write_bytes_justified = report
                    .write_bytes_justified
                    .saturating_add(required_write_bytes);
            }
            Verdict::Unaccounted => {
                report.unaccounted += 1;
                report.unknown_write_unaccounted += usize::from(unknown_write_reason.is_some());
                report.write_bytes_unaccounted = report
                    .write_bytes_unaccounted
                    .saturating_add(required_write_bytes);
                *report
                    .unaccounted_vanish
                    .entry(c.vanish.label())
                    .or_insert(0) += 1;
                if c.func_unprinted {
                    report.unaccounted_in_unprinted += 1;
                }
            }
        }
        let func = inputs
            .node_funcs
            .get(&base)
            .and_then(|s| s.iter().next().copied())
            .unwrap_or(0);
        report.verdicts.push(InsnVerdict {
            node: base,
            func,
            func_name: inputs
                .func_names
                .get(&func)
                .cloned()
                .unwrap_or_else(|| format!("FUN_{:x}", func)),
            mnemonic: t.3,
            shape: inputs.shape_of(t),
            vanish: c.vanish,
            verdict: c.verdict,
            rtl_inop_only: c.rtl_inop_only,
            func_unprinted: c.func_unprinted,
            required_write_bytes,
            represented_write_bytes,
            selected_write_bytes,
            unknown_write_reason,
        });
    }

    // Zero-fill so every per-binary dump carries the same keys and the corpus
    // aggregation never has to guess a missing category was zero.
    for j in Justification::all() {
        report.justified.entry(j.label()).or_insert(0);
    }
    report
}

// Machine-readable dump

fn dump_path(db: &DecompileDB, dir: &str) -> std::path::PathBuf {
    let stem = db
        .binary_path
        .as_ref()
        .and_then(|p| p.file_name())
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    std::path::Path::new(dir).join(format!("{}.coverage.json", stem))
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_counts(map: &BTreeMap<&'static str, usize>) -> String {
    let body: Vec<String> = map
        .iter()
        .map(|(k, v)| format!("\n    {}: {}", json_str(k), v))
        .collect();
    format!("{{{}\n  }}", body.join(","))
}

fn json_post_emit_stages(stages: &[PostEmitStageReport]) -> String {
    let body: Vec<String> = stages
        .iter()
        .map(|stage| {
            format!(
                "\n    {}: {{\"all_witnesses_before\": {}, \"all_witnesses_after\": {}, \"baseline_exact_before\": {}, \"baseline_exact_after\": {}, \"newly_changed_or_removed\": {}, \"recovered\": {}, \"endpoint_changed_or_removed\": {}}}",
                json_str(stage.stage),
                stage.all_witnesses_before,
                stage.all_witnesses_after,
                stage.baseline_exact_before,
                stage.baseline_exact_after,
                stage.newly_changed_or_removed,
                stage.recovered,
                stage.endpoint_changed_or_removed,
            )
        })
        .collect();
    format!("{{{}\n  }}", body.join(","))
}

fn json_optional_pct(value: Option<f64>) -> String {
    value
        .map(|pct| format!("{pct:.4}"))
        .unwrap_or_else(|| "null".to_string())
}

fn log_optional_pct(value: Option<f64>) -> String {
    value
        .map(|pct| format!("{pct:.2}%"))
        .unwrap_or_else(|| "N/A".to_string())
}

/// JSON by hand: the record is flat, and the audit must not drag serde derives
/// onto the IR types it borrows from.
fn write_dump(db: &DecompileDB, report: &CoverageReport, dir: &str) {
    let path = dump_path(db, dir);
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let mut out = String::new();
    out.push_str("{\n  \"schema_version\": 3,\n");
    out.push_str(&format!(
        "  \"binary\": {},\n",
        json_str(
            &db.binary_path
                .as_ref()
                .map(|p| p.to_string_lossy().to_string())
                .unwrap_or_default()
        )
    ));
    out.push_str(&format!("  \"universe\": {},\n", report.universe));
    out.push_str(&format!("  \"represented\": {},\n", report.represented));
    out.push_str(&format!("  \"unaccounted\": {},\n", report.unaccounted));
    out.push_str(&format!(
        "  \"write_bytes_required\": {},\n",
        report.write_bytes_required
    ));
    out.push_str(&format!(
        "  \"write_bytes_represented\": {},\n",
        report.write_bytes_represented
    ));
    out.push_str(&format!(
        "  \"write_bytes_justified\": {},\n",
        report.write_bytes_justified
    ));
    out.push_str(&format!(
        "  \"write_bytes_unaccounted\": {},\n",
        report.write_bytes_unaccounted
    ));
    out.push_str(&format!(
        "  \"partial_write_instructions\": {},\n",
        report.partial_write_instructions
    ));
    out.push_str(&format!(
        "  \"write_bytes_overrepresented\": {},\n  \"over_write_instructions\": {},\n",
        report.write_bytes_overrepresented, report.over_write_instructions
    ));
    out.push_str(&format!(
        "  \"unknown_write_instructions\": {},\n  \"unknown_write_represented\": {},\n  \"unknown_write_justified\": {},\n  \"unknown_write_unaccounted\": {},\n",
        report.unknown_write_instructions,
        report.unknown_write_represented,
        report.unknown_write_justified,
        report.unknown_write_unaccounted
    ));
    out.push_str(&format!(
        "  \"write_coverage_pct\": {},\n",
        json_optional_pct(report.write_coverage_pct())
    ));
    out.push_str(&format!(
        "  \"post_emit_metric\": \"exact-syntactic-witness-persistence\",\n  \"post_emit_witnesses\": {},\n  \"post_emit_final_witnesses\": {},\n  \"post_emit_exact_survived\": {},\n  \"post_emit_changed_or_removed\": {},\n  \"post_emit_unattributed_changed_or_removed\": {},\n  \"post_emit_stage_attribution\": {},\n  \"post_emit_exact_presence_pct\": {},\n",
        report.post_emit_witnesses,
        report.post_emit_final_witnesses,
        report.post_emit_exact_survived,
        report.post_emit_changed_or_removed,
        report.post_emit_unattributed_changed_or_removed,
        json_post_emit_stages(&report.post_emit_stages),
        json_optional_pct(report.post_emit_exact_presence_pct())
    ));
    out.push_str(&format!("  \"rtl_inop_only\": {},\n", report.rtl_inop_only));
    out.push_str(&format!(
        "  \"unaccounted_in_unprinted\": {},\n",
        report.unaccounted_in_unprinted
    ));
    out.push_str(&format!(
        "  \"coverage_pct\": {:.4},\n",
        report.coverage_pct()
    ));
    out.push_str(&format!(
        "  \"justified\": {},\n",
        json_counts(&report.justified)
    ));
    out.push_str(&format!("  \"vanish\": {},\n", json_counts(&report.vanish)));
    out.push_str(&format!(
        "  \"unaccounted_vanish\": {},\n",
        json_counts(&report.unaccounted_vanish)
    ));
    out.push_str("  \"instructions\": [");
    let mut first = true;
    for v in &report.verdicts {
        if !first {
            out.push(',');
        }
        first = false;
        let verdict = match v.verdict {
            Verdict::Represented => "represented".to_string(),
            Verdict::Justified(j) => format!("justified:{}", j.label()),
            Verdict::Unaccounted => "unaccounted".to_string(),
        };
        out.push_str(&format!(
            "\n    {{\"addr\": \"{:#x}\", \"func\": \"{:#x}\", \"func_name\": {}, \"mnemonic\": {}, \"shape\": {}, \"vanish\": {}, \"verdict\": {}, \"rtl_inop_only\": {}, \"func_unprinted\": {}, \"required_write_bytes\": {}, \"represented_write_bytes\": {}, \"selected_write_bytes\": {}, \"unknown_write_reason\": {}}}",
            v.node,
            v.func,
            json_str(&v.func_name),
            json_str(v.mnemonic),
            json_str(&v.shape),
            json_str(v.vanish.label()),
            json_str(&verdict),
            v.rtl_inop_only,
            v.func_unprinted,
            v.required_write_bytes,
            v.represented_write_bytes,
            v.selected_write_bytes,
            json_str(v.unknown_write_reason.unwrap_or(""))
        ));
    }
    out.push_str("\n  ]\n}\n");
    if let Err(e) = std::fs::write(&path, out) {
        log::warn!("coverage: failed to write {}: {}", path.display(), e);
    }
}

// Pass

pub struct CoverageAuditPass;

impl IRPass for CoverageAuditPass {
    fn name(&self) -> &'static str {
        "coverage_audit"
    }

    fn run(&self, db: &mut DecompileDB) {
        // The selected trees and the printed tree are typed fields, not
        // relations, so a parallel sub-DB would not carry them and every
        // instruction would look lost. Refuse to report rather than report a
        // number that is an artifact of scheduling.
        if db.cast_selected_functions.is_empty() || db.cast_optimized_translation_unit.is_none() {
            log::warn!(
                "coverage: no selected functions or no emitted tree on this DB; audit skipped"
            );
            return;
        }
        let report = audit(db);
        if report.universe == 0 {
            return;
        }

        let just: Vec<String> = report
            .justified
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect();
        let vanish: Vec<String> = report
            .vanish
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect();
        let post_emit_attribution: Vec<String> = report
            .post_emit_stages
            .iter()
            .map(|stage| format!("{}={}", stage.stage, stage.endpoint_changed_or_removed))
            .collect();
        eprintln!(
            "[coverage] universe={} represented={} justified={} unaccounted={} coverage={:.2}% write-bytes={}/{} justified-bytes={} gap-bytes={} over-bytes={} write-coverage={} partial-writes={} over-writes={} unknown-writes={}/{} justified-unknown={} gap-unknown={} post-emit-exact={}/{} changed-or-removed={} post-emit-exact-presence={} post-emit-stage-attribution=[{}] post-emit-unattributed={} rtl-inop-only={} unprinted-fn={} just[{}] vanish[{}]",
            report.universe,
            report.represented,
            report.justified_total(),
            report.unaccounted,
            report.coverage_pct(),
            report.write_bytes_represented,
            report.write_bytes_required,
            report.write_bytes_justified,
            report.write_bytes_unaccounted,
            report.write_bytes_overrepresented,
            log_optional_pct(report.write_coverage_pct()),
            report.partial_write_instructions,
            report.over_write_instructions,
            report.unknown_write_represented,
            report.unknown_write_instructions,
            report.unknown_write_justified,
            report.unknown_write_unaccounted,
            report.post_emit_exact_survived,
            report.post_emit_witnesses,
            report.post_emit_changed_or_removed,
            log_optional_pct(report.post_emit_exact_presence_pct()),
            post_emit_attribution.join(","),
            report.post_emit_unattributed_changed_or_removed,
            report.rtl_inop_only,
            report.unaccounted_in_unprinted,
            just.join(" "),
            vanish.join(" "),
        );

        if let Ok(dir) = std::env::var("MANIFOLD_COVERAGE_DUMP") {
            if !dir.is_empty() {
                write_dump(db, &report, &dir);
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "unrefinedinstruction",
            "instr_in_function",
            "emit_function",
            "func_entry",
            "op_register",
            "op_immediate",
            "op_indirect",
            "decoded_memory_write_bytes",
            "decoded_memory_write_unknown",
            "mach_inst",
            "linear_inst",
            "ltl_inst",
            "rtl_inst_candidate",
            "rtl_inst",
            "cminor_stmt",
            "csharp_stmt_candidate",
            "csharp_stmt",
            "clight_stmt",
            "clight_stmt_dead",
            "emit_clight_stmt",
            "rtl_succ",
            "clight_succ",
            "emit_next",
            "next",
            "flags_and_jump_pair",
            "plt_entry",
            "plt_block",
            "is_external_function",
            "single_def_const",
            "emit_inline_temp",
            "dead_store",
            "copy_eliminated",
            "trim_instruction",
            "trim_jump_table_impl",
            // Typed handoffs rather than relations, but the scheduler orders on
            // the declared name: reading them places this pass after every
            // writer of the selected trees and of the printed tree.
            "cast_selected_functions",
            "cast_post_emit_audit_trail",
            "cast_optimized_translation_unit",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::{ClightAttr, ClightIntSize, ClightSignedness, ClightType};

    fn int_ty() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn long_ty() -> ClightType {
        ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default())
    }

    const NO: Symbol = "0";

    fn insn(addr: Address, mnem: &'static str, ops: [Symbol; 4]) -> InsnTuple {
        (addr, 4, "", mnem, ops[0], ops[1], ops[2], ops[3], 0, 0)
    }

    fn mem(seg: &'static str, base: &'static str, disp: i64, size: usize) -> MemOperand {
        MemOperand {
            seg,
            base,
            index: "NONE",
            disp,
            size,
        }
    }

    fn web_at(node: Node) -> u64 {
        (node << crate::decompile::passes::rtl_pass::MREG_DISCRIMINANT_BITS) | 3
    }

    /// SelectedFunction has no Default; build one with only the fields the
    /// audit reads populated.
    fn selected_func(statements: Vec<(Node, ClightStmt)>) -> SelectedFunction {
        let statements: HashMap<_, _> = statements.into_iter().collect();
        SelectedFunction {
            address: 0x1000,
            name: "f".to_string(),
            entry_node: 0x1000,
            return_type: int_ty(),
            param_regs: Vec::new(),
            param_types: Vec::new(),
            stack_size: 0,
            structure_world:
                crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_STRUCTURED,
            selected_candidate_nodes: statements.keys().copied().collect(),
            statements,
            selected_write_bytes: Default::default(),
            successors: Default::default(),
            used_regs: Default::default(),
            struct_fields: Default::default(),
            sseq_groups: Default::default(),
            var_types: Default::default(),
            var_type_candidates: Default::default(),
            var_decl_idx: Default::default(),
            loop_headers: Default::default(),
            switch_heads: Default::default(),
            reg_struct_ids: Default::default(),
            loop_info: Default::default(),
        }
    }

    /// A bare shell: no artifacts anywhere, no functions, nothing justified.
    fn empty_inputs() -> AuditInputs {
        AuditInputs {
            insns: BTreeMap::new(),
            node_funcs: BTreeMap::new(),
            func_names: HashMap::new(),
            regs: HashMap::new(),
            imms: HashSet::new(),
            mems: HashMap::new(),
            guard_slot: crate::abi::AbiConfig::sysv_x86_64().stack_guard_slot(),
            mach: HashSet::new(),
            linear: HashSet::new(),
            ltl: HashSet::new(),
            rtl_cand: HashSet::new(),
            rtl_cand_inop: HashSet::new(),
            rtl: HashSet::new(),
            rtl_inop: HashSet::new(),
            cminor: HashSet::new(),
            csh_cand: HashSet::new(),
            cshminor: HashSet::new(),
            clight_cand: HashSet::new(),
            clight: HashSet::new(),
            selected: HashSet::new(),
            required_write_bytes: HashMap::new(),
            selected_write_bytes: HashMap::new(),
            unknown_write_reason: HashMap::new(),
            selected_comparison: HashSet::new(),
            succ: HashMap::new(),
            live_webs: HashSet::new(),
            live_def_nodes: HashSet::new(),
            rtl_move: HashMap::new(),
            rtl_non_move: HashSet::new(),
            move_src_of: HashMap::new(),
            prev_by_addr: HashMap::new(),
            flags_pair_of: HashMap::new(),
            inlined_webs: HashSet::new(),
            funcs_with_return: HashSet::new(),
            printed_funcs: HashSet::new(),
            plt_funcs: HashSet::new(),
            external_funcs: HashSet::new(),
            skipped_funcs: HashSet::new(),
            trimmed: HashSet::new(),
            jump_table_trim: HashSet::new(),
            dead_store: HashSet::new(),
            copy_eliminated: HashSet::new(),
            dead_var_store: HashSet::new(),
        }
    }

    fn own(inputs: &mut AuditInputs, node: Node, func: Address) {
        inputs.node_funcs.entry(node).or_default().insert(func);
        inputs.printed_funcs.insert(func);
    }

    #[test]
    fn a_node_with_a_selected_statement_is_represented() {
        let mut i = empty_inputs();
        own(&mut i, 0x1000, 0x1000);
        i.selected.insert(0x1000);
        let t = insn(0x1000, "ADD", [NO, NO, NO, NO]);
        let c = classify(&i, 0x1000, &t);
        assert_eq!(c.verdict, Verdict::Represented);
        assert_eq!(c.vanish, Layer::Selected);
    }

    #[test]
    fn a_statement_that_survived_only_as_a_synth_subnode_still_counts() {
        let mut i = empty_inputs();
        own(&mut i, 0x1000, 0x1000);
        // An RMW fuses into one address: the store half lands at synth2.
        i.selected.insert(0x1000 | SYNTH_NODE_BIT2);
        let t = insn(0x1000, "OR", [NO, NO, NO, NO]);
        assert_eq!(classify(&i, 0x1000, &t).verdict, Verdict::Represented);
    }

    #[test]
    fn a_store_with_no_artifact_anywhere_is_unaccounted_at_asm() {
        let mut i = empty_inputs();
        own(&mut i, 0x2000, 0x1000);
        let t = insn(0x2000, "MOVUPS", [NO, NO, NO, NO]);
        let c = classify(&i, 0x2000, &t);
        assert_eq!(c.verdict, Verdict::Unaccounted);
        assert_eq!(c.vanish, Layer::AsmOnly);
    }

    #[test]
    fn an_artifact_that_died_between_rtl_and_clight_is_unaccounted_at_rtl() {
        let mut i = empty_inputs();
        own(&mut i, 0x3000, 0x1000);
        i.mach.insert(0x3000);
        i.linear.insert(0x3000);
        i.ltl.insert(0x3000);
        i.rtl_cand.insert(0x3000);
        i.rtl.insert(0x3000);
        let t = insn(0x3000, "MOVUPS", [NO, NO, NO, NO]);
        let c = classify(&i, 0x3000, &t);
        assert_eq!(c.verdict, Verdict::Unaccounted);
        assert_eq!(c.vanish, Layer::Rtl);
    }

    #[test]
    fn optimizer_kills_are_justified_only_at_the_pre_opt_boundary() {
        let mut i = empty_inputs();
        own(&mut i, 0x3050, 0x1000);
        own(&mut i, 0x3060, 0x1000);
        i.mach.insert(0x3050);
        i.mach.insert(0x3060);
        i.ltl.insert(0x3050);
        i.ltl.insert(0x3060);
        i.rtl_cand.insert(0x3050);
        i.rtl_cand.insert(0x3060);

        // A pre-opt disappearance without a production decision remains a
        // defect candidate.  Facts for unrelated nodes must not turn the
        // relation into a blanket optimizer justification.
        let dead = insn(0x3050, "XOR", [NO, NO, NO, NO]);
        i.dead_store.insert(0xdead);
        i.copy_eliminated.insert(0xbeef);
        assert_eq!(classify(&i, 0x3050, &dead).verdict, Verdict::Unaccounted);
        assert_eq!(
            classify(&i, 0x3060, &insn(0x3060, "MOV", [NO, NO, NO, NO])).verdict,
            Verdict::Unaccounted
        );

        i.dead_store.insert(0x3050);
        i.copy_eliminated.insert(0x3060);
        assert_eq!(
            classify(&i, 0x3050, &dead).verdict,
            Verdict::Justified(Justification::DeadStore)
        );
        assert_eq!(
            classify(&i, 0x3060, &insn(0x3060, "MOV", [NO, NO, NO, NO])).verdict,
            Verdict::Justified(Justification::CopyEliminated)
        );

        // The same fact cannot excuse a later loss: some non-trivial artifact
        // survived the optimizer and still vanished downstream.
        i.rtl.insert(0x3050);
        assert_eq!(classify(&i, 0x3050, &dead).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn audit_collects_production_optimizer_kill_relations() {
        let mut db = DecompileDB::default();
        db.rel_push("dead_store", (0x3050_u64,));
        db.rel_push("copy_eliminated", (0x3060_u64,));

        let inputs = collect(&db);
        assert_eq!(inputs.dead_store, HashSet::from([0x3050]));
        assert_eq!(inputs.copy_eliminated, HashSet::from([0x3060]));
        assert!(CoverageAuditPass.inputs().contains(&"dead_store"));
        assert!(CoverageAuditPass.inputs().contains(&"copy_eliminated"));
    }

    #[test]
    fn a_node_that_reached_clight_and_lost_selection_is_unaccounted_at_clight() {
        let mut i = empty_inputs();
        own(&mut i, 0x3100, 0x1000);
        i.mach.insert(0x3100);
        i.clight.insert(0x3100);
        let c = classify(&i, 0x3100, &insn(0x3100, "ADD", [NO, NO, NO, NO]));
        assert_eq!(c.verdict, Verdict::Unaccounted);
        assert_eq!(c.vanish, Layer::Clight);
    }

    #[test]
    fn a_candidate_dropped_before_the_per_function_export_vanishes_at_clight_cand() {
        let mut i = empty_inputs();
        own(&mut i, 0x3200, 0x1000);
        i.mach.insert(0x3200);
        i.clight_cand.insert(0x3200);
        let c = classify(&i, 0x3200, &insn(0x3200, "ADD", [NO, NO, NO, NO]));
        assert_eq!(c.vanish, Layer::ClightCandidate);
    }

    #[test]
    fn a_folded_cmp_whose_branch_kept_the_comparison_is_justified() {
        let mut i = empty_inputs();
        own(&mut i, 0x4000, 0x1000);
        own(&mut i, 0x4002, 0x1000);
        i.succ.insert(0x4000, vec![0x4002]);
        i.selected.insert(0x4002);
        i.selected_comparison.insert(0x4002);
        let t = insn(0x4000, "CMP", [NO, NO, NO, NO]);
        assert_eq!(
            classify(&i, 0x4000, &t).verdict,
            Verdict::Justified(Justification::CompareFolded)
        );
    }

    #[test]
    fn a_cmp_whose_branch_lost_the_comparison_is_unaccounted() {
        let mut i = empty_inputs();
        own(&mut i, 0x4000, 0x1000);
        own(&mut i, 0x4002, 0x1000);
        i.succ.insert(0x4000, vec![0x4002]);
        // The branch survived, but with no comparison left in it.
        i.selected.insert(0x4002);
        let t = insn(0x4000, "CMP", [NO, NO, NO, NO]);
        assert_eq!(classify(&i, 0x4000, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn a_reg_move_is_justified_only_when_its_web_is_referenced() {
        let mut i = empty_inputs();
        own(&mut i, 0x5000, 0x1000);
        i.regs.insert("o1", "RAX");
        i.regs.insert("o2", "RBX");
        let t = insn(0x5000, "MOV", ["o1", "o2", NO, NO]);

        // No web anywhere: the move vanished with nothing to show for it.
        assert_eq!(classify(&i, 0x5000, &t).verdict, Verdict::Unaccounted);

        // A web defined at this node IS referenced downstream.
        i.live_def_nodes.insert(web_def_node(web_at(0x5000)));
        i.live_webs.insert(web_at(0x5000));
        assert_eq!(
            classify(&i, 0x5000, &t).verdict,
            Verdict::Justified(Justification::CopyAbsorbed)
        );
    }

    #[test]
    fn a_flowing_web_never_justifies_a_lost_computation() {
        let mut i = empty_inputs();
        own(&mut i, 0x5100, 0x1000);
        i.regs.insert("o1", "RAX");
        i.regs.insert("o2", "RBX");
        // An ADD is not a rename: its destination flowing proves nothing about
        // the addition, which is gone.
        let t = insn(0x5100, "ADD", ["o1", "o2", NO, NO]);
        i.live_def_nodes.insert(web_def_node(web_at(0x5100)));
        i.live_webs.insert(web_at(0x5100));
        assert_eq!(classify(&i, 0x5100, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn a_memory_source_move_is_not_a_rename() {
        let mut i = empty_inputs();
        own(&mut i, 0x5200, 0x1000);
        i.regs.insert("o1", "RAX");
        i.mems.insert("o2", mem("NONE", "RBX", 8, 8));
        let t = insn(0x5200, "MOV", ["o1", "o2", NO, NO]);
        i.live_def_nodes.insert(web_def_node(web_at(0x5200)));
        i.live_webs.insert(web_at(0x5200));
        assert_eq!(classify(&i, 0x5200, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn nops_and_landing_pads_are_justified_but_a_direction_flag_write_is_not() {
        let mut i = empty_inputs();
        own(&mut i, 0x6000, 0x1000);
        own(&mut i, 0x6004, 0x1000);
        assert_eq!(
            classify(&i, 0x6000, &insn(0x6000, "ENDBR64", [NO, NO, NO, NO])).verdict,
            Verdict::Justified(Justification::NopPadding)
        );
        assert_eq!(
            classify(&i, 0x6004, &insn(0x6004, "CLD", [NO, NO, NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn frame_bookkeeping_is_justified_but_a_general_push_is_not() {
        let mut i = empty_inputs();
        own(&mut i, 0x7000, 0x1000);
        own(&mut i, 0x7001, 0x1000);
        i.regs.insert("rbp", "RBP");
        i.regs.insert("rdi", "RDI");
        assert_eq!(
            classify(&i, 0x7000, &insn(0x7000, "PUSH", ["rbp", NO, NO, NO])).verdict,
            Verdict::Justified(Justification::FrameSetup)
        );
        // Pushing an argument register is a call-setup store, not frame setup.
        assert_eq!(
            classify(&i, 0x7001, &insn(0x7001, "PUSH", ["rdi", NO, NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn a_sub_that_moves_the_stack_pointer_is_frame_setup_but_one_on_a_gpr_is_not() {
        let mut i = empty_inputs();
        own(&mut i, 0x7100, 0x1000);
        own(&mut i, 0x7200, 0x1000);
        i.regs.insert("rsp", "RSP");
        i.regs.insert("rax", "RAX");
        i.imms.insert("i32");
        assert_eq!(
            classify(&i, 0x7100, &insn(0x7100, "SUB", ["i32", "rsp", NO, NO])).verdict,
            Verdict::Justified(Justification::FrameSetup)
        );
        assert_eq!(
            classify(&i, 0x7200, &insn(0x7200, "SUB", ["i32", "rax", NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn only_the_protector_slot_counts_as_canary_bookkeeping() {
        let mut i = empty_inputs();
        own(&mut i, 0xc000, 0x1000);
        own(&mut i, 0xc008, 0x1000);
        i.regs.insert("rax", "RAX");
        i.mems.insert("canary", mem("FS", "NONE", 0x28, 8));
        // Another thread-local slot is program data; losing it is a defect.
        i.mems.insert("tls", mem("FS", "NONE", -0x40, 8));
        assert_eq!(
            classify(&i, 0xc000, &insn(0xc000, "MOV", ["canary", "rax", NO, NO])).verdict,
            Verdict::Justified(Justification::StackCanary)
        );
        assert_eq!(
            classify(&i, 0xc008, &insn(0xc008, "MOV", ["tls", "rax", NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn a_branch_fused_into_its_flag_setter_is_justified() {
        let mut i = empty_inputs();
        own(&mut i, 0xd000, 0x1000);
        own(&mut i, 0xd002, 0x1000);
        i.prev_by_addr.insert(0xd002, vec![0xd000]);
        let je = insn(0xd002, "JE", [NO, NO, NO, NO]);
        // The flag setter kept no comparison: the branch is lost, not folded.
        i.selected.insert(0xd000);
        assert_eq!(classify(&i, 0xd002, &je).verdict, Verdict::Unaccounted);
        i.selected_comparison.insert(0xd000);
        assert_eq!(
            classify(&i, 0xd002, &je).verdict,
            Verdict::Justified(Justification::BranchFolded)
        );
    }

    #[test]
    fn an_unconditional_jump_is_never_a_folded_branch() {
        let mut i = empty_inputs();
        own(&mut i, 0xd010, 0x1000);
        own(&mut i, 0xd012, 0x1000);
        i.prev_by_addr.insert(0xd012, vec![0xd010]);
        i.selected_comparison.insert(0xd010);
        assert_eq!(
            classify(&i, 0xd012, &insn(0xd012, "JMP", [NO, NO, NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn a_rename_that_collapsed_onto_its_source_is_justified() {
        let mut i = empty_inputs();
        own(&mut i, 0xe000, 0x1000);
        let src = web_at(0x100);
        let dst = web_at(0xe000);
        i.rtl_move.insert(0xe000, vec![(src, dst)]);
        i.move_src_of.insert(dst, vec![src]);
        let t = insn(0xe000, "MOV", [NO, NO, NO, NO]);

        // Neither web is referenced: the move went nowhere.
        assert_eq!(classify(&i, 0xe000, &t).verdict, Verdict::Unaccounted);

        // The source flows and the destination does not: copy propagation.
        i.live_webs.insert(src);
        assert_eq!(
            classify(&i, 0xe000, &t).verdict,
            Verdict::Justified(Justification::CopyAbsorbed)
        );

        // A node that also carries a non-move RTL form is not a pure rename.
        i.rtl_non_move.insert(0xe000);
        assert_eq!(classify(&i, 0xe000, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn a_rename_chain_is_followed_to_the_web_that_survives() {
        let mut i = empty_inputs();
        own(&mut i, 0xe100, 0x1000);
        // mov a,b at 0xe0f0 then mov b,c at 0xe100: only a's web survives.
        let a = web_at(0x100);
        let b = web_at(0xe0f0);
        let c = web_at(0xe100);
        i.rtl_move.insert(0xe100, vec![(b, c)]);
        i.move_src_of.insert(c, vec![b]);
        i.move_src_of.insert(b, vec![a]);
        let t = insn(0xe100, "MOV", [NO, NO, NO, NO]);

        // Only the far end of the chain is referenced.
        i.live_webs.insert(a);
        assert_eq!(
            classify(&i, 0xe100, &t).verdict,
            Verdict::Justified(Justification::CopyAbsorbed)
        );

        // Break the chain: nothing it could have named survives.
        i.move_src_of.remove(&b);
        assert_eq!(classify(&i, 0xe100, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn every_alternative_rename_source_must_reach_a_live_web() {
        let mut i = empty_inputs();
        own(&mut i, 0xe200, 0x1000);
        let live = web_at(0x100);
        let dead = web_at(0x200);
        let dst = web_at(0xe200);
        i.rtl_move.insert(0xe200, vec![(live, dst), (dead, dst)]);
        i.move_src_of.insert(dst, vec![dead, live]);
        i.live_webs.insert(live);
        let t = insn(0xe200, "MOV", [NO, NO, NO, NO]);

        assert_eq!(classify(&i, 0xe200, &t).verdict, Verdict::Unaccounted);
        i.live_webs.insert(dead);
        assert_eq!(
            classify(&i, 0xe200, &t).verdict,
            Verdict::Justified(Justification::CopyAbsorbed)
        );
    }

    #[test]
    fn a_label_wrapped_candidate_matches_the_statement_assembly_inlined() {
        let inner = ClightStmt::Scall(None, ClightExpr::EvarSymbol("f".into(), int_ty()), vec![]);
        let labeled = ClightStmt::Slabel(0x1004, Box::new(inner.clone()));
        // Assembly inlined the bare call into an if body and dropped the label.
        let mut func = selected_func(vec![(
            0x1000u64,
            ClightStmt::Sifthenelse(
                ClightExpr::Etempvar(1, int_ty()),
                Box::new(ClightStmt::Sskip),
                Box::new(inner.clone()),
            ),
        )]);
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&labeled]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(selected.contains(&0x1004));
    }

    #[test]
    fn equal_candidate_at_an_unselected_node_is_not_credited() {
        let folded = ClightStmt::Sset(9, ClightExpr::EconstInt(1, int_ty()));
        let mut func = selected_func(vec![(
            0x1000,
            ClightStmt::Sifthenelse(
                ClightExpr::Etempvar(1, int_ty()),
                Box::new(folded.clone()),
                Box::new(ClightStmt::Sskip),
            ),
        )]);
        // Only 0x1004 was chosen. 0x1008 offered the same statement value,
        // which is not provenance that it survived selection.
        func.selected_candidate_nodes.insert(0x1004);
        let candidates = HashMap::from([(0x1004, vec![&folded]), (0x1008, vec![&folded])]);
        let mut selected = HashSet::new();
        record_selected(
            &func,
            Some(&candidates),
            &mut selected,
            &mut HashSet::new(),
            &mut HashSet::new(),
            &mut HashSet::new(),
            &mut HashSet::new(),
        );
        assert!(selected.contains(&0x1004));
        assert!(!selected.contains(&0x1008));
    }

    #[test]
    fn a_value_the_optimizer_recorded_as_inlined_is_justified() {
        let mut i = empty_inputs();
        own(&mut i, 0xf000, 0x1000);
        let w = web_at(0xf000);
        let t = insn(0xf000, "MOV", [NO, NO, NO, NO]);
        assert_eq!(classify(&i, 0xf000, &t).verdict, Verdict::Unaccounted);

        i.inlined_webs.insert(w);
        assert_eq!(
            classify(&i, 0xf000, &t).verdict,
            Verdict::Justified(Justification::ValueInlined)
        );

        // A web still referenced as a variable is not inlined away; the node
        // owed a statement and did not produce one.
        i.live_def_nodes.insert(0xf000);
        assert_eq!(classify(&i, 0xf000, &t).verdict, Verdict::Unaccounted);
    }

    #[test]
    fn a_plt_thunk_body_is_justified() {
        let mut i = empty_inputs();
        own(&mut i, 0x8000, 0x8000);
        i.plt_funcs.insert(0x8000);
        assert_eq!(
            classify(&i, 0x8000, &insn(0x8000, "JMP", [NO, NO, NO, NO])).verdict,
            Verdict::Justified(Justification::PltThunk)
        );
    }

    #[test]
    fn a_ret_is_justified_only_when_the_function_returns_somewhere() {
        let mut i = empty_inputs();
        own(&mut i, 0x9000, 0x1000);
        let t = insn(0x9000, "RET", [NO, NO, NO, NO]);
        assert_eq!(classify(&i, 0x9000, &t).verdict, Verdict::Unaccounted);
        i.funcs_with_return.insert(0x1000);
        assert_eq!(
            classify(&i, 0x9000, &t).verdict,
            Verdict::Justified(Justification::ReturnFolded)
        );
    }

    #[test]
    fn a_recorded_dead_var_store_is_justified_but_a_surviving_candidate_is_not() {
        let mut i = empty_inputs();
        own(&mut i, 0xa000, 0x1000);
        own(&mut i, 0xa004, 0x1000);
        i.dead_var_store.insert(0xa000);
        i.dead_var_store.insert(0xa004);
        // The second node still has a live candidate, so the dead marking on it
        // describes a different candidate and cannot excuse the loss.
        i.clight.insert(0xa004);
        assert_eq!(
            classify(&i, 0xa000, &insn(0xa000, "MOV", [NO, NO, NO, NO])).verdict,
            Verdict::Justified(Justification::DeadVarStore)
        );
        assert_eq!(
            classify(&i, 0xa004, &insn(0xa004, "MOV", [NO, NO, NO, NO])).verdict,
            Verdict::Unaccounted
        );
    }

    #[test]
    fn an_instruction_in_an_unprinted_function_is_flagged() {
        let mut i = empty_inputs();
        i.node_funcs.entry(0xb000).or_default().insert(0x1000);
        let c = classify(&i, 0xb000, &insn(0xb000, "ADD", [NO, NO, NO, NO]));
        assert_eq!(c.verdict, Verdict::Unaccounted);
        assert!(c.func_unprinted);
    }

    #[test]
    fn a_trivial_selected_statement_is_not_representation() {
        assert!(is_trivial_stmt(&ClightStmt::Sskip));
        assert!(is_trivial_stmt(&ClightStmt::Slabel(
            7,
            Box::new(ClightStmt::Sskip)
        )));
        assert!(is_trivial_stmt(&ClightStmt::Ssequence(vec![
            ClightStmt::Sskip,
            ClightStmt::Slabel(1, Box::new(ClightStmt::Sskip)),
        ])));
        assert!(!is_trivial_stmt(&ClightStmt::Sgoto(3)));
    }

    #[test]
    fn a_selected_label_wrapping_nothing_leaves_its_node_unrepresented() {
        let func = selected_func(vec![
            (
                0x1000u64,
                ClightStmt::Slabel(1, Box::new(ClightStmt::Sskip)),
            ),
            (0x1004u64, ClightStmt::Sgoto(1)),
        ]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            None,
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(!selected.contains(&0x1000));
        assert!(selected.contains(&0x1004));
    }

    #[test]
    fn a_statement_tree_assembly_folded_into_a_parent_still_counts_as_selected() {
        let folded = ClightStmt::Sset(9, ClightExpr::EconstInt(1, int_ty()));
        let mut func = selected_func(vec![(
            0x1000u64,
            ClightStmt::Sifthenelse(
                ClightExpr::Etempvar(1, int_ty()),
                Box::new(folded.clone()),
                Box::new(ClightStmt::Sskip),
            ),
        )]);
        // 0x1004's key is gone from `statements`, but its statement is a
        // subtree of the if that absorbed it.
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&folded]);

        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(selected.contains(&0x1000));
        assert!(selected.contains(&0x1004));
    }

    #[test]
    fn a_branch_absorbed_with_rewritten_arms_still_counts_by_its_condition() {
        let cond = ClightExpr::Ebinop(
            ClightBinaryOp::Oeq,
            Box::new(ClightExpr::Etempvar(1, int_ty())),
            Box::new(ClightExpr::EconstInt(0, int_ty())),
            int_ty(),
        );
        // The candidate branch as exported: label-wrapped, goto arms.
        let cand = ClightStmt::Slabel(
            0x1004,
            Box::new(ClightStmt::Sifthenelse(
                cond.clone(),
                Box::new(ClightStmt::Sgoto(2)),
                Box::new(ClightStmt::Sgoto(3)),
            )),
        );
        // Assembly absorbed it into a parent and inlined the goto arms into
        // bodies, so no subtree equals the candidate -- but the comparison
        // still guards the selected branch.
        let mut func = selected_func(vec![(
            0x1000u64,
            ClightStmt::Sifthenelse(
                ClightExpr::Etempvar(9, int_ty()),
                Box::new(ClightStmt::Sifthenelse(
                    cond.clone(),
                    Box::new(ClightStmt::Sreturn(None)),
                    Box::new(ClightStmt::Sset(7, ClightExpr::EconstInt(1, int_ty()))),
                )),
                Box::new(ClightStmt::Sskip),
            ),
        )]);
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&cand]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(selected.contains(&0x1004));
        assert!(cmp.contains(&0x1004));
    }

    #[test]
    fn a_loop_exit_spelled_with_the_inverse_comparison_still_counts() {
        // Candidate: if (t >= 0) goto out.  Loop assembly's pre-built break
        // guard spells it if (t < 0) break -- same operands, inverse operator.
        let cand = ClightStmt::Sifthenelse(
            ClightExpr::Ebinop(
                ClightBinaryOp::Oge,
                Box::new(ClightExpr::Etempvar(1, int_ty())),
                Box::new(ClightExpr::EconstInt(0, int_ty())),
                int_ty(),
            ),
            Box::new(ClightStmt::Sgoto(2)),
            Box::new(ClightStmt::Sgoto(3)),
        );
        let mut func = selected_func(vec![(
            0x1000u64,
            ClightStmt::Sloop(
                Box::new(ClightStmt::Sifthenelse(
                    ClightExpr::Ebinop(
                        ClightBinaryOp::Olt,
                        Box::new(ClightExpr::Etempvar(1, int_ty())),
                        Box::new(ClightExpr::EconstInt(0, int_ty())),
                        int_ty(),
                    ),
                    Box::new(ClightStmt::Sbreak),
                    Box::new(ClightStmt::Sskip),
                )),
                Box::new(ClightStmt::Sskip),
            ),
        )]);
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&cand]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(selected.contains(&0x1004));
        assert!(cmp.contains(&0x1004));
    }

    #[test]
    fn a_branch_whose_condition_survives_nowhere_is_not_credited() {
        let cand = ClightStmt::Sifthenelse(
            ClightExpr::Ebinop(
                ClightBinaryOp::Oeq,
                Box::new(ClightExpr::Etempvar(1, int_ty())),
                Box::new(ClightExpr::EconstInt(0, int_ty())),
                int_ty(),
            ),
            Box::new(ClightStmt::Sgoto(2)),
            Box::new(ClightStmt::Sgoto(3)),
        );
        // The selected tree has a branch, but on a DIFFERENT comparison.
        let mut func = selected_func(vec![(
            0x1000u64,
            ClightStmt::Sifthenelse(
                ClightExpr::Ebinop(
                    ClightBinaryOp::One,
                    Box::new(ClightExpr::Etempvar(5, int_ty())),
                    Box::new(ClightExpr::EconstInt(0, int_ty())),
                    int_ty(),
                ),
                Box::new(ClightStmt::Sreturn(None)),
                Box::new(ClightStmt::Sskip),
            ),
        )]);
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&cand]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(!selected.contains(&0x1004));
    }

    #[test]
    fn a_candidate_absent_from_the_tree_is_not_credited() {
        let missing = ClightStmt::Sset(9, ClightExpr::EconstInt(42, int_ty()));
        let mut func = selected_func(vec![(0x1000u64, ClightStmt::Sgoto(1))]);
        func.selected_candidate_nodes.insert(0x1004);
        let mut cands: HashMap<Node, Vec<&ClightStmt>> = HashMap::new();
        cands.insert(0x1004, vec![&missing]);
        let mut selected = HashSet::new();
        let mut cmp = HashSet::new();
        let mut raw: HashSet<u64> = HashSet::new();
        let mut webs: HashSet<Node> = HashSet::new();
        let mut rets = HashSet::new();
        record_selected(
            &func,
            Some(&cands),
            &mut selected,
            &mut cmp,
            &mut raw,
            &mut webs,
            &mut rets,
        );
        assert!(!selected.contains(&0x1004));
    }

    #[test]
    fn only_a_real_comparison_counts_as_a_kept_compare() {
        let cond = ClightExpr::Ebinop(
            ClightBinaryOp::Olt,
            Box::new(ClightExpr::Etempvar(1, int_ty())),
            Box::new(ClightExpr::EconstInt(0, int_ty())),
            int_ty(),
        );
        assert!(stmt_has_comparison(&ClightStmt::Sifthenelse(
            cond,
            Box::new(ClightStmt::Sgoto(1)),
            Box::new(ClightStmt::Sskip),
        )));
        assert!(!stmt_has_comparison(&ClightStmt::Sifthenelse(
            ClightExpr::EconstInt(1, int_ty()),
            Box::new(ClightStmt::Sgoto(1)),
            Box::new(ClightStmt::Sskip),
        )));
    }

    #[test]
    fn coverage_excludes_justified_absence_from_the_denominator() {
        let mut r = CoverageReport {
            universe: 100,
            represented: 60,
            unaccounted: 20,
            ..CoverageReport::default()
        };
        r.justified.insert("nop-padding", 20);
        assert_eq!(r.justified_total(), 20);
        assert!((r.coverage_pct() - 75.0).abs() < 1e-9);
    }

    #[test]
    fn write_coverage_exposes_a_partial_wide_store() {
        let store = |id| {
            ClightStmt::Sassign(
                ClightExpr::Evar(id, long_ty()),
                ClightExpr::EconstLong(0, long_ty()),
            )
        };
        assert_eq!(stmt_memory_write_bytes(&store(1), 8), 8);
        assert_eq!(
            stmt_memory_write_bytes(&ClightStmt::Ssequence(vec![store(1), store(2)]), 8),
            16
        );
        assert_eq!(
            stmt_memory_write_bytes(
                &ClightStmt::Sifthenelse(
                    ClightExpr::EconstInt(1, int_ty()),
                    Box::new(store(1)),
                    Box::new(store(2)),
                ),
                8,
            ),
            8
        );

        let mut report = CoverageReport {
            write_bytes_required: 16,
            write_bytes_represented: 8,
            write_bytes_unaccounted: 8,
            partial_write_instructions: 1,
            ..CoverageReport::default()
        };
        assert!((report.write_coverage_pct().unwrap() - 50.0).abs() < 1e-9);
        report.write_bytes_justified = 8;
        assert!((report.write_coverage_pct().unwrap() - 100.0).abs() < 1e-9);
        report.write_bytes_justified = 16;
        assert_eq!(report.write_coverage_pct(), None);
        assert_eq!(
            CoverageReport::default().post_emit_exact_presence_pct(),
            None
        );
    }

    #[test]
    fn only_a_proven_stack_sset_satisfies_a_write_width() {
        let stack_local = 7;
        let ordinary_temp = 8;
        let stack_set = ClightStmt::Sset(stack_local, ClightExpr::EconstLong(42, long_ty()));
        let temp_set = ClightStmt::Sset(ordinary_temp, ClightExpr::EconstLong(42, long_ty()));

        // Context-free Ssets remain SSA computations, even when their RHS is
        // wide enough to resemble the decoded store.
        assert_eq!(stmt_memory_write_bytes(&stack_set, 8), 0);

        let mut stack_var_types = HashMap::from([(stack_local, long_ty())]);
        assert_eq!(
            stmt_selected_write_bytes(&stack_set, 8, &stack_var_types),
            8
        );
        assert_eq!(stmt_selected_write_bytes(&temp_set, 8, &stack_var_types), 0);

        // The selected destination declaration, not a wider RHS, determines
        // how much of the architectural write the recovered cell represents.
        stack_var_types.insert(stack_local, int_ty());
        assert_eq!(
            stmt_selected_write_bytes(&stack_set, 8, &stack_var_types),
            4
        );
    }

    #[test]
    fn selected_synth_stores_sum_to_the_decoded_width() {
        let low = ClightStmt::Sassign(
            ClightExpr::Evar(1, long_ty()),
            ClightExpr::EconstLong(0, long_ty()),
        );
        let high = ClightStmt::Sassign(
            ClightExpr::Evar(2, long_ty()),
            ClightExpr::EconstLong(0, long_ty()),
        );
        let base = 0x1000;
        let mut func = selected_func(vec![
            (base | SYNTH_NODE_BIT, low.clone()),
            (base | SYNTH_NODE_BIT2, high.clone()),
        ]);
        func.selected_write_bytes = [
            (base | SYNTH_NODE_BIT, stmt_memory_write_bytes(&low, 8)),
            (base | SYNTH_NODE_BIT2, stmt_memory_write_bytes(&high, 8)),
        ]
        .into_iter()
        .collect();
        let mut inputs = empty_inputs();
        inputs.selected_write_bytes = func.selected_write_bytes;
        assert_eq!(inputs.represented_write_bytes(base), 16);
    }

    #[test]
    fn post_emit_visibility_attributes_only_the_unrecovered_stage_loss() {
        use crate::decompile::passes::c_pass::types::{CType, FuncDef, SourceLoc, StorageClass};

        let effect = CStmt::Expr(CExpr::assign(CExpr::var("x"), CExpr::int(1)));
        let ret = CStmt::Return(Some(CExpr::int(0)));
        let tu = |body, local_vars| TranslationUnit {
            decls: vec![TopLevelDecl::FuncDef(FuncDef {
                name: "f".to_string(),
                return_type: CType::int(),
                params: Vec::new(),
                is_variadic: false,
                storage_class: StorageClass::Auto,
                body,
                local_vars,
                loc: SourceLoc::unknown(),
            })],
            ..TranslationUnit::default()
        };
        let initial = tu(
            CStmt::Sequence(vec![effect.clone(), ret.clone()]),
            Vec::new(),
        );
        let without_effect = tu(ret.clone(), Vec::new());
        let mut trail = PostEmitAuditTrail::new(&initial);
        trail
            .record(PostEmitCheckpoint::ClightEmitFinalize, &initial)
            .unwrap();
        trail
            .record(PostEmitCheckpoint::ForLoop, &without_effect)
            .unwrap();
        // The exact effect spelling returns at the next checkpoint.  Its
        // transient forloop loss must not remain in endpoint attribution.
        trail
            .record(PostEmitCheckpoint::VarReduce, &initial)
            .unwrap();

        let mut db = DecompileDB::default();
        db.cast_post_emit_audit_trail = Some(trail);
        db.cast_optimized_translation_unit = Some(tu(ret, Vec::new()));
        let visibility = post_emit_visibility(&db);
        assert_eq!(visibility.witnesses, 2);
        assert_eq!(visibility.final_witnesses, 1);
        assert_eq!(visibility.exact_survived, 1);
        assert_eq!(visibility.changed_or_removed, 1);
        assert_eq!(visibility.unattributed_changed_or_removed, 0);
        assert_eq!(
            visibility
                .stages
                .iter()
                .map(|stage| stage.endpoint_changed_or_removed)
                .collect::<Vec<_>>(),
            vec![0, 0, 0, 1]
        );
        assert_eq!(visibility.stages[1].newly_changed_or_removed, 1);
        assert_eq!(visibility.stages[2].recovered, 1);
        assert_eq!(visibility.stages[3].newly_changed_or_removed, 1);
    }

    #[test]
    fn post_emit_visibility_normalizes_assignment_initializers() {
        use crate::decompile::passes::c_pass::types::{CType, FuncDef, SourceLoc, StorageClass};

        let effect = CStmt::Expr(CExpr::assign(CExpr::var("x"), CExpr::int(1)));
        let tu = |body, local_vars| TranslationUnit {
            decls: vec![TopLevelDecl::FuncDef(FuncDef {
                name: "f".to_string(),
                return_type: CType::int(),
                params: Vec::new(),
                is_variadic: false,
                storage_class: StorageClass::Auto,
                body,
                local_vars,
                loc: SourceLoc::unknown(),
            })],
            ..TranslationUnit::default()
        };

        // Moving the same assignment into a declaration initializer is a
        // structural rewrite, not effect erosion.
        let initial = tu(effect.clone(), vec![VarDecl::new("x", CType::int())]);
        let initialized = tu(
            CStmt::Empty,
            vec![VarDecl::new("x", CType::int()).with_init(Initializer::Expr(CExpr::int(1)))],
        );
        let mut trail = PostEmitAuditTrail::new(&initial);
        trail
            .record(PostEmitCheckpoint::ClightEmitFinalize, &initial)
            .unwrap();
        trail.record(PostEmitCheckpoint::ForLoop, &initial).unwrap();
        trail
            .record(PostEmitCheckpoint::VarReduce, &initialized)
            .unwrap();
        let mut db = DecompileDB::default();
        db.cast_post_emit_audit_trail = Some(trail);
        db.cast_optimized_translation_unit = Some(initialized);
        let visibility = post_emit_visibility(&db);
        assert_eq!(visibility.witnesses, 1);
        assert_eq!(visibility.exact_survived, 1);
        assert_eq!(visibility.changed_or_removed, 0);
        assert!(visibility
            .stages
            .iter()
            .all(|stage| stage.endpoint_changed_or_removed == 0));
    }

    #[test]
    fn a_web_id_reports_the_node_that_defined_it() {
        let node = 0x4015a0u64;
        assert_eq!(web_def_node(web_at(node)), node);
    }

    #[test]
    fn the_operand_shape_separates_a_wide_store_from_a_scalar_one() {
        let mut regs = HashMap::new();
        regs.insert("v", "XMM0");
        let imms = HashSet::new();
        let mut mems = HashMap::new();
        mems.insert("m16", mem("NONE", "RAX", 8, 16));
        mems.insert("m8", mem("NONE", "RAX", 8, 8));
        mems.insert("msp", mem("NONE", "RSP", 24, 4));
        assert_eq!(
            operand_shape("v", &regs, &imms, &mems).as_deref(),
            Some("r:vec")
        );
        assert_eq!(
            operand_shape("m16", &regs, &imms, &mems).as_deref(),
            Some("m16[gen]")
        );
        assert_eq!(
            operand_shape("m8", &regs, &imms, &mems).as_deref(),
            Some("m8[gen]")
        );
        assert_eq!(
            operand_shape("msp", &regs, &imms, &mems).as_deref(),
            Some("m4[sp]")
        );
        assert_eq!(operand_shape("0", &regs, &imms, &mems), None);
    }
}
