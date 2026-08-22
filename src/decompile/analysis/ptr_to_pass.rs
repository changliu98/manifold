use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::run_pass;

use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// Pointer provenance analysis: tracks how each pointer base was derived
ascent_par! {
    #![measure_rule_times]
    #[swap_db]
    pub struct PtrToPassProgram;

    relation rtl_inst(Node, RTLInst);
    relation instr_in_function(Node, Address);
    relation emit_function_param_candidate(Address, RTLReg);
    relation call_site(Node, Symbol);
    relation call_return_reg(Node, RTLReg);
    relation allocation_site(Node, RTLReg, usize);

    // Allocator names are extensional knowledge.  Keeping them as facts makes
    // allocation-site discovery an ordinary join instead of an imperative
    // HashMap/HashSet pre-pass.
    #[local] relation allocator_function(Symbol);
    // Language/POSIX vocabulary.
    allocator_function("malloc");
    allocator_function("calloc");
    allocator_function("realloc");
    allocator_function("reallocarray");
    allocator_function("aligned_alloc");
    allocator_function("strdup");
    allocator_function("strndup");
    // GNU/gnulib's widely deployed fail-fast allocator wrappers.
    allocator_function("xmalloc");
    allocator_function("xcalloc");
    allocator_function("xrealloc");
    allocator_function("xreallocarray");
    allocator_function("ximalloc");
    allocator_function("xirealloc");
    allocator_function("xicalloc");
    allocator_function("xireallocarray");
    allocator_function("xzalloc");
    allocator_function("xizalloc");
    allocator_function("xcharalloc");
    allocator_function("xnmalloc");
    allocator_function("xinmalloc");
    allocator_function("xnrealloc");
    allocator_function("x2realloc");
    allocator_function("x2nrealloc");
    allocator_function("xpalloc");
    allocator_function("imalloc");
    allocator_function("irealloc");
    allocator_function("icalloc");
    allocator_function("ireallocarray");
    allocator_function("xstrdup");
    allocator_function("xstrndup");
    allocator_function("xmemdup");
    allocator_function("ximemdup");
    allocator_function("ximemdup0");

    allocation_site(node, result_reg, 0usize) <--
        call_site(node, name),
        allocator_function(name),
        call_return_reg(node, result_reg);

    // (func, reg, provenance_id)
    relation provenance_root(Address, RTLReg, u64);
    // (func, src_reg, dst_reg, edge_type, offset)
    relation provenance_edge(Address, RTLReg, RTLReg, EdgeType, i64);
    // (func, reg, root_reg, root_provenance_id, accumulated_offset, depth)
    relation provenance_chain(Address, RTLReg, RTLReg, u64, i64, usize);

    // Roots: function params and allocation return values
    provenance_root(func, param_reg, provenance_id) <--
        emit_function_param_candidate(func, param_reg),
        let provenance_id = compute_provenance_id(*func, *param_reg);

    provenance_root(func, result_reg, provenance_id) <--
        instr_in_function(node, func),
        allocation_site(node, result_reg, _),
        let provenance_id = compute_provenance_id(*func, *result_reg);

    // PT-2: offset window guards against large immediates (absolute addresses, wide constants) creating spurious Embed edges into integer registers and mis-typing them as pointers. The bound is config::CONFIG.ptr_to.embed_max_offset, which documents that it is empirical rather than derived; it lives there because CLAUDE.md keeps tuned constants out of rule bodies, and because five rules below share it and must not drift apart.
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed(offset)), args, dst)),
        if args.len() >= 1,
        if offset.abs() < CONFIG.ptr_to.embed_max_offset,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oaddlimm(offset), args, dst)),
        if args.len() >= 1,
        if offset.abs() < CONFIG.ptr_to.embed_max_offset,
        let src = args[0];

    // Embed edges from LEA with indexed2 addressing (base + index + offset)
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed2(offset)), args, dst)),
        if args.len() >= 1,
        if offset.abs() < CONFIG.ptr_to.embed_max_offset,
        let src = args[0];

    // Embed edges from LEA with scaled indexed addressing (base + index*scale + offset)
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed2scaled(_, offset)), args, dst)),
        if args.len() >= 1,
        if offset.abs() < CONFIG.ptr_to.embed_max_offset,
        let src = args[0];

    // Oaddl/Osubl have non-constant RHS: use Assign (alias-only) so acc_ofs stays honest.
    provenance_edge(func, src, dst, EdgeType::Assign, 0) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oaddl, args, dst)),
        if args.len() >= 1,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Assign, 0) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Osubl, args, dst)),
        if args.len() >= 1,
        let src = args[0];

    // Deref edges from 64-bit loads (pointer-to-pointer patterns)
    provenance_edge(func, src, dst, EdgeType::Deref, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed(offset), args, dst)),
        if *chunk == MemoryChunk::MAny64 || *chunk == MemoryChunk::MInt64,
        if args.len() >= 1,
        if offset.abs() < CONFIG.ptr_to.embed_max_offset,
        let src = args[0];

    // Assign edges from Omove (register copy)
    provenance_edge(func, src, dst, EdgeType::Assign, 0) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        let src = args[0];

    // PT-3: depth=6 is a termination guarantee, not a precision knob -- provenance_edge contains cycles, so an unbounded depth makes acc_ofs diverge; measured on corpus, depth 6 truncated nothing.
    provenance_chain(func, reg, reg, prov_id, 0, 0) <--
        provenance_root(func, reg, prov_id);

    provenance_chain(func, dst, root, prov_id, acc_ofs + offset, depth + 1) <--
        provenance_chain(func, src, root, prov_id, acc_ofs, depth),
        provenance_edge(func, src, dst, ?EdgeType::Embed, offset),
        if *depth < 6;

    provenance_chain(func, dst, root, prov_id, acc_ofs, depth + 1) <--
        provenance_chain(func, src, root, prov_id, acc_ofs, depth),
        provenance_edge(func, src, dst, ?EdgeType::Assign, _),
        if *depth < 6;

    // A chain has pointer evidence only when a member is actually DEREFERENCED; an Embed edge (LEA) is not standalone evidence, since gcc emits LEA for plain integer arithmetic too.
    #[local] relation chain_has_ptr_evidence(Address, RTLReg, u64);
    chain_has_ptr_evidence(func, root, prov_id) <--
        provenance_chain(func, src, root, prov_id, _, _),
        provenance_edge(func, src, _, ?EdgeType::Deref, _);

    relation emit_var_type_candidate(RTLReg, XType);
    emit_var_type_candidate(reg, XType::Xptr) <--
        provenance_chain(func, reg, root, prov_id, _, _),
        chain_has_ptr_evidence(func, root, prov_id);

    // HARD 32-bit-int evidence: an operand of a genuine 32-bit comparison (excluding the NULL-check form) is never a pointer, so it safely brakes forward root-evidence propagation.
    #[local] relation hard_int32(RTLReg);
    hard_int32(reg) <--
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if is_hard_int_cmp_cond(cond),
        for reg in args.iter();

    // PT-1: an Assign-only copy chain types as pointer when its ROOT carries pointer evidence; forward-only, so the bidirectional int/ptr pollution the type pass disabled cannot arise.
    #[local] relation reg_has_ptr_candidate(RTLReg);
    reg_has_ptr_candidate(reg) <--
        emit_var_type_candidate(reg, xt),
        if matches!(xt, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr
            | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    // Gated !hard_int32: do not carry a pointer root forward into the integer half of a register reused across roles; a genuine pointer member still types via its own deref evidence.
    emit_var_type_candidate(reg, XType::Xptr) <--
        provenance_chain(_, reg, root, _, _, _),
        reg_has_ptr_candidate(root),
        !hard_int32(reg);

    // Pointee refinement is a set property: a tracked value receives a
    // concrete pointer type exactly when all of its indexed dereferences use
    // one chunk.  Mixed chunks retain the generic Xptr candidate because they
    // usually describe fields of a recovered struct.
    #[local] relation provenance_deref_chunk(Address, RTLReg, MemoryChunk);
    provenance_deref_chunk(func, base_reg, *chunk) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed(_), args, _)),
        if !args.is_empty(),
        let base_reg = args[0],
        provenance_chain(func, base_reg, _, _, _, _);
    provenance_deref_chunk(func, base_reg, *chunk) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed(_), args, _)),
        if !args.is_empty(),
        let base_reg = args[0],
        provenance_chain(func, base_reg, _, _, _, _);

    #[local] relation provenance_has_mixed_chunks(Address, RTLReg);
    provenance_has_mixed_chunks(func, reg) <--
        provenance_deref_chunk(func, reg, left),
        provenance_deref_chunk(func, reg, right),
        if left != right;

    emit_var_type_candidate(reg, XType::Xptr) <--
        provenance_has_mixed_chunks(_, reg);

    emit_var_type_candidate(reg, xt) <--
        provenance_deref_chunk(func, reg, chunk),
        !provenance_has_mixed_chunks(func, reg),
        let xt = pointee_xtype_for_chunk(*chunk);

    // An assign-only (zero accumulated offset) descendant can also establish
    // that its provenance root is char-addressed.  Wider pointee types are not
    // lifted to the root: doing so would rescale byte displacements into
    // element units and can walk beyond the object.
    #[local] relation provenance_root_deref_chunk(Address, RTLReg, MemoryChunk);
    provenance_root_deref_chunk(func, root, *chunk) <--
        provenance_chain(func, reg, root, _, acc_ofs, _),
        if *acc_ofs == 0,
        if reg != root,
        provenance_deref_chunk(func, reg, chunk);

    #[local] relation provenance_root_has_mixed_chunks(Address, RTLReg);
    provenance_root_has_mixed_chunks(func, root) <--
        provenance_root_deref_chunk(func, root, left),
        provenance_root_deref_chunk(func, root, right),
        if left != right;

    emit_var_type_candidate(root, XType::Xcharptr) <--
        provenance_root_deref_chunk(func, root, chunk),
        !provenance_root_has_mixed_chunks(func, root),
        let xt = pointee_xtype_for_chunk(*chunk),
        if xt == XType::Xcharptr;
}

// A genuine 32-bit comparison that is not the compare-against-0 NULL check; such an operand is an integer, never a pointer.
fn is_hard_int_cmp_cond(cond: &Condition) -> bool {
    let is32 = matches!(
        cond,
        Condition::Ccomp(_)
            | Condition::Ccompu(_)
            | Condition::Ccompimm(_, _)
            | Condition::Ccompuimm(_, _)
    );
    let is_null = matches!(
        cond,
        Condition::Ccompimm(Comparison::Ceq, 0)
            | Condition::Ccompuimm(Comparison::Ceq, 0)
            | Condition::Ccompimm(Comparison::Cne, 0)
            | Condition::Ccompuimm(Comparison::Cne, 0)
    );
    is32 && !is_null
}

// Unique provenance ID from function address and register
pub fn compute_provenance_id(func: Address, reg: RTLReg) -> u64 {
    let mut hasher = DefaultHasher::new();
    func.hash(&mut hasher);
    reg.hash(&mut hasher);
    hasher.finish()
}

pub struct PtrToPass;

impl IRPass for PtrToPass {
    fn name(&self) -> &'static str {
        "ptr_to"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, PtrToPassProgram);
    }

    fn inputs(&self) -> &'static [&'static str] {
        static INPUTS: &[&str] = &[
            "rtl_inst",
            "instr_in_function",
            "emit_function_param_candidate",
            "allocation_site",
            "call_site",
            "call_return_reg",
        ];
        INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        static OUTPUTS: &[&str] = &[
            "allocation_site",
            "emit_var_type_candidate",
            "provenance_root",
            "provenance_edge",
            "provenance_chain",
        ];
        OUTPUTS
    }
}

// Pointee type implied by a single deref chunk width/class.
fn pointee_xtype_for_chunk(chunk: MemoryChunk) -> XType {
    match chunk {
        MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool => {
            XType::Xcharptr
        }
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => XType::Xintptr,
        MemoryChunk::MFloat64 => XType::Xfloatptr,
        MemoryChunk::MFloat32 => XType::Xsingleptr,
        _ => XType::Xptr,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn allocator_and_pointee_facts_are_derived_in_one_fixpoint() {
        let function = 0x1000;
        let root = 100;
        let derived = 101;
        let mixed = 300;
        let mut prog = PtrToPassProgram::default();
        prog.call_site.push((1, "malloc"));
        prog.call_return_reg.push((1, 10));
        prog.call_site.push((2, "ordinary_function"));
        prog.call_return_reg.push((2, 20));
        prog.emit_function_param_candidate.push((function, root));
        prog.emit_function_param_candidate.push((function, mixed));
        prog.rtl_inst.push((
            3,
            RTLInst::Iop(Operation::Omove, Arc::new(vec![root]), derived),
        ));
        prog.rtl_inst.push((
            4,
            RTLInst::Iload(
                MemoryChunk::MInt8Unsigned,
                Addressing::Aindexed(0),
                Arc::new(vec![derived]),
                200,
            ),
        ));
        prog.rtl_inst.push((
            5,
            RTLInst::Iload(
                MemoryChunk::MInt32,
                Addressing::Aindexed(0),
                Arc::new(vec![mixed]),
                301,
            ),
        ));
        prog.rtl_inst.push((
            6,
            RTLInst::Iload(
                MemoryChunk::MInt64,
                Addressing::Aindexed(8),
                Arc::new(vec![mixed]),
                302,
            ),
        ));
        for node in 3..=6 {
            prog.instr_in_function.push((node, function));
        }

        prog.run();

        assert!(prog.allocation_site.iter().any(|row| row == &(1, 10, 0)));
        assert!(!prog.allocation_site.iter().any(|row| row.0 == 2));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(derived, XType::Xcharptr)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(root, XType::Xcharptr)));
        assert!(!prog.emit_var_type_candidate.iter().any(|row| {
            row.0 == mixed
                && matches!(
                    row.1,
                    XType::Xcharptr | XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr
                )
        }));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(mixed, XType::Xptr)));
    }
}
