
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::run_pass;

use std::collections::{HashMap, HashSet};
use crate::x86::op::{Addressing, Operation};
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
    relation allocation_site(Node, RTLReg, usize);

    // (func, reg, provenance_id)
    relation provenance_root(Address, RTLReg, u64);
    // (func, src_reg, dst_reg, edge_type, offset)
    relation provenance_edge(Address, RTLReg, RTLReg, EdgeType, i64);
    // (func, reg, root_reg, root_provenance_id, accumulated_offset, depth)
    relation provenance_chain(Address, RTLReg, RTLReg, u64, i64, usize);
    // (func, child_root, child_prov_id, parent_root, parent_prov_id, deref_offset)
    relation provenance_deref_link(Address, RTLReg, u64, RTLReg, u64, i64);

    // Roots: function params and allocation return values
    provenance_root(func, param_reg, provenance_id) <--
        emit_function_param_candidate(func, param_reg),
        let provenance_id = compute_provenance_id(*func, *param_reg);

    provenance_root(func, result_reg, provenance_id) <--
        instr_in_function(node, func),
        allocation_site(node, result_reg, _),
        let provenance_id = compute_provenance_id(*func, *result_reg);

    // Embed edges from LEA/add-immediate with offset in [0, 2048)
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed(offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Aindexed(offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oaddlimm(offset), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    // Embed edges from LEA with indexed2 addressing (base + index + offset)
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed2(offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Aindexed2(offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    // Embed edges from LEA with scaled indexed addressing (base + index*scale + offset)
    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed2scaled(_, offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    provenance_edge(func, src, dst, EdgeType::Embed, offset) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Aindexed2scaled(_, offset)), args, dst)),
        if args.len() >= 1,
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    // Embed edges from Oaddl (variable pointer addition, offset unknown -> 0)
    provenance_edge(func, src, dst, EdgeType::Embed, 0) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Oaddl, args, dst)),
        if args.len() >= 1,
        let src = args[0];

    // Embed edges from Osubl (pointer subtraction, offset unknown -> 0)
    provenance_edge(func, src, dst, EdgeType::Embed, 0) <--
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
        if *offset >= 0 && *offset < 2048,
        let src = args[0];

    // Assign edges from Omove (register copy)
    provenance_edge(func, src, dst, EdgeType::Assign, 0) <--
        instr_in_function(node, func),
        rtl_inst(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        let src = args[0];

    // Chain propagation from roots, depth-limited to 3
    provenance_chain(func, reg, reg, prov_id, 0, 0) <--
        provenance_root(func, reg, prov_id);

    provenance_chain(func, dst, root, prov_id, acc_ofs + offset, depth + 1) <--
        provenance_chain(func, src, root, prov_id, acc_ofs, depth),
        provenance_edge(func, src, dst, ?EdgeType::Embed, offset),
        if *depth < 3;

    provenance_chain(func, dst, root, prov_id, acc_ofs, depth + 1) <--
        provenance_chain(func, src, root, prov_id, acc_ofs, depth),
        provenance_edge(func, src, dst, ?EdgeType::Assign, _),
        if *depth < 3;

    // Deref links connect parent provenance chains to child roots
    provenance_deref_link(func, dst, child_prov_id, root, parent_prov_id, acc_ofs + offset) <--
        provenance_chain(func, src, root, parent_prov_id, acc_ofs, depth),
        provenance_edge(func, src, dst, ?EdgeType::Deref, offset),
        if *depth < 3,
        let child_prov_id = compute_provenance_id(*func, *dst);

    // Every register in a provenance chain is derived from a pointer root (allocation site or function param) and carries a pointer value.
    relation emit_var_type_candidate(RTLReg, XType);
    emit_var_type_candidate(reg, XType::Xptr) <--
        provenance_chain(_, reg, _, _, _, _);
}

// Unique provenance ID from function address and register
pub fn compute_provenance_id(func: Address, reg: RTLReg) -> u64 {
    let mut hasher = DefaultHasher::new();
    func.hash(&mut hasher);
    reg.hash(&mut hasher);
    hasher.finish()
}

const ALLOC_FUNCTIONS: &[&str] = &[
    "malloc", "calloc", "realloc", "reallocarray", "aligned_alloc",
    "xmalloc", "xcalloc", "xrealloc", "xreallocarray",
    "ximalloc", "xirealloc", "xicalloc", "xireallocarray",
    "xzalloc", "xizalloc", "xcharalloc",
    "xnmalloc", "xinmalloc", "xnrealloc",
    "x2realloc", "x2nrealloc", "xpalloc",
    "imalloc", "irealloc", "icalloc", "ireallocarray",
    "strdup", "strndup", "xstrdup", "xstrndup",
    "xmemdup", "ximemdup", "ximemdup0",
];

pub struct PtrToPass;

impl IRPass for PtrToPass {
    fn name(&self) -> &'static str { "ptr_to" }

    fn run(&self, db: &mut DecompileDB) {
        let alloc_set: HashSet<&str> = ALLOC_FUNCTIONS.iter().copied().collect();

        let call_sites: Vec<(Node, Symbol)> = db
            .rel_iter::<(Node, Symbol)>("call_site")
            .cloned()
            .collect();
        let call_return_regs: Vec<(Node, RTLReg)> = db
            .rel_iter::<(Node, RTLReg)>("call_return_reg")
            .cloned()
            .collect();

        let ret_reg_map: HashMap<Node, RTLReg> = call_return_regs.into_iter().collect();

        for &(node, func_name) in &call_sites {
            if alloc_set.contains(func_name) {
                if let Some(&ret_reg) = ret_reg_map.get(&node) {
                    db.rel_push("allocation_site", (node, ret_reg, 0usize));
                }
            }
        }

        run_pass!(db, PtrToPassProgram);
        emit_provenance_ptr_types(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        static INPUTS: &[&str] = &[
            "rtl_inst", "instr_in_function",
            "emit_function_param_candidate", "allocation_site",
            "call_site", "call_return_reg",
        ];
        INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        static OUTPUTS: &[&str] = &[
            "allocation_site", "emit_var_type_candidate",
            "provenance_root", "provenance_edge",
            "provenance_chain", "provenance_deref_link",
        ];
        OUTPUTS
    }
}

// Emit pointer types for provenance-tracked registers with consistent deref chunks
fn emit_provenance_ptr_types(db: &mut DecompileDB) {
    let chains: Vec<(Address, RTLReg)> = db
        .rel_iter::<(Address, RTLReg, RTLReg, u64, i64, usize)>("provenance_chain")
        .map(|&(func, reg, _, _, _, _)| (func, reg))
        .collect();

    if chains.is_empty() { return; }

    let tracked: HashSet<(Address, RTLReg)> = chains.into_iter().collect();

    let mut reg_deref_chunks: HashMap<RTLReg, Vec<MemoryChunk>> = HashMap::new();

    let instr_func: HashMap<Node, Address> = db
        .rel_iter::<(Node, Address)>("instr_in_function")
        .map(|&(n, f)| (n, f))
        .collect();

    for &(node, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let (chunk, base_reg) = match inst {
            RTLInst::Iload(chunk, Addressing::Aindexed(_), args, _) if !args.is_empty() => {
                (*chunk, args[0])
            }
            RTLInst::Istore(chunk, Addressing::Aindexed(_), args, _) if !args.is_empty() => {
                (*chunk, args[0])
            }
            _ => continue,
        };

        if let Some(&func) = instr_func.get(&node) {
            if tracked.contains(&(func, base_reg)) {
                reg_deref_chunks.entry(base_reg).or_default().push(chunk);
            }
        }
    }

    for (reg, chunks) in &reg_deref_chunks {
        if chunks.is_empty() { continue; }
        let first = chunks[0];
        if !chunks.iter().all(|c| *c == first) { continue; }

        let xtype = match first {
            MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool => XType::Xcharptr,
            MemoryChunk::MInt32 | MemoryChunk::MAny32 => XType::Xintptr,
            MemoryChunk::MFloat64 => XType::Xfloatptr,
            MemoryChunk::MFloat32 => XType::Xsingleptr,
            _ => continue,
        };
        db.rel_push("emit_var_type_candidate", (*reg, xtype));
    }
}
