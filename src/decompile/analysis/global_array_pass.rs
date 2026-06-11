

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
use crate::{declare_io_from, run_pass};

use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent_par;

// Global array detection: identifies arrays from repeated constant-offset accesses to global symbols
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct GlobalArrayPassProgram;

    relation rtl_inst(Node, RTLInst);
    relation symbols(Address, Symbol, Symbol);
    relation base_ident_to_symbol(Ident, Symbol);
    relation symbol_size(Address, usize, Symbol);
    relation instr_in_function(Node, Address);

    relation global_addr_access(Ident, i64, Node, MemoryChunk);

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aglobal(ident, offset), _, _));

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aglobal(ident, offset), _, _));

    global_addr_access(ident, 0, node, MemoryChunk::MAny64) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oindirectsymbol(ident), _, _));

    global_addr_access(ident, offset, node, MemoryChunk::MAny64) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aglobal(ident, offset)), _, _));

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Abasedscaled(_scale, ident, offset), _, _));

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Abasedscaled(_scale, ident, offset), _, _));

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Abased(ident, offset), _, _));

    global_addr_access(ident, offset, node, chunk) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Abased(ident, offset), _, _));

    relation symbol_address(Ident, Address);

    symbol_address(ident, addr) <--
        symbols(addr, sym_name, _sym_type),
        base_ident_to_symbol(ident, name),
        if *sym_name == *name;

    // Only coalesce when symbol_size is known; no 64KiB fallback (it folded unrelated globals).
    relation base_effective_bound(Ident, i64);

    base_effective_bound(ident, *size as i64) <--
        symbol_address(ident, addr),
        symbol_size(addr, size, _),
        if *size > 0;

    relation base_coalesce_limit(Ident, i64);

    base_coalesce_limit(ident, limit) <--
        base_effective_bound(ident, _),
        agg limit = min_i64(bound) in base_effective_bound(ident, bound);

    // Coalesce nearby symbols into the same array when within the base symbol's bounds
    relation array_coalesce_candidate(Ident, Ident, i64);

    array_coalesce_candidate(base_ident, member_ident, offset) <--
        symbol_address(base_ident, base_addr),
        symbol_address(member_ident, member_addr),
        if *member_addr > *base_addr,
        let offset = (*member_addr as i64) - (*base_addr as i64),
        base_coalesce_limit(base_ident, limit),
        if offset < *limit,
        global_addr_access(member_ident, _, _, _),
        global_addr_access(base_ident, _, _, _);

    relation accessed_global(Ident);

    accessed_global(ident) <--
        global_addr_access(ident, _, _, _);

    relation symbol_bounds(Address, Address);

    symbol_bounds(start_addr, end_addr) <--
        symbol_size(start_addr, size, _name),
        if *size > 0,
        let end_addr = *start_addr + (*size as u64);

    // Interior symbol detection: accessed symbol falls within a sized symbol's range
    relation address_in_sized_symbol(Ident, Address, i64);

    address_in_sized_symbol(accessed_ident, start_addr, offset) <--
        global_addr_access(accessed_ident, _, _, _),
        symbol_address(accessed_ident, accessed_addr),
        symbol_bounds(start_addr, end_addr),
        if *accessed_addr > *start_addr && *accessed_addr < *end_addr,
        let offset = (*accessed_addr - *start_addr) as i64;

    relation interior_to_base_ident(Ident, Ident, i64);

    interior_to_base_ident(interior_ident, base_ident, offset) <--
        address_in_sized_symbol(interior_ident, start_addr, offset),
        symbol_address(base_ident, start_addr);

    relation global_distinct_offset(Ident, i64);

    global_distinct_offset(ident, offset) <--
        global_addr_access(ident, offset, _, _);

    global_distinct_offset(base_ident, combined_offset) <--
        array_coalesce_candidate(base_ident, member_ident, member_offset),
        global_addr_access(member_ident, local_offset, _, _),
        let combined_offset = member_offset + local_offset;

    global_distinct_offset(base_ident, offset) <--
        interior_to_base_ident(_interior_ident, base_ident, offset);

    global_distinct_offset(base_ident, 0) <--
        interior_to_base_ident(_interior_ident, base_ident, _offset);

    relation interior_offset(Ident, i64);

    interior_offset(base_ident, 0) <--
        interior_to_base_ident(_interior_ident, base_ident, _offset);

    interior_offset(base_ident, offset) <--
        interior_to_base_ident(_interior_ident, base_ident, offset);

    // Interior offsets must be multiples of the element size, so GCD over them is the validated stride; the former {1,2,4,8} whitelist on pairwise diffs wrongly rejected legitimate strides like 3, 5, 12.
    relation interior_stride(Ident, i64);

    interior_stride(ident, ofs) <--
        interior_offset(ident, ofs),
        if *ofs > 0;

    relation interior_element_size(Ident, usize);

    interior_element_size(ident, elem_size) <--
        interior_stride(ident, _),
        agg elem_size = gcd_aggregator(stride) in interior_stride(ident, stride),
        if elem_size > 1;

    // SR-1/SR-3: a candidate stride s is rejected if any access crosses an element boundary, any two loads at the same intra-offset disagree on width, s is not a multiple of every SIB scale or widest load, walk increment is not a whole-element multiple, or not all touched elements expose the same intra-offset set; smallest passing stride wins (weakest consistent claim).

    // Per-function def sites of RTL registers (single-def/walker guards are structural value-set arguments, NOT order/proximity reasoning).
    #[local] relation rtl_reg_def(Address, RTLReg, Node);
    rtl_reg_def(*func, *dst, *node) <--
        rtl_inst(node, ?RTLInst::Iop(_, _, dst)),
        instr_in_function(node, func);
    rtl_reg_def(*func, *dst, *node) <--
        rtl_inst(node, ?RTLInst::Iload(_, _, _, dst)),
        instr_in_function(node, func);
    rtl_reg_def(*func, *dst, *node) <--
        rtl_inst(node, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        instr_in_function(node, func);
    rtl_reg_def(*func, *dst, *node) <--
        rtl_inst(node, ?RTLInst::Ibuiltin(_, _, BuiltinArg::BA(dst))),
        instr_in_function(node, func);

    #[local] relation rtl_reg_def_count(Address, RTLReg, usize);
    rtl_reg_def_count(func, reg, n) <--
        rtl_reg_def(func, reg, _),
        agg n = count_items(node) in rtl_reg_def(func, reg, node);

    // A register whose ONLY def is the symbol-address materialization (PIE/RIP-relative `lea sym(%rip),%r`) provably holds &sym+ofs at every use.
    #[local] relation global_base_reg(Address, RTLReg, Ident, i64);
    global_base_reg(*func, *dst, *ident, 0) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oindirectsymbol(ident), _, dst)),
        instr_in_function(node, func),
        rtl_reg_def_count(func, dst, n),
        if *n == 1;
    global_base_reg(*func, *dst, *ident, *ofs) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aglobal(ident, ofs)), _, dst)),
        instr_in_function(node, func),
        rtl_reg_def_count(func, dst, n),
        if *n == 1;
    global_base_reg(*func, *dst, *ident, *ofs) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Aglobal(ident, ofs)), _, dst)),
        instr_in_function(node, func),
        rtl_reg_def_count(func, dst, n),
        if *n == 1;

    // Strength-reduced array walker: exactly one symbol-address init plus self-increments by a single constant K -- value set is {&sym+ofs+n*K} on every path, so derefs are array accesses and K is a stride multiple.
    #[local] relation walker_init(Address, RTLReg, Ident, i64, Node);
    walker_init(*func, *dst, *ident, 0, *node) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oindirectsymbol(ident), _, dst)),
        instr_in_function(node, func);
    walker_init(*func, *dst, *ident, *ofs, *node) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aglobal(ident, ofs)), _, dst)),
        instr_in_function(node, func);

    #[local] relation walker_incr(Address, RTLReg, i64, Node);
    walker_incr(*func, *dst, *k, *node) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oaddlimm(k), args, dst)),
        if args.len() == 1 && args[0] == *dst,
        if *k != 0,
        instr_in_function(node, func);
    walker_incr(*func, *dst, *k, *node) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Aindexed(k)), args, dst)),
        if args.len() == 1 && args[0] == *dst,
        if *k != 0,
        instr_in_function(node, func);

    #[local] relation walker_init_node(Address, RTLReg, Node);
    walker_init_node(func, reg, node) <-- walker_init(func, reg, _, _, node);
    #[local] relation walker_init_count(Address, RTLReg, usize);
    walker_init_count(func, reg, n) <--
        walker_init_node(func, reg, _),
        agg n = count_items(node) in walker_init_node(func, reg, node);

    #[local] relation walker_incr_node(Address, RTLReg, Node);
    walker_incr_node(func, reg, node) <-- walker_incr(func, reg, _, node);
    #[local] relation walker_incr_node_count(Address, RTLReg, usize);
    walker_incr_node_count(func, reg, n) <--
        walker_incr_node(func, reg, _),
        agg n = count_items(node) in walker_incr_node(func, reg, node);

    #[local] relation walker_k(Address, RTLReg, i64);
    walker_k(func, reg, k) <-- walker_incr(func, reg, k, _);
    #[local] relation walker_k_count(Address, RTLReg, usize);
    walker_k_count(func, reg, n) <--
        walker_k(func, reg, _),
        agg n = count_items(k) in walker_k(func, reg, k);

    #[local] relation global_walker(Address, RTLReg, Ident, i64, i64);
    global_walker(*func, *reg, *ident, *base_ofs, k.abs()) <--
        walker_init(func, reg, ident, base_ofs, _),
        walker_init_count(func, reg, ic), if *ic == 1,
        walker_k(func, reg, k),
        walker_k_count(func, reg, kc), if *kc == 1,
        walker_incr_node_count(func, reg, mc),
        rtl_reg_def_count(func, reg, n),
        if *n == 1 + *mc;

    // Register-keyed access projections so bridged rules join on (func, base_reg) instead of filtering a cartesian product.
    #[local] relation reg_scaled_access(Address, RTLReg, i64, i64, MemoryChunk, bool);
    reg_scaled_access(*func, args[0], *sc, *ofs, *chunk, true) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed2scaled(sc, ofs), args, _)),
        if args.len() >= 1,
        instr_in_function(node, func);
    reg_scaled_access(*func, args[0], *sc, *ofs, *chunk, false) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed2scaled(sc, ofs), args, _)),
        if args.len() >= 1,
        instr_in_function(node, func);

    // Aindexed2 (reg+reg): the symbol register can sit in either operand slot, so both are projected.
    #[local] relation reg_pair_access(Address, RTLReg, i64, MemoryChunk, bool);
    reg_pair_access(*func, args[0], *ofs, *chunk, true) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed2(ofs), args, _)),
        if args.len() >= 2,
        instr_in_function(node, func);
    reg_pair_access(*func, args[1], *ofs, *chunk, true) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed2(ofs), args, _)),
        if args.len() >= 2,
        instr_in_function(node, func);
    reg_pair_access(*func, args[0], *ofs, *chunk, false) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed2(ofs), args, _)),
        if args.len() >= 2,
        instr_in_function(node, func);
    reg_pair_access(*func, args[1], *ofs, *chunk, false) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed2(ofs), args, _)),
        if args.len() >= 2,
        instr_in_function(node, func);

    #[local] relation reg_plain_access(Address, RTLReg, i64, MemoryChunk, bool);
    reg_plain_access(*func, args[0], *ofs, *chunk, true) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed(ofs), args, _)),
        if args.len() == 1,
        instr_in_function(node, func);
    reg_plain_access(*func, args[0], *ofs, *chunk, false) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed(ofs), args, _)),
        if args.len() == 1,
        instr_in_function(node, func);

    // Unified access evidence: (ident, byte offset from symbol, chunk, is_load, var_indexed).
    relation global_access_ev(Ident, i64, MemoryChunk, bool, bool);

    // Constant-offset accesses on the symbol itself.
    global_access_ev(*ident, *ofs, *chunk, true, false) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(ident, ofs), _, _));
    global_access_ev(*ident, *ofs, *chunk, false, false) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Aglobal(ident, ofs), _, _));

    // Variable-indexed accesses, absolute SIB forms (non-PIE).
    global_access_ev(*ident, *ofs, *chunk, true, true) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Abasedscaled(_, ident, ofs), _, _));
    global_access_ev(*ident, *ofs, *chunk, false, true) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Abasedscaled(_, ident, ofs), _, _));
    global_access_ev(*ident, *ofs, *chunk, true, true) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Abased(ident, ofs), _, _));
    global_access_ev(*ident, *ofs, *chunk, false, true) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Abased(ident, ofs), _, _));

    // Bridged: scaled/indexed access through a single-def symbol-address register.
    global_access_ev(*ident, lea_ofs + ofs, *chunk, *is_load, true) <--
        global_base_reg(func, base, ident, lea_ofs),
        reg_scaled_access(func, base, _, ofs, chunk, is_load);
    global_access_ev(*ident, lea_ofs + ofs, *chunk, *is_load, true) <--
        global_base_reg(func, base, ident, lea_ofs),
        reg_pair_access(func, base, ofs, chunk, is_load);
    // Bridged constant-offset deref through the single-def symbol register.
    global_access_ev(*ident, lea_ofs + ofs, *chunk, *is_load, false) <--
        global_base_reg(func, base, ident, lea_ofs),
        reg_plain_access(func, base, ofs, chunk, is_load);
    // Walker derefs (variable by construction: the walker visits successive elements).
    global_access_ev(*ident, base_ofs + ofs, *chunk, *is_load, true) <--
        global_walker(func, reg, ident, base_ofs, _),
        reg_plain_access(func, reg, ofs, chunk, is_load);

    // Fold interior-symbol and coalesced-member accesses onto the base (rebased to its offset space) so validation sees every access.
    global_access_ev(*base, int_ofs + ofs, *chunk, *is_load, *is_var) <--
        interior_to_base_ident(int_id, base, int_ofs),
        global_access_ev(int_id, ofs, chunk, is_load, is_var);
    global_access_ev(*base, member_ofs + ofs, *chunk, *is_load, *is_var) <--
        array_coalesce_candidate(base, member, member_ofs),
        global_access_ev(member, ofs, chunk, is_load, is_var);

    #[local] relation ev_has_var(Ident);
    ev_has_var(ident) <-- global_access_ev(ident, _, _, _, true);

    // SIB scales observed for the ident (element boundaries land on multiples).
    #[local] relation global_scale_hint(Ident, i64);
    global_scale_hint(*ident, *sc) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Abasedscaled(sc, ident, _), _, _)),
        if *sc >= 2;
    global_scale_hint(*ident, *sc) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Abasedscaled(sc, ident, _), _, _)),
        if *sc >= 2;
    global_scale_hint(*ident, *sc) <--
        global_base_reg(func, base, ident, _),
        reg_scaled_access(func, base, sc, _, _, _),
        if *sc >= 2;

    #[local] relation global_walk_stride(Ident, i64);
    global_walk_stride(ident, k) <-- global_walker(_, _, ident, _, k);

    // ---- candidate stride generation (bounded; validation prunes) ----
    #[local] relation ev_offset(Ident, i64);
    ev_offset(ident, ofs) <-- global_access_ev(ident, ofs, _, _, _);

    #[local] relation ev_min(Ident, i64);
    ev_min(ident, m) <--
        ev_offset(ident, _),
        agg m = min_i64(o) in ev_offset(ident, o);

    #[local] relation ev_diff(Ident, i64);
    ev_diff(ident, ofs - m) <--
        ev_offset(ident, ofs),
        ev_min(ident, m),
        if ofs > m;

    #[local] relation ev_gcd(Ident, i64);
    ev_gcd(ident, g as i64) <--
        ev_diff(ident, _),
        agg g = gcd_aggregator(d) in ev_diff(ident, d),
        if g > 0;

    #[local] relation ev_end(Ident, i64);
    ev_end(ident, ofs + (chunk_byte_size(chunk) as i64)) <--
        global_access_ev(ident, ofs, chunk, _, _);
    #[local] relation ev_max_end(Ident, i64);
    ev_max_end(ident, e) <--
        ev_end(ident, _),
        agg e = max_i64(x) in ev_end(ident, x);

    #[local] relation ev_load_width(Ident, i64);
    ev_load_width(ident, chunk_byte_size(chunk) as i64) <--
        global_access_ev(ident, _, chunk, true, _);
    #[local] relation ev_max_load_width(Ident, i64);
    ev_max_load_width(ident, w) <--
        ev_load_width(ident, _),
        agg w = max_i64(x) in ev_load_width(ident, x);

    #[local] relation stride_cand(Ident, i64);
    // GCD of offset diffs plus small multiples covers composite strides (e.g. 12 = 3*4 where SIB only exposes factor 4), bounded by span.
    stride_cand(ident, g) <-- ev_gcd(ident, g);
    stride_cand(ident, k * g) <--
        ev_gcd(ident, g),
        ev_max_end(ident, e),
        for k in 2i64..=8i64,
        if k * g <= *e;
    // observed SIB scales and walker increments are direct stride evidence
    stride_cand(ident, sc) <-- global_scale_hint(ident, sc);
    stride_cand(ident, k) <-- global_walk_stride(ident, k), if *k > 0;
    // single-element span (max access end), raw and rounded up to the field alignment
    stride_cand(ident, e) <-- ev_max_end(ident, e), if *e > 0;
    stride_cand(ident, ((e + w - 1) / w) * w) <--
        ev_max_end(ident, e),
        ev_max_load_width(ident, w),
        if *w > 0 && *e > 0;

    // ---- validation: reject candidates contradicted by any access ----
    #[local] relation cand_intra(Ident, i64, i64, MemoryChunk, bool);
    cand_intra(*ident, *s, ofs.rem_euclid(*s), *chunk, *is_load) <--
        stride_cand(ident, s),
        if *s > 0,
        global_access_ev(ident, ofs, chunk, is_load, _);

    #[local] relation stride_bad(Ident, i64);
    // fit: an access must not cross its element boundary
    stride_bad(ident, s) <--
        cand_intra(ident, s, x, c, _),
        if *x + (chunk_byte_size(c) as i64) > *s;
    // load-width consistency per intra offset (element field types are fixed)
    stride_bad(ident, s) <--
        cand_intra(ident, s, x, c1, true),
        cand_intra(ident, s, x, c2, true),
        if chunk_byte_size(c1) != chunk_byte_size(c2);
    // SIB scale: index*scale must land on element boundaries
    stride_bad(ident, s) <--
        stride_cand(ident, s),
        if *s > 0,
        global_scale_hint(ident, sc),
        if *s % *sc != 0;
    // pointer-walk increment is a whole number of elements
    stride_bad(ident, s) <--
        stride_cand(ident, s),
        if *s > 0,
        global_walk_stride(ident, k),
        if *k % *s != 0;
    // element size is a multiple of its widest (loaded) field: C natural alignment
    stride_bad(ident, s) <--
        stride_cand(ident, s),
        if *s > 0,
        ev_max_load_width(ident, w),
        if *w > 0 && *s % *w != 0;
    // pattern: every touched element exposes the same intra-offset set
    #[local] relation patt_row(Ident, i64, i64, i64);
    patt_row(*ident, *s, ofs.div_euclid(*s), ofs.rem_euclid(*s)) <--
        stride_cand(ident, s),
        if *s > 0,
        global_access_ev(ident, ofs, _, _, true);
    patt_row(*ident, *s, ofs.div_euclid(*s), ofs.rem_euclid(*s)) <--
        stride_cand(ident, s),
        if *s > 0,
        global_access_ev(ident, ofs, _, _, false),
        !ev_has_var(ident);
    #[local] relation patt_k(Ident, i64, i64);
    patt_k(ident, s, k) <-- patt_row(ident, s, k, _);
    stride_bad(ident, s) <--
        patt_row(ident, s, k1, x),
        patt_k(ident, s, k2),
        if k1 != k2,
        !patt_row(ident, s, k2, x);

    #[local] relation stride_ok(Ident, i64);
    stride_ok(ident, s) <--
        stride_cand(ident, s),
        if *s > 0,
        !stride_bad(ident, s);

    // Smallest validated stride: weakest consistent claim.
    relation inferred_element_size(Ident, usize);

    inferred_element_size(ident, s as usize) <--
        stride_ok(ident, _),
        agg s = min_i64(v) in stride_ok(ident, v);

    relation array_offset_count(Ident, usize);

    array_offset_count(ident, count) <--
        global_distinct_offset(ident, _),
        agg count = count_items(ofs) in global_distinct_offset(ident, ofs);

    relation array_min_offset(Ident, i64);

    array_min_offset(ident, min_ofs) <--
        global_distinct_offset(ident, _),
        agg min_ofs = min_i64(ofs) in global_distinct_offset(ident, ofs);

    relation array_max_offset(Ident, i64);

    array_max_offset(ident, max_ofs) <--
        global_distinct_offset(ident, _),
        agg max_ofs = max_i64(ofs) in global_distinct_offset(ident, ofs);

    // Element count: prefer symbol size (array fills its symbol) over observed access extent.
    #[local] relation array_count_cand(Ident, usize);

    array_count_cand(ident, ((*max_ofs as usize) / elem_size) + 1) <--
        inferred_element_size(ident, elem_size),
        if *elem_size > 0,
        array_max_offset(ident, max_ofs),
        if *max_ofs >= 0;
    array_count_cand(ident, size / elem_size) <--
        inferred_element_size(ident, elem_size),
        if *elem_size > 0,
        symbol_address(ident, addr),
        symbol_size(addr, size, _),
        if *size >= *elem_size;

    #[local] relation array_count(Ident, usize);
    array_count(ident, c) <--
        array_count_cand(ident, _),
        agg c = max_usize(x) in array_count_cand(ident, x);

    // SR-1: constant route requires 3+ distinct offsets spanning >= 2 elements (2 alone could be a struct or adjacency); variable-index route (scaled/walked access) suffices alone to admit short arrays; interior-symbol idents never claim their own array -- their accesses fold onto the base.
    relation is_global_array(Ident, usize, usize);

    is_global_array(ident, elem_size, count) <--
        inferred_element_size(ident, elem_size),
        if *elem_size > 0,
        array_offset_count(ident, ofs_count),
        if *ofs_count >= 3,
        array_max_offset(ident, max_ofs),
        if *max_ofs >= (*elem_size as i64),
        array_min_offset(ident, min_ofs),
        if *min_ofs >= 0,
        array_count(ident, count),
        !address_in_sized_symbol(ident, _, _);

    is_global_array(ident, elem_size, count) <--
        inferred_element_size(ident, elem_size),
        if *elem_size > 0,
        ev_has_var(ident),
        array_min_offset(ident, min_ofs),
        if *min_ofs >= 0,
        array_count(ident, count),
        !address_in_sized_symbol(ident, _, _);

    relation emit_address_as_offset(Ident, Symbol, i64);

    emit_address_as_offset(interior_ident, *name, offset) <--
        interior_to_base_ident(interior_ident, base_ident, offset),
        symbol_address(base_ident, base_addr),
        symbol_size(base_addr, _size, name);

}

pub struct GlobalArrayPass;

impl IRPass for GlobalArrayPass {
    fn name(&self) -> &'static str { "global_array" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, GlobalArrayPassProgram);

        // Diagnostic hook (env-gated, like CF4_TRACE) for array/stride-recovery work.
        if std::env::var("GA_DUMP").is_ok() {
            for t in db.rel_iter::<(Ident, i64, MemoryChunk, bool, bool)>("global_access_ev") {
                eprintln!("[GA] global_access_ev {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, Ident, i64)>("interior_to_base_ident") {
                eprintln!("[GA] interior_to_base_ident {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, i64)>("global_distinct_offset") {
                eprintln!("[GA] global_distinct_offset {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, usize)>("inferred_element_size") {
                eprintln!("[GA] inferred_element_size {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, usize)>("interior_element_size") {
                eprintln!("[GA] interior_element_size {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, usize, usize)>("is_global_array") {
                eprintln!("[GA] is_global_array {:x?}", t);
            }
        }
    }

    declare_io_from!(GlobalArrayPassProgram);
}


pub fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a.abs()
    } else {
        gcd(b, a % b)
    }
}

pub(crate) fn gcd_aggregator<'a>(
    inp: impl Iterator<Item = (&'a i64,)>,
) -> impl Iterator<Item = usize> {
    let strides: Vec<i64> = inp.map(|(s,)| *s).collect();
    if strides.is_empty() {
        return None.into_iter();
    }
    let mut result = strides[0].abs();
    for &s in &strides[1..] {
        result = gcd(result, s.abs());
    }
    Some(result as usize).into_iter()
}

pub(crate) fn count_items<'a, T: 'a>(inp: impl Iterator<Item = (&'a T,)>) -> impl Iterator<Item = usize> {
    std::iter::once(inp.count())
}

pub(crate) fn max_i64<'a>(inp: impl Iterator<Item = (&'a i64,)>) -> impl Iterator<Item = i64> {
    inp.map(|(v,)| *v).max().into_iter()
}

pub(crate) fn max_usize<'a>(inp: impl Iterator<Item = (&'a usize,)>) -> impl Iterator<Item = usize> {
    inp.map(|(v,)| *v).max().into_iter()
}

pub(crate) fn min_i64<'a>(inp: impl Iterator<Item = (&'a i64,)>) -> impl Iterator<Item = i64> {
    inp.map(|(v,)| *v).min().into_iter()
}
