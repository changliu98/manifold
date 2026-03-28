

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
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

    // Use symbol_size when known, otherwise 65536 heuristic
    relation base_effective_bound(Ident, i64);

    base_effective_bound(ident, *size as i64) <--
        symbol_address(ident, addr),
        symbol_size(addr, size, _),
        if *size > 0;

    base_effective_bound(ident, 65536) <--
        accessed_global(ident);

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

    // GCD of interior offsets gives element size
    relation interior_stride(Ident, i64);

    interior_stride(ident, stride) <--
        interior_offset(ident, ofs1),
        interior_offset(ident, ofs2),
        if *ofs2 > *ofs1,
        let stride = *ofs2 - *ofs1,
        if is_valid_element_size(stride as usize);

    relation interior_element_size(Ident, usize);

    interior_element_size(ident, elem_size) <--
        interior_stride(ident, _),
        agg elem_size = gcd_aggregator(stride) in interior_stride(ident, stride),
        if elem_size > 1;

    // GCD of access offset strides gives array element size
    relation array_stride(Ident, i64);

    array_stride(ident, stride) <--
        global_distinct_offset(ident, ofs1),
        global_distinct_offset(ident, ofs2),
        if *ofs2 > *ofs1,
        let stride = *ofs2 - *ofs1,
        if is_valid_element_size(stride as usize);

    relation inferred_element_size(Ident, usize);

    inferred_element_size(ident, elem_size) <--
        array_stride(ident, _),
        agg elem_size = gcd_aggregator(stride) in array_stride(ident, stride),
        if elem_size > 0;

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

    // Array confirmed: 2+ offsets with consistent stride and non-negative base
    relation is_global_array(Ident, usize, usize);

    is_global_array(ident, elem_size, count) <--
        inferred_element_size(ident, elem_size),
        array_offset_count(ident, ofs_count),
        if *ofs_count >= 2,
        array_max_offset(ident, max_ofs),
        array_min_offset(ident, min_ofs),
        if *min_ofs >= 0,
        let count = ((*max_ofs as usize) / elem_size) + 1;

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
    }

    declare_io_from!(GlobalArrayPassProgram);
}


pub fn is_valid_element_size(size: usize) -> bool {
    matches!(size, 1 | 2 | 4 | 8)
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

pub(crate) fn min_i64<'a>(inp: impl Iterator<Item = (&'a i64,)>) -> impl Iterator<Item = i64> {
    inp.map(|(v,)| *v).min().into_iter()
}
