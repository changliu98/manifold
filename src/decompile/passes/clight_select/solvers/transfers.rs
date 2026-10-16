//! Decoder-owned value transfers, independent of recovered storage targets.
//!
//! A load-transport proof preserves the fetched word through C conversion.
//! It deliberately makes no address, aliasing, initialization or lifetime claim.
use crate::decompile::passes::clight_select::syntax::{ArtifactKey, Artifacts};
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::{solvers::integer_semantics::{CopyValue, LoadValue}, query::FunctionData};
use crate::mreg::Mreg;
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) const LOADS: ArtifactKey<BTreeMap<Node, LoadValue>> =
    ArtifactKey::projected("load-transfers", |loads, plan| {
        let mut result = loads.clone();
        for load in result.values_mut() {
            load.destination = plan.write(load.node, load.destination);
        }
        result
    });
pub(crate) const COPIES: ArtifactKey<BTreeMap<Node, CopyValue>> =
    ArtifactKey::projected("copy-transfers", |copies, plan| {
        let mut result = copies.clone();
        for copy in result.values_mut() {
            copy.source = plan.read(copy.node, copy.source);
            copy.destination = plan.write(copy.node, copy.destination);
        }
        result
    });
const INPUT_VIEWS: ArtifactKey<Vec<(Node, RTLReg, u32, bool)>> =
    ArtifactKey::projected("frame-input-views", |views, plan| {
        views
            .iter()
            .map(|&(n, r, bits, sign)| (n, plan.read(n, r), bits, sign))
            .collect()
    });
pub(super) const INPUTS: &[&str] = &[
    "rtl_inst",
    "ltl_inst",
    "instr_in_function",
    "instruction",
    "machine_register_write_view",
    "machine_load_extension",
    "type_storage_access",
];

/// Reversing a scalar frame transfer must retain its access width even if a
/// later declaration uses a wider carrier. These casts encode decoder facts,
/// not preferred source types. Preserve every candidate and its world index.
pub(super) fn project_frame_views(function: &mut FunctionData) {
    fn read_view(expr: &mut ClightExpr, source: RTLReg, ty: &ClightType) {
        match expr {
            ClightExpr::Etempvar(reg, _) if *reg as RTLReg == source => {
                *expr = ClightExpr::Ecast(Box::new(expr.clone()), ty.clone());
            }
            ClightExpr::Ecast(inner, existing)
                if existing == ty
                    && matches!(inner.as_ref(), ClightExpr::Etempvar(reg, _) if *reg as RTLReg == source) =>
                {}
            ClightExpr::Ecast(inner, _) | ClightExpr::Eunop(_, inner, _) => {
                read_view(inner, source, ty)
            }
            ClightExpr::Ebinop(_, a, b, _) => {
                read_view(a, source, ty);
                read_view(b, source, ty);
            }
            ClightExpr::Econdition(c, a, b, _) => {
                read_view(c, source, ty);
                read_view(a, source, ty);
                read_view(b, source, ty);
            }
            _ => {} // Do not rewrite an address or another memory access.
        }
    }
    fn inlined_read(statement: &mut ClightStmt, source: RTLReg, ty: &ClightType) {
        match statement {
            ClightStmt::Sifthenelse(condition, _, _) | ClightStmt::Sswitch(condition, _) => {
                read_view(condition, source, ty)
            }
            ClightStmt::Sreturn(Some(expr)) | ClightStmt::Sset(_, expr) => {
                read_view(expr, source, ty)
            }
            ClightStmt::Scall(_, _, args) => {
                for arg in args {
                    read_view(arg, source, ty);
                }
            }
            ClightStmt::Slabel(_, body) | ClightStmt::Seffect(_, body) => {
                inlined_read(body, source, ty)
            }
            ClightStmt::Ssequence(items) if items.len() == 1 => {
                inlined_read(&mut items[0], source, ty)
            }
            _ => {}
        }
    }
    fn cast(statement: &mut ClightStmt, destination: RTLReg, bits: u32, signed: bool) {
        match statement {
            ClightStmt::Sset(dst, rhs) if *dst as RTLReg == destination => {
                let size = match bits {
                    8 => ClightIntSize::I8,
                    16 => ClightIntSize::I16,
                    _ => return,
                };
                let ty = ClightType::Tint(
                    size,
                    if signed {
                        ClightSignedness::Signed
                    } else {
                        ClightSignedness::Unsigned
                    },
                    ClightAttr::default(),
                );
                if !matches!(rhs, ClightExpr::Ecast(_, existing) if *existing == ty) {
                    *rhs = ClightExpr::Ecast(Box::new(rhs.clone()), ty);
                }
            }
            ClightStmt::Slabel(_, body) | ClightStmt::Seffect(_, body) => {
                cast(body, destination, bits, signed)
            }
            ClightStmt::Ssequence(items) if items.len() == 1 => {
                cast(&mut items[0], destination, bits, signed)
            }
            _ => {}
        }
    }
    let Some(copies) = COPIES.get(&function.analysis_facts) else {
        return;
    };
    for copy in copies.values() {
        if [copy.source, copy.destination].iter().any(|reg| {
            function
                .var_type_candidates
                .get(reg)
                .into_iter()
                .flatten()
                .chain(function.var_types.get(reg))
                .any(|ty| ty.is_float())
        }) {
            continue; // Numeric casts cannot implement floating bit transport.
        }
        if function
            .storage_writes
            .iter()
            .any(|w| w.root == copy.destination || w.locals.contains(&copy.destination))
        {
            continue;
        }
        let view = if copy.storage {
            Some((copy.bits, false))
        } else {
            copy.memory_input
        };
        let Some((bits @ (8 | 16), signed)) = view else {
            continue;
        };
        for statement in function
            .node_statements
            .get_mut(&copy.node)
            .into_iter()
            .flatten()
        {
            cast(statement, copy.destination, bits, signed);
            if !copy.storage {
                let size = if bits == 8 {
                    ClightIntSize::I8
                } else {
                    ClightIntSize::I16
                };
                let ty = ClightType::Tint(
                    size,
                    if signed {
                        ClightSignedness::Signed
                    } else {
                        ClightSignedness::Unsigned
                    },
                    ClightAttr::default(),
                );
                // A folded load may survive only inside its consumer's
                // predicate/argument. Preserve its source access view too.
                inlined_read(statement, copy.source, &ty);
            }
        }
    }
    for &(node, source, bits, signed) in INPUT_VIEWS
        .get(&function.analysis_facts)
        .into_iter()
        .flatten()
    {
        if function
            .var_type_candidates
            .get(&source)
            .into_iter()
            .flatten()
            .chain(function.var_types.get(&source))
            .any(|ty| ty.is_float())
        {
            continue;
        }
        let size = match bits {
            8 => ClightIntSize::I8,
            16 => ClightIntSize::I16,
            _ => continue,
        };
        let ty = ClightType::Tint(
            size,
            if signed {
                ClightSignedness::Signed
            } else {
                ClightSignedness::Unsigned
            },
            ClightAttr::default(),
        );
        for statement in function
            .node_statements
            .get_mut(&node)
            .into_iter()
            .flatten()
        {
            inlined_read(statement, source, &ty);
        }
    }
}

pub(super) fn collect(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut instructions = BTreeMap::<Node, Option<RTLInst>>::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        instructions
            .entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut destinations = BTreeMap::<Node, BTreeSet<Mreg>>::new();
    let mut memory_nodes = BTreeSet::new();
    for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
        if matches!(inst, LTLInst::Lload(..) | LTLInst::Lgetstack(..)) {
            memory_nodes.insert(*node);
        }
        if let LTLInst::Lload(_, _, _, dst)
        | LTLInst::Lgetstack(_, _, _, dst)
        | LTLInst::Lop(_, _, dst) = inst
        {
            destinations.entry(*node).or_default().insert(*dst);
        }
    }
    let mut widths = BTreeMap::<(Node, Mreg), BTreeSet<u32>>::new();
    for &(node, reg, bits) in db.rel_iter::<(Node, Mreg, u32)>("machine_register_write_view") {
        widths.entry((node, reg)).or_default().insert(bits);
    }
    let mut extensions = BTreeMap::<Node, BTreeSet<(u32, u32, bool)>>::new();
    for &(node, input, output, signed) in
        db.rel_iter::<(Node, u32, u32, bool)>("machine_load_extension")
    {
        extensions
            .entry(node)
            .or_default()
            .insert((input, output, signed));
    }
    let mut mnemonics = BTreeMap::<Node, BTreeSet<Symbol>>::new();
    for row in db.rel_iter::<(
        Address,
        usize,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        usize,
        usize,
    )>("instruction")
    {
        mnemonics.entry(row.0).or_default().insert(row.3);
    }
    let mut stores = BTreeMap::<(Address, Node, RTLReg), BTreeSet<u32>>::new();
    let mut reads = BTreeMap::<(Address, Node, RTLReg), BTreeSet<MemoryChunk>>::new();
    for &(function, node, reg, _, write, chunk) in
        db.rel_iter::<(Address, Node, RTLReg, i64, bool, MemoryChunk)>("type_storage_access")
    {
        if write {
            let bits = (crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(&chunk)
                * 8) as u32;
            stores
                .entry((function, node, reg))
                .or_default()
                .insert(bits);
        } else {
            reads
                .entry((function, node, reg))
                .or_default()
                .insert(chunk);
        }
    }
    let mut by_function = BTreeMap::<Address, BTreeMap<Node, LoadValue>>::new();
    let mut copies = BTreeMap::<Address, BTreeMap<Node, CopyValue>>::new();
    for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        let Some(Some(inst)) = instructions.get(&node) else {
            continue;
        };
        let write_bits = destinations
            .get(&node)
            .filter(|r| r.len() == 1)
            .and_then(|r| r.first())
            .and_then(|reg| widths.get(&(node, *reg)))
            .filter(|w| w.len() == 1)
            .and_then(|w| w.first())
            .copied();
        let signed_word_load = mnemonics
            .get(&node)
            .filter(|m| m.len() == 1)
            .and_then(|m| m.first())
            .is_some_and(|m| matches!(*m, "MOVSX" | "MOVSXD"));
        if let RTLInst::Iop(crate::x86::op::Operation::Omove, args, destination) = inst {
            if args.len() == 1 {
                let storage = stores.get(&(function, node, *destination));
                let bits = if let Some(widths) = storage {
                    (widths.len() == 1).then(|| *widths.first().unwrap())
                } else {
                    write_bits
                };
                if let Some(bits @ (8 | 16 | 32 | 64)) = bits {
                    let memory_input = if memory_nodes.contains(&node) {
                        let Some(chunks) = reads.get(&(function, node, args[0])) else {
                            continue;
                        };
                        let Some(&(input, output, signed)) = extensions
                            .get(&node)
                            .filter(|e| e.len() == 1)
                            .and_then(|e| e.first())
                        else {
                            continue;
                        };
                        // A storage view contributes width only. Extension is
                        // owned by the decoded load, including MOVSX byte/word.
                        if output != bits
                            || chunks.is_empty()
                            || chunks.iter().any(|c| integer_bits(*c) != Some(input))
                        {
                            continue;
                        }
                        Some((input, signed))
                    } else {
                        None
                    };
                    copies.entry(function).or_default().insert(
                        node,
                        CopyValue {
                            node,
                            source: args[0],
                            destination: *destination,
                            bits,
                            storage: storage.is_some(),
                            memory_input,
                        },
                    );
                }
            }
        }
        let RTLInst::Iload(chunk, _, _, destination) = inst else {
            continue;
        };
        let mut chunk = *chunk;
        if let Some(extension) = extensions.get(&node) {
            let Some(&(input, output, signed)) =
                extension.iter().next().filter(|_| extension.len() == 1)
            else {
                continue;
            };
            if integer_bits(chunk) != Some(input) || write_bits != Some(output) {
                continue;
            }
            chunk = match (input, signed) {
                (8, true) => MemoryChunk::MInt8Signed,
                (8, false) => MemoryChunk::MInt8Unsigned,
                (16, true) => MemoryChunk::MInt16Signed,
                (16, false) => MemoryChunk::MInt16Unsigned,
                (32, _) => MemoryChunk::MInt32,
                (64, _) => MemoryChunk::MInt64,
                _ => continue,
            };
        }
        by_function.entry(function).or_default().insert(
            node,
            LoadValue {
                node,
                chunk,
                destination: *destination,
                write_bits,
                signed_word_load,
            },
        );
    }
    for function in functions {
        let input_views = reads
            .iter()
            .filter_map(|(&(owner, node, reg), chunks)| {
                if owner != function.address {
                    return None;
                }
                let &(input, _, signed) =
                    extensions.get(&node).filter(|e| e.len() == 1)?.first()?;
                (matches!(input, 8 | 16)
                    && !chunks.is_empty()
                    && chunks.iter().all(|c| integer_bits(*c) == Some(input)))
                .then_some((node, reg, input, signed))
            })
            .collect();
        INPUT_VIEWS.insert(&mut function.analysis_facts, input_views);
        LOADS.insert(
            &mut function.analysis_facts,
            by_function.remove(&function.address).unwrap_or_default(),
        );
        COPIES.insert(
            &mut function.analysis_facts,
            copies.remove(&function.address).unwrap_or_default(),
        );
    }
}

fn integer_bits(chunk: MemoryChunk) -> Option<u32> {
    match chunk {
        MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => Some(8),
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => Some(16),
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => Some(32),
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => Some(64),
        _ => None,
    }
}

pub(super) fn contains(facts: &Artifacts, node: Node) -> bool {
    LOADS
        .get(facts)
        .is_some_and(|loads| loads.contains_key(&node))
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::transfers::*;
    use crate::x86::op::Operation;
    use std::sync::Arc;

    #[test]
    fn frame_width_survives_a_wide_declaration_and_a_folded_consumer() {
        let word = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let source = ClightExpr::Etempvar(3, word.clone());
        let mut f = FunctionData::new(1, "views".into(), vec![], vec![], None, 0, 90, true);
        f.node_statements
            .insert(90, vec![ClightStmt::Sset(4, source.clone())]);
        f.node_statements.insert(
            7,
            vec![ClightStmt::Sifthenelse(
                source,
                Box::new(ClightStmt::Sgoto(8)),
                Box::new(ClightStmt::Sgoto(9)),
            )],
        );
        COPIES.insert(
            &mut f.analysis_facts,
            BTreeMap::from([
                (
                    90,
                    CopyValue {
                        node: 90,
                        source: 3,
                        destination: 4,
                        bits: 8,
                        storage: true,
                        memory_input: None,
                    },
                ),
                (
                    7,
                    CopyValue {
                        node: 7,
                        source: 3,
                        destination: 5,
                        bits: 32,
                        storage: false,
                        memory_input: Some((8, false)),
                    },
                ),
            ]),
        );
        project_frame_views(&mut f);
        assert!(matches!(
            &f.node_statements[&90][0],
            ClightStmt::Sset(
                4,
                ClightExpr::Ecast(
                    _,
                    ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _)
                )
            )
        ));
        assert!(matches!(
            &f.node_statements[&7][0],
            ClightStmt::Sifthenelse(
                ClightExpr::Ecast(
                    _,
                    ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _)
                ),
                _,
                _
            )
        ));
        let once = f.node_statements.clone();
        project_frame_views(&mut f);
        assert_eq!(once, f.node_statements, "view normalization is idempotent");
    }

    #[test]
    fn promoted_storage_chunks_do_not_choose_the_load_extension() {
        for signed in [false, true] {
            let mut db = DecompileDB::default();
            db.rel_push("instr_in_function", (10_u64, 1_u64));
            db.rel_push(
                "rtl_inst",
                (10_u64, RTLInst::Iop(Operation::Omove, Arc::new(vec![3]), 4)),
            );
            db.rel_push(
                "ltl_inst",
                (
                    10_u64,
                    LTLInst::Lgetstack(Slot::Local, -8, Typ::Tint, Mreg::AX),
                ),
            );
            db.rel_push(
                "type_storage_access",
                (
                    1_u64,
                    10_u64,
                    3_u64,
                    -8_i64,
                    false,
                    MemoryChunk::MInt8Unsigned,
                ),
            );
            db.rel_push("machine_register_write_view", (10_u64, Mreg::AX, 32_u32));
            db.rel_push("machine_load_extension", (10_u64, 8_u32, 32_u32, signed));
            let mut f = FunctionData::new(1, "extension".into(), vec![], vec![], None, 0, 10, true);
            collect(&db, std::slice::from_mut(&mut f));
            assert_eq!(
                COPIES.get(&f.analysis_facts).unwrap()[&10].memory_input,
                Some((8, signed))
            );
        }
    }
}
