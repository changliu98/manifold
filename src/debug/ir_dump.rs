// Dumps each IR stage to separate files grouped by function, similar to CompCert's -d flags.
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::convert::from_relations::{convert_stmt, ConversionContext};
use crate::decompile::passes::c_pass::print::print_stmt;
use crate::x86::types::*;
use std::collections::{BTreeMap, HashMap};
use std::io::Write;
use std::sync::Arc;
use crate::x86::mach::Mreg;
use crate::decompile::passes::rtl_pass::convert_ltl_builtins_to_rtl;

// Per-function collector: function address -> sorted list of (node, lines).
type FuncMap = BTreeMap<u64, Vec<(u64, Vec<String>)>>;

fn build_node_to_func(db: &DecompileDB) -> HashMap<u64, u64> {
    db.rel_iter::<(Node, Address)>("instr_in_function")
        .map(|(n, f)| (*n, *f))
        .collect()
}

fn build_func_names(db: &DecompileDB) -> HashMap<u64, &str> {
    db.rel_iter::<(Symbol, Address)>("func_entry")
        .map(|(name, addr)| (*addr, *name))
        .collect()
}

fn insert_into_func_map(func_map: &mut FuncMap, node: u64, func_addr: u64, lines: Vec<String>) {
    func_map
        .entry(func_addr)
        .or_default()
        .push((node, lines));
}

// Count entries per node; nodes with >1 have ambiguity (multiple candidate lifts).
fn count_per_node(func_map: &FuncMap) -> HashMap<u64, usize> {
    let mut counts: HashMap<u64, usize> = HashMap::new();
    for entries in func_map.values() {
        for (node, _) in entries {
            *counts.entry(*node).or_insert(0) += 1;
        }
    }
    counts
}

// Prefix [candidate] to lines of nodes with multiple IR entries.
fn add_candidate_markers(func_map: &mut FuncMap) {
    let counts = count_per_node(func_map);
    for entries in func_map.values_mut() {
        for (node, lines) in entries.iter_mut() {
            if counts.get(node).copied().unwrap_or(0) > 1 {
                for line in lines.iter_mut() {
                    *line = format!("[candidate] {}", line);
                }
            }
        }
    }
}

fn write_func_map(
    path: &str,
    ir_name: &str,
    func_map: &FuncMap,
    func_names: &HashMap<u64, &str>,
) -> std::io::Result<()> {
    let mut f = std::fs::File::create(path)?;
    writeln!(f, ";; {} IR dump", ir_name)?;
    writeln!(f)?;

    for (func_addr, entries) in func_map {
        let name = func_names.get(func_addr).unwrap_or(&"unknown");
        writeln!(f, ";; ---- {} (0x{:x}) ----", name, func_addr)?;

        let mut sorted = entries.clone();
        sorted.sort_by_key(|(node, _)| *node);

        for (node, lines) in &sorted {
            for line in lines {
                writeln!(f, "  0x{:x}:  {}", node, line)?;
            }
        }
        writeln!(f)?;
    }

    Ok(())
}

// Write all IR stages to separate files: .asm, .mach, .linear, .ltl, .rtl, .cminor, .csharpminor, .clight.
pub fn dump_all_ir(
    db: &DecompileDB,
    base_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let node_to_func = build_node_to_func(db);
    let func_names = build_func_names(db);

    {
        let mut func_map: FuncMap = BTreeMap::new();
        let mut entries: Vec<_> = db
            .rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("instruction")
            .collect();
        entries.sort_by_key(|(addr, _, _, _, _, _, _, _, _, _)| *addr);

        for (addr, _size, _prefix, mnemonic, op1, op2, op3, op4, _, _) in &entries {
            let ops = format!("{} {} {} {}", op1, op2, op3, op4);
            let ops = ops.trim();
            let line = if ops.is_empty() {
                mnemonic.to_string()
            } else {
                format!("{} {}", mnemonic, ops)
            };
            if let Some(&func_addr) = node_to_func.get(addr) {
                insert_into_func_map(&mut func_map, *addr, func_addr, vec![line]);
            } else {
                insert_into_func_map(&mut func_map, *addr, *addr, vec![line]);
            }
        }

        let path = format!("{}.asm", base_path);
        write_func_map(&path, "x86 Assembly", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, inst) in db.rel_iter::<(Address, MachInst)>("mach_inst") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", inst)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.mach", base_path);
        write_func_map(&path, "Mach", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, inst) in db.rel_iter::<(Address, LinearInst)>("linear_inst") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", inst)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.linear", base_path);
        write_func_map(&path, "Linear", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", inst)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.ltl", base_path);
        write_func_map(&path, "LTL", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", inst)]);
            }
        }
        let builtin_data: Vec<_> = db
            .rel_iter::<(Node, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>)>("ltl_builtin_unconverted")
            .cloned()
            .collect();
        let reg_rtl_map: HashMap<(Node, Mreg), RTLReg> = db
            .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
            .map(|(n, m, r)| ((*n, *m), *r))
            .collect();
        let converted = convert_ltl_builtins_to_rtl(&builtin_data, &reg_rtl_map);
        for (node, inst) in converted {
            if let Some(&func_addr) = node_to_func.get(&node) {
                insert_into_func_map(&mut func_map, node, func_addr, vec![format!("{:?}", inst)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.rtl", base_path);
        write_func_map(&path, "RTL", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", stmt)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.cminor", base_path);
        write_func_map(&path, "Cminor", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        let mut func_map: FuncMap = BTreeMap::new();
        for (node, stmt) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
            if let Some(&func_addr) = node_to_func.get(node) {
                insert_into_func_map(&mut func_map, *node, func_addr, vec![format!("{:?}", stmt)]);
            }
        }
        add_candidate_markers(&mut func_map);
        let path = format!("{}.csharpminor", base_path);
        write_func_map(&path, "Csharpminor", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    {
        // ident_to_symbol is multi-valued (versioned globals, aliases); pick lex-smallest name per id.
        let id_to_name: HashMap<usize, String> = {
            let mut groups: HashMap<usize, String> = HashMap::new();
            for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
                let s = name.to_string();
                groups.entry(*id)
                    .and_modify(|curr| { if &s < curr { *curr = s.clone(); } })
                    .or_insert(s);
            }
            groups
        };
        let mut ctx = ConversionContext::new(id_to_name.clone());

        use std::collections::HashSet;
        let unwrap_slabel = |s: &ClightStmt| -> ClightStmt {
            match s {
                ClightStmt::Slabel(_, inner) => *inner.clone(),
                other => other.clone(),
            }
        };
        let emitted_pairs: Vec<(u64, ClightStmt)> = db
            .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .map(|(_, node, stmt)| (*node, unwrap_slabel(stmt)))
            .collect();
        let mut emitted_per_node: HashMap<u64, usize> = HashMap::new();
        for (node, _) in &emitted_pairs {
            *emitted_per_node.entry(*node).or_insert(0) += 1;
        }
        let selected: HashSet<(u64, ClightStmt)> = emitted_pairs
            .into_iter()
            .filter(|(node, _)| emitted_per_node.get(node) == Some(&1))
            .collect();
        let dead: HashSet<(u64, ClightStmt)> = db
            .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
            .map(|(_, node, stmt)| (*node, unwrap_slabel(stmt)))
            .collect();

        let mut func_map: FuncMap = BTreeMap::new();
        for (node, stmt) in db.rel_iter::<(Node, ClightStmt)>("clight_stmt") {
            if let Some(&func_addr) = node_to_func.get(node) {
                let cstmt = convert_stmt(stmt, &mut ctx);
                let c_code = print_stmt(&cstmt);
                let c_code = c_code.trim().to_string();

                let key = (*node, stmt.clone());
                let marker = if selected.contains(&key) {
                    "[selected] "
                } else if dead.contains(&key) {
                    "[dead]     "
                } else {
                    "[candidate]"
                };

                let line = if c_code.is_empty() {
                    format!("{} {:?}", marker, stmt)
                } else {
                    format!("{} {}", marker, c_code)
                };
                insert_into_func_map(&mut func_map, *node, func_addr, vec![line]);
            }
        }
        let path = format!("{}.clight", base_path);
        write_func_map(&path, "Clight", &func_map, &func_names)?;
        log::info!("  IR dump: {}", path);
    }

    Ok(())
}
