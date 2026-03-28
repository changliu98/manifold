// Generates .dataflow.yaml: assembly with register-to-variable mappings for debugging.
use crate::decompile::elevator::DecompileDB;
use capstone::prelude::*;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use crate::x86::types::*;
use crate::x86::mach::Mreg;

#[derive(Serialize)]
struct DataflowOutput {
    binary: String,
    functions: Vec<FunctionDataflow>,
}

#[derive(Serialize)]
struct FunctionDataflow {
    name: String,
    address: String,
    instructions: Vec<InstructionDataflow>,
}

#[derive(Serialize)]
struct InstructionDataflow {
    address: String,
    asm: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    mappings: Vec<String>,
}

// Dump per-instruction register-to-RTL-variable mappings as YAML.
pub fn dump_dataflow(
    db: &DecompileDB,
    binary_path: &str,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let binary_data = std::fs::read(binary_path)
        .map_err(|e| format!("Failed to read binary file {}: {}", binary_path, e))?;

    let cs = Capstone::new()
        .x86()
        .mode(arch::x86::ArchMode::Mode64)
        .syntax(arch::x86::ArchSyntax::Att)
        .detail(true)
        .build()
        .map_err(|e| format!("Failed to create Capstone engine: {}", e))?;

    let canonical_map = build_canonical_map(db);

    let mut func_map: HashMap<u64, String> = HashMap::new();
    for (addr, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        func_map.insert(*addr as u64, name.to_string());
    }

    let mut def_sites: HashSet<(u64, String)> = HashSet::new();
    for (node, mreg) in db.rel_iter::<(Node, Mreg)>("reg_def_site") {
        def_sites.insert((*node, format!("{:?}", mreg)));
    }

    let mut reg_rtl_map: HashMap<u64, Vec<(String, u64)>> = HashMap::new();
    for (node, mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        let canonical = canonical_map.get(rtl_reg).copied().unwrap_or(*rtl_reg);
        reg_rtl_map
            .entry(*node)
            .or_default()
            .push((format!("{:?}", mreg), canonical));
    }

    let mut instr_info: HashMap<u64, (usize, String, String)> = HashMap::new();
    for (addr, size, _, mnemonic, op1, op2, op3, op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("instruction") {
        let ops = [op1, op2, op3, op4]
            .iter()
            .map(|s| format!("{}", s))
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .join(", ");
        instr_info.insert(*addr, (*size, mnemonic.to_string(), ops));
    }

    let mut func_addrs: HashMap<u64, Vec<u64>> = HashMap::new();
    for (addr, func_start) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        func_addrs.entry(*func_start).or_default().push(*addr);
    }

    let mut func_starts: Vec<u64> = func_addrs.keys().copied().collect();
    func_starts.sort();

    let mut functions = Vec::new();

    for func_start in func_starts {
        let func_name = func_map
            .get(&func_start)
            .cloned()
            .unwrap_or_else(|| format!("func_{:x}", func_start));

        let addrs = func_addrs.get(&func_start).unwrap();

        let mut sorted_addrs = addrs.clone();
        sorted_addrs.sort();

        let has_mappings = sorted_addrs.iter().any(|a| reg_rtl_map.contains_key(a));
        if !has_mappings {
            continue;
        }

        let mut instructions = Vec::new();

        for addr in sorted_addrs {
            let asm = get_asm(&cs, &binary_data, addr, &instr_info);

            let mappings_raw = reg_rtl_map.get(&addr);
            let mut mappings = Vec::new();

            if let Some(regs) = mappings_raw {
                for (mreg, var_id) in regs {
                    let role = if def_sites.contains(&(addr, mreg.clone())) {
                        "def"
                    } else {
                        "use"
                    };

                    mappings.push(format!("{} -> var_{} ({})", mreg, var_id, role));
                }
            }
            mappings.sort();

            instructions.push(InstructionDataflow {
                address: format!("0x{:x}", addr),
                asm,
                mappings,
            });
        }

        functions.push(FunctionDataflow {
            name: func_name,
            address: format!("0x{:x}", func_start),
            instructions,
        });
    }

    let output = DataflowOutput {
        binary: binary_path.to_string(),
        functions,
    };

    let yaml_output = serde_yaml::to_string(&output)
        .map_err(|e| format!("Failed to serialize to YAML: {}", e))?;

    std::fs::write(output_path, yaml_output)
        .map_err(|e| format!("Failed to write {}: {}", output_path, e))?;

    Ok(())
}

// Disassemble a single instruction at addr, falling back to stored mnemonic/operands.
fn get_asm(
    cs: &Capstone,
    binary_data: &[u8],
    addr: u64,
    instr_info: &HashMap<u64, (usize, String, String)>,
) -> String {
    if let Some((size, mnemonic, ops)) = instr_info.get(&addr) {
        let start_offset = addr as usize;
        if start_offset < binary_data.len() {
            let max_len = std::cmp::min(*size, binary_data.len() - start_offset);
            if max_len > 0 {
                let instruction_bytes = &binary_data[start_offset..start_offset + max_len];
                if let Ok(insns) = cs.disasm_count(instruction_bytes, addr, 1) {
                    if let Some(insn) = insns.iter().next() {
                        let mnemonic_cap = insn.mnemonic().unwrap_or("");
                        let op_str = insn.op_str().unwrap_or("");
                        return if op_str.is_empty() {
                            mnemonic_cap.to_string()
                        } else {
                            format!("{} {}", mnemonic_cap, op_str)
                        };
                    }
                }
            }
        }

        if ops.is_empty() {
            mnemonic.clone()
        } else {
            format!("{} {}", mnemonic, ops)
        }
    } else {
        format!("(unknown)")
    }
}

// Build canonical RTL register mapping via union-find over alias_edge.
fn build_canonical_map(db: &DecompileDB) -> HashMap<u64, u64> {
    let mut uf = UnionFind::new();

    for (r1, r2) in db.rel_iter::<(RTLReg, RTLReg)>("alias_edge") {
        uf.make_set(*r1);
        uf.make_set(*r2);
        uf.union(*r1, *r2);
    }

    let mut canonical: HashMap<u64, u64> = HashMap::new();
    let keys: Vec<u64> = uf.parent.keys().copied().collect();
    for key in keys {
        canonical.insert(key, uf.find(key));
    }

    canonical
}

struct UnionFind {
    parent: HashMap<u64, u64>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind {
            parent: HashMap::new(),
        }
    }

    fn make_set(&mut self, x: u64) {
        self.parent.entry(x).or_insert(x);
    }

    fn find(&mut self, x: u64) -> u64 {
        let mut root = x;
        while let Some(&p) = self.parent.get(&root) {
            if p == root {
                break;
            }
            root = p;
        }

        let mut curr = x;
        while curr != root {
            let next = self.parent[&curr];
            self.parent.insert(curr, root);
            curr = next;
        }
        root
    }

    fn union(&mut self, x: u64, y: u64) {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x != root_y {
            if root_x < root_y {
                self.parent.insert(root_y, root_x);
            } else {
                self.parent.insert(root_x, root_y);
            }
        }
    }
}
