// Generates .debug.yaml: all IR stages for each instruction address, used for pipeline debugging.
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::rtl_pass::convert_ltl_builtins_to_rtl;
use crate::decompile::passes::c_pass::convert::from_relations::{convert_stmt, ConversionContext};
use crate::decompile::passes::c_pass::print::print_stmt;
use crate::x86::types::*;
use capstone::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use crate::x86::mach::Mreg;
use std::sync::Arc;

#[derive(Debug, Serialize, Deserialize)]
pub struct DebugDump {
    pub binary_path: String,
    pub addresses: BTreeMap<String, AddressDebugInfo>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct AddressDebugInfo {
    pub address_dec: u64,
    pub x86_asm: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub mach: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub linear: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub ltl: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub stack_vars: Vec<StackVar>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rtl: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub cminor: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub clight: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub clight_c: Option<String>,
    
}


#[derive(Debug, Serialize, Deserialize)]
pub struct StackVar {
    pub offset: i64,
    pub rtl_reg: u64,
    pub ptr_class: String,
}

// Classify an RTL register as pointer, data, or unknown from is_ptr/is_not_ptr relations.
fn get_ptr_class_string(db: &DecompileDB, rtl_reg: u64) -> String {
    let in_ptr = db.rel_iter::<(RTLReg,)>("is_ptr").any(|(r,)| *r == rtl_reg);
    let in_not_ptr = db.rel_iter::<(RTLReg,)>("is_not_ptr").any(|(r,)| *r == rtl_reg);

    match (in_ptr, in_not_ptr) {
        (true, false) => "pointer".to_string(),
        (false, true) => "data".to_string(),
        _ => "unknown".to_string(),
    }
}

// Dump all IR stages (mach, linear, ltl, rtl, cminor, clight) per instruction to YAML.
pub fn dump_debug(
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

    let node_to_func: HashMap<u64, u64> = db
        .rel_iter::<(Node, Address)>("instr_in_function")
        .map(|(n, f)| (*n, *f))
        .collect();

    let mut ltl_map: HashMap<u64, Vec<&LTLInst>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
        ltl_map.entry(*node).or_insert_with(Vec::new).push(inst);
    }

    let mut mach_map: HashMap<u64, Vec<&MachInst>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Address, MachInst)>("mach_inst") {
        mach_map.entry(*node).or_insert_with(Vec::new).push(inst);
    }

    let mut linear_map: HashMap<u64, Vec<&LinearInst>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Address, LinearInst)>("linear_inst") {
        linear_map.entry(*node).or_insert_with(Vec::new).push(inst);
    }

    let builtin_data: Vec<_> = db.rel_iter::<(Node, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>)>("ltl_builtin_unconverted").cloned().collect();
    let reg_rtl_map: HashMap<(Node, Mreg), RTLReg> = db
        .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
        .map(|(n, m, r)| ((*n, *m), *r))
        .collect();
    let converted_builtins = convert_ltl_builtins_to_rtl(&builtin_data, &reg_rtl_map);

    let mut rtl_map: HashMap<u64, Vec<RTLInst>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        rtl_map
            .entry(*node)
            .or_insert_with(Vec::new)
            .push(inst.clone());
    }
    for (node, inst) in converted_builtins {
        rtl_map.entry(node).or_insert_with(Vec::new).push(inst);
    }

    let mut cminor_map: HashMap<u64, Vec<&CminorStmt>> = HashMap::new();
    for (node, stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
        cminor_map.entry(*node).or_insert_with(Vec::new).push(stmt);
    }

    let mut clight_map: HashMap<u64, Vec<&ClightStmt>> = HashMap::new();
    for (node, stmt) in db.rel_iter::<(Node, ClightStmt)>("clight_stmt") {
        clight_map.entry(*node).or_insert_with(Vec::new).push(stmt);
    }

    let mut stack_var_map: HashMap<u64, Vec<(i64, u64)>> = HashMap::new();
    for (func_start, _addr, offset, rtl_reg) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        stack_var_map
            .entry(*func_start)
            .or_insert_with(Vec::new)
            .push((*offset, *rtl_reg));
    }

    let mut sorted_instructions: Vec<_> = db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("instruction").collect();
    sorted_instructions.sort_by_key(|(addr, _, _, _, _, _, _, _, _, _)| *addr);

    let mut addresses = BTreeMap::new();

    for (addr, size, _, mnemonic, op1, op2, op3, op4, _, _) in sorted_instructions {
        let node = *addr;
        let addr_key = format!("0x{:x}", addr);

        // NOTE: virtual address as file offset works for PIE binaries but may be incorrect for non-PIE.
        let start_offset = *addr as usize;
        let fallback = || Some(format!("{} {}", mnemonic, format!("{} {} {} {}", op1, op2, op3, op4).trim()));
        let asm_info = if start_offset < binary_data.len() {
            let max_len = std::cmp::min(*size as usize, binary_data.len() - start_offset);
            let instruction_bytes = &binary_data[start_offset..start_offset + max_len];

            if let Ok(insns) = cs.disasm_count(instruction_bytes, *addr, 1) {
                if let Some(insn) = insns.iter().next() {
                    let mnemonic_cap = insn.mnemonic().unwrap_or("").to_string();
                    let op_str = insn.op_str().unwrap_or("").to_string();
                    if op_str.is_empty() {
                        Some(mnemonic_cap)
                    } else {
                        Some(format!("{} {}", mnemonic_cap, op_str))
                    }
                } else {
                    fallback()
                }
            } else {
                fallback()
            }
        } else {
            fallback()
        };

        let mut mach = Vec::new();
        if let Some(mach_insts) = mach_map.get(&node) {
            for inst in mach_insts {
                mach.push(format!("{:?}", inst));
            }
        }

        let mut linear = Vec::new();
        if let Some(linear_insts) = linear_map.get(&node) {
            for inst in linear_insts {
                linear.push(format!("{:?}", inst));
            }
        }

        let mut ltl = Vec::new();
        if let Some(ltl_insts) = ltl_map.get(&node) {
            for inst in ltl_insts {
                ltl.push(format!("{:?}", inst));
            }
        }


        let mut stack_vars_set = HashSet::new();
        if let Some(stack_var_list) = stack_var_map.get(addr) {
            for (offset, rtl_reg) in stack_var_list {
                let ptr_class = get_ptr_class_string(db, *rtl_reg);
                stack_vars_set.insert((*offset, *rtl_reg, ptr_class));
            }
        }
        let mut stack_vars: Vec<StackVar> = stack_vars_set
            .into_iter()
            .map(|(offset, rtl_reg, ptr_class)| StackVar {
                offset,
                rtl_reg,
                ptr_class,
            })
            .collect();
        stack_vars.sort_by(|a, b| a.offset.cmp(&b.offset));

        let mut rtl = Vec::new();
        if let Some(rtl_insts) = rtl_map.get(&node) {
            for inst in rtl_insts {
                rtl.push(format!("{:?}", inst));
            }
        }

        let mut cminor = Vec::new();
        if let Some(cminor_stmts) = cminor_map.get(&node) {
            for stmt in cminor_stmts {
                cminor.push(format!("{:?}", stmt));
            }
        }

        let mut clight = Vec::new();
        let mut clight_c_parts = Vec::new();
        if let Some(clight_stmts) = clight_map.get(&node) {
            let id_to_name: HashMap<usize, String> = db.rel_iter::<(Ident, Symbol)>("ident_to_symbol")
                .map(|(id, name)| (*id, name.to_string()))
                .collect();
            let mut ctx = ConversionContext::new(id_to_name);

            for stmt in clight_stmts {
                clight.push(format!("{:?}", stmt));

                let cstmt = convert_stmt(stmt, &mut ctx);
                let c_code = print_stmt(&cstmt);
                let c_code_trimmed = c_code.trim();
                if !c_code_trimmed.is_empty() {
                    clight_c_parts.push(c_code_trimmed.to_string());
                }
            }
        }

        let clight_c = if clight_c_parts.is_empty() {
            None
        } else {
            Some(clight_c_parts.join("\n"))
        };


        addresses.insert(
            addr_key.clone(),
            AddressDebugInfo {
                address_dec: *addr,
                x86_asm: asm_info,
                mach,
                linear,
                ltl,
                stack_vars,
                rtl,
                cminor,
                clight,
                clight_c,
            },
        );
    }

    let debug_dump = DebugDump {
        binary_path: binary_path.to_string(),
        addresses,
    };

    let yaml_output = serde_yaml::to_string(&debug_dump)
        .map_err(|e| format!("Failed to serialize to YAML: {}", e))?;

    std::fs::write(output_path, yaml_output)
        .map_err(|e| format!("Failed to write YAML file {}: {}", output_path, e))?;

    Ok(())
}
