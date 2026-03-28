// Identifies nodes that failed to lift through the pipeline and dumps their available IR stages.
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;
use serde::Serialize;
use std::collections::{BTreeMap, HashMap};

#[derive(Debug, Serialize)]
pub enum LostReason {
    NoClight,
    OnlySkip,
}

#[derive(Debug, Serialize)]
pub struct LostNodeInfo {
    pub address: String,
    pub function: String,
    pub function_addr: String,
    pub reason: LostReason,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub x86_mnemonic: Option<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub mach: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub linear: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub ltl: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rtl: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub cminor: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub csharpminor: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub clight: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct LostDump {
    pub total_nodes: usize,
    pub lost_nodes: usize,
    pub coverage_pct: f64,
    pub per_function: BTreeMap<String, FunctionLostInfo>,
}

#[derive(Debug, Serialize)]
pub struct FunctionLostInfo {
    pub function_addr: String,
    pub total_nodes: usize,
    pub lost_nodes: usize,
    pub nodes: Vec<LostNodeInfo>,
}

// Check if a ClightStmt is only a placeholder (Sskip or label-wrapped Sskip).
fn is_default_stmt(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sskip => true,
        ClightStmt::Slabel(_, inner) => is_default_stmt(inner),
        _ => false,
    }
}

// Compare instr_in_function nodes against emit_clight_stmt to find unlifted nodes and dump to YAML.
pub fn dump_lost(
    db: &DecompileDB,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let func_names: HashMap<Address, &str> = db
        .rel_iter::<(Address, Symbol, Node)>("emit_function")
        .map(|(addr, name, _)| (*addr, *name))
        .collect();

    let mut func_nodes: BTreeMap<Address, Vec<Node>> = BTreeMap::new();
    for (node, func_addr) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        func_nodes.entry(*func_addr).or_default().push(*node);
    }
    for nodes in func_nodes.values_mut() {
        nodes.sort();
        nodes.dedup();
    }

    let mut emitted: HashMap<(Address, Node), Vec<ClightStmt>> = HashMap::new();
    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        emitted
            .entry((*addr, *node))
            .or_default()
            .push(stmt.clone());
    }

    let mut mach_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Address, MachInst)>("mach_inst") {
        mach_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", inst));
    }

    let mut linear_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Address, LinearInst)>("linear_inst") {
        linear_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", inst));
    }

    let mut ltl_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
        ltl_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", inst));
    }

    let mut rtl_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        rtl_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", inst));
    }

    let mut cminor_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
        cminor_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", stmt));
    }

    let mut csharp_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, stmt) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
        csharp_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", stmt));
    }

    let mut clight_map: HashMap<Node, Vec<String>> = HashMap::new();
    for (node, stmt) in db.rel_iter::<(Node, ClightStmt)>("clight_stmt") {
        clight_map
            .entry(*node)
            .or_default()
            .push(format!("{:?}", stmt));
    }

    let mut mnemonic_map: HashMap<Node, String> = HashMap::new();
    for (addr, _, _, mnemonic, _, _, _, _, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("instruction") {
        mnemonic_map.insert(*addr, mnemonic.to_string());
    }

    let mut total_nodes = 0usize;
    let mut total_lost = 0usize;
    let mut per_function: BTreeMap<String, FunctionLostInfo> = BTreeMap::new();

    for (func_addr, nodes) in &func_nodes {
        let func_name = func_names
            .get(func_addr)
            .copied()
            .unwrap_or("unknown");

        let mut lost_nodes_info = Vec::new();

        for node in nodes {
            total_nodes += 1;

            let stmts = emitted.get(&(*func_addr, *node));
            let reason = match stmts {
                None => Some(LostReason::NoClight),
                Some(stmts) if stmts.iter().all(|s| is_default_stmt(s)) => {
                    Some(LostReason::OnlySkip)
                }
                _ => None,
            };

            if let Some(reason) = reason {
                total_lost += 1;
                lost_nodes_info.push(LostNodeInfo {
                    address: format!("0x{:x}", node),
                    function: func_name.to_string(),
                    function_addr: format!("0x{:x}", func_addr),
                    reason,
                    x86_mnemonic: mnemonic_map.get(node).cloned(),
                    mach: mach_map.get(node).cloned().unwrap_or_default(),
                    linear: linear_map.get(node).cloned().unwrap_or_default(),
                    ltl: ltl_map.get(node).cloned().unwrap_or_default(),
                    rtl: rtl_map.get(node).cloned().unwrap_or_default(),
                    cminor: cminor_map.get(node).cloned().unwrap_or_default(),
                    csharpminor: csharp_map.get(node).cloned().unwrap_or_default(),
                    clight: clight_map.get(node).cloned().unwrap_or_default(),
                });
            }
        }

        if !lost_nodes_info.is_empty() {
            let func_total = nodes.len();
            let func_key = format!("{}(0x{:x})", func_name, func_addr);
            per_function.insert(
                func_key,
                FunctionLostInfo {
                    function_addr: format!("0x{:x}", func_addr),
                    total_nodes: func_total,
                    lost_nodes: lost_nodes_info.len(),
                    nodes: lost_nodes_info,
                },
            );
        }
    }

    let coverage_pct = if total_nodes > 0 {
        ((total_nodes - total_lost) as f64 / total_nodes as f64) * 100.0
    } else {
        100.0
    };

    let dump = LostDump {
        total_nodes,
        lost_nodes: total_lost,
        coverage_pct,
        per_function,
    };

    log::info!(
        "Statement coverage: {}/{} nodes ({:.1}%), {} lost",
        total_nodes - total_lost,
        total_nodes,
        coverage_pct,
        total_lost
    );

    let yaml_output =
        serde_yaml::to_string(&dump).map_err(|e| format!("Failed to serialize lost dump: {}", e))?;
    std::fs::write(output_path, yaml_output)
        .map_err(|e| format!("Failed to write lost dump to {}: {}", output_path, e))?;

    Ok(())
}
