//! Opt-in snapshots of the actual selection problem, never an alternate solve.
//!
//! `MANIFOLD_SELECTION_AUDIT_DIR` requests fresh per-solve artifact directories;
//! `MANIFOLD_SELECTION_AUDIT_FUNCTION` optionally restricts the function address
//! (hexadecimal). No labels, forced types, or benchmark policy enter selection.
//! SAT in a snapshot means feasibility in the recorded formula, not validation
//! of semantic obligations that were never visited by the production search.

use super::{BuiltFunction, FunctionData};
use crate::decompile::passes::c_pass::print::Printer;
use crate::decompile::passes::clight_select::type_graph::TypeTerm;
use serde_json::{json, Value};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use z3::ast::Bool;
use z3::{Model, Optimize, SatResult};

pub(super) struct Snapshot(Option<(PathBuf, String)>);

impl Snapshot {
    pub(super) fn start(function: &FunctionData, optimizer: &Optimize) -> Self {
        let Some(directory) = std::env::var_os("MANIFOLD_SELECTION_AUDIT_DIR") else {
            return Self(None);
        };
        if let Ok(address) = std::env::var("MANIFOLD_SELECTION_AUDIT_FUNCTION") {
            if u64::from_str_radix(address.trim_start_matches("0x"), 16).ok()
                != Some(function.address)
            {
                return Self(None);
            }
        }
        Self(Some((PathBuf::from(directory), optimizer.to_string())))
    }

    pub(super) fn finish(
        self,
        built: &BuiltFunction,
        function: &FunctionData,
        optimizer: &Optimize,
        softs: &[(Bool, u64)],
        model: Option<&Model>,
        status: SatResult,
    ) {
        let Some((root, base)) = self.0 else { return };
        let (aliases, mut metadata) = describe(built, function, softs, model, status);
        metadata["model_objectives"] = json!(optimizer
            .get_objectives()
            .iter()
            .map(|objective| {
                model
                    .and_then(|m| m.eval(objective, true))
                    .map(|value| value.to_string())
            })
            .collect::<Vec<_>>());
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let output = root.join(format!(
            "{:x}-{}-{}",
            function.address,
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let write = || -> Result<(), Box<dyn std::error::Error>> {
            std::fs::create_dir_all(&root)?;
            // Never reuse an earlier result, including after a failed write.
            std::fs::create_dir(&output)?;
            std::fs::write(output.join("base.smt2"), format!("{base}\n{aliases}"))?;
            std::fs::write(output.join("final.smt2"), format!("{optimizer}\n{aliases}"))?;
            std::fs::write(
                output.join("choices.json"),
                serde_json::to_vec_pretty(&metadata)?,
            )?;
            Ok(())
        };
        if let Err(error) = write() {
            eprintln!("[selection-audit] {}: {error}", output.display());
        }
    }
}

fn describe(
    built: &BuiltFunction,
    function: &FunctionData,
    softs: &[(Bool, u64)],
    model: Option<&Model>,
    status: SatResult,
) -> (String, Value) {
    let mut aliases = String::new();
    let mut next = 0;
    let mut alias = |condition: &Bool| {
        let name = format!("manifold_audit_{next}");
        next += 1;
        writeln!(aliases, "(declare-fun {name} () Bool)").unwrap();
        writeln!(aliases, "(assert (= {name} {condition}))").unwrap();
        name
    };
    let truth =
        |condition: &Bool| model.and_then(|m| m.eval(condition, true).and_then(|v| v.as_bool()));
    let spell = |term: &TypeTerm| {
        let mut printer = Printer::with_default_config();
        printer.print_type(&term.to_c(function.data_model));
        printer.into_string()
    };
    let mut registers = Vec::new();
    let graph = super::analysis::type_evidence::GRAPH.get(&function.analysis_facts);
    for &reg in &built.regs {
        let choice = built.concrete_declarations.0.get(&reg);
        let alternatives: Vec<_> = choice
            .into_iter()
            .flat_map(|c| &c.alternatives)
            .map(|(id, selected)| {
                let choice = choice.unwrap();
                json!({
                    "type": spell(built.concrete_declarations.term(*id)),
                    "literal": alias(selected), "selected": truth(selected),
                    "legacy": choice.legacy.contains(id),
                    "evidence": choice.evidence.contains(id),
                    "proposed": choice.proposed.contains(id),
                })
            })
            .collect();
        registers.push(json!({
            "reg": reg, "managed": choice.is_some(),
            "must_pointer": function.must_pointer_regs.contains(&reg),
            "fixed": graph.is_some_and(|g| g.fixed.contains(&reg)),
            "unknown_storage": graph.is_some_and(|g| g.unknown_storage.contains(&reg)),
            "unknown_values": graph.is_some_and(|g| g.unknown_values.contains(&reg)),
            "parameter": function.param_regs.iter().position(|r| *r == reg),
            "upstream": function.var_type_candidates[&reg].iter()
                .map(|c| spell(&TypeTerm::from_candidate(*c, function.data_model)))
                .collect::<Vec<_>>(),
            "alternatives": alternatives,
        }));
    }
    let mut statements = Vec::new();
    for &node in &built.nodes {
        if let Some(choices) = built.selvar.get(&node) {
            for (index, selected) in choices.iter().enumerate() {
                statements.push(json!({"node": node, "index": index,
                    "literal": alias(selected), "selected": truth(selected)}));
            }
        }
    }
    let softs: Vec<_> = softs
        .iter()
        .map(|(condition, weight)| {
            json!({"literal": alias(condition), "weight": weight,
                   "satisfied": truth(condition)})
        })
        .collect();
    let metadata = json!({
        "schema": 1, "function": function.address, "name": function.name,
        "z3": z3::full_version(),
        "status": format!("{status:?}"),
        "scope": "recorded hard constraints and learned refutations; unvisited semantic obligations remain unchecked",
        "registers": registers, "statements": statements, "base_softs": softs,
    });
    (aliases, metadata)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::{
        analysis::{c_types::CTypes, type_evidence::GRAPH, type_recovery::TypeRecovery, Stack},
        candtype::{CandType, Sign},
        type_graph::{EvidenceGraph, Fact},
    };
    use std::collections::HashMap;

    #[test]
    fn snapshot_distinguishes_available_and_refuted_without_mutating_selection() {
        let mut function = FunctionData::new(1, "audit".into(), vec![], vec![], None, 0, 7, true);
        let word = CandType::I64(Sign::Signed);
        let byte = CandType::I8(Sign::Signed);
        function.var_type_candidates.insert(10, vec![word, byte]);
        function.var_types.insert(10, word);
        let ty = TypeTerm::from_candidate(byte, function.data_model);
        let mut graph = EvidenceGraph::default();
        graph.hypotheses.entry(10).or_default().insert(ty.clone());
        graph.facts.insert(Fact::ValueHint {
            value: 10,
            ty: ty.clone(),
        });
        GRAPH.insert(&mut function.analysis_facts, graph);
        let optimizer = Optimize::new();
        let backend = super::super::OptimizeBackend::new(&optimizer);
        let built = super::super::build_function_constraints_with_stack(
            super::super::TypeDt::build(),
            &function,
            &HashMap::new(),
            &[],
            &backend,
            &Stack::new(&[&TypeRecovery, &CTypes]),
        );
        let softs = backend.into_softs();
        let before = optimizer.to_string();
        let (_, rejected) = built
            .concrete_declarations
            .options(10)
            .find(|(t, _)| **t == ty)
            .unwrap();
        optimizer.assert(&rejected.not());
        assert_eq!(optimizer.check(&[]), SatResult::Sat);
        let production = optimizer.to_string();
        let (aliases, metadata) = describe(
            &built,
            &function,
            &softs,
            optimizer.get_model().as_ref(),
            SatResult::Sat,
        );
        assert_eq!(production, optimizer.to_string());
        let literal = metadata["registers"][0]["alternatives"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["type"] == "char")
            .unwrap()["literal"]
            .as_str()
            .unwrap();
        for (snapshot, expected) in [(before, SatResult::Sat), (production, SatResult::Unsat)] {
            let replay = Optimize::new();
            replay.from_string(format!("{snapshot}\n{aliases}\n(assert {literal})"));
            assert_eq!(replay.check(&[]), expected);
        }
    }
}
