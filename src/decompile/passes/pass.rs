// IRPass trait, swap-run-swap macros, and dependency-based pass scheduler.
use crate::decompile::elevator::DecompileDB;
use std::collections::{HashSet, VecDeque};

// A single stage of the decompilation pipeline with declared input/output relations.
pub trait IRPass: Send + Sync {
    fn name(&self) -> &'static str;

    fn run(&self, db: &mut DecompileDB);

    fn inputs(&self) -> &'static [&'static str] {
        &[]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[]
    }

    /// Relations this pass reads through imperative `db.rel_iter(...)` calls outside its Ascent program (and helper modules invoked from `run`). Must be declared so the scheduler can clone them for parallel sub-DBs.
    fn extra_reads(&self) -> &'static [&'static str] {
        &[]
    }

    /// Per-rule dependency edges within this pass's Ascent program: (body_rel, head_rel) pairs.
    fn rule_deps(&self) -> &'static [(&'static str, &'static str)] {
        &[]
    }
}

// An edge in the pass dependency graph: from -> to via shared relations.
#[derive(Debug, Clone)]
pub struct DepEdge {
    pub from: usize,
    pub to: usize,
    pub relations: Vec<&'static str>,
}

// A group of passes that can execute concurrently (no mutual dependencies).
#[derive(Debug, Clone)]
pub struct Stage {
    pub passes: Vec<usize>,
}

// Topologically-sorted sequence of parallel stages with dependency edges.
#[derive(Debug)]
pub struct Schedule {
    pub names: Vec<&'static str>,
    pub edges: Vec<DepEdge>,
    pub stages: Vec<Stage>,
}

impl Schedule {
    pub fn print(&self) {
        log::info!("===============================================");
        log::info!("          Pass Dependency Schedule");
        log::info!("===============================================");

        if self.edges.is_empty() {
            log::info!("  (no dependencies detected)");
        } else {
            log::info!("  Dependencies:");
            for edge in &self.edges {
                let shared: Vec<_> = edge.relations.iter().copied().collect();
                let shared_str = if shared.len() <= 3 {
                    shared.join(", ")
                } else {
                    format!(
                        "{}, ... ({} relations)",
                        shared[..3].join(", "),
                        shared.len()
                    )
                };
                log::info!(
                    "    {} -> {} (via: {})",
                    self.names[edge.from],
                    self.names[edge.to],
                    shared_str
                );
            }
        }

        log::info!("  Execution stages:");
        for (i, stage) in self.stages.iter().enumerate() {
            let pass_names: Vec<_> = stage.passes.iter().map(|&idx| self.names[idx]).collect();
            let par_marker = if pass_names.len() > 1 {
                " [parallel]"
            } else {
                ""
            };
            log::info!("    Stage {}: {}{}", i, pass_names.join(", "), par_marker);
        }
        log::info!("");
    }

    /// Generate a Graphviz DOT representation of the pipeline dependency graph (uses `passes` for per-pass rule-level dependencies).
    pub fn to_dot(&self, passes: &[Box<dyn IRPass>]) -> String {
        use std::fmt::Write;
        let mut dot = String::new();
        writeln!(dot, "digraph pipeline {{").unwrap();
        writeln!(dot, "  rankdir=TB;").unwrap();
        writeln!(dot, "  compound=true;").unwrap();
        writeln!(
            dot,
            "  node [shape=box, style=filled, fillcolor=\"#f0f0f0\", fontname=\"Helvetica\"];"
        )
        .unwrap();
        writeln!(dot, "  edge [fontname=\"Helvetica\", fontsize=10];").unwrap();
        writeln!(dot).unwrap();

        // Stage subgraphs for visual grouping
        for (stage_idx, stage) in self.stages.iter().enumerate() {
            writeln!(dot, "  subgraph cluster_stage_{} {{", stage_idx).unwrap();
            writeln!(dot, "    label=\"Stage {}\";", stage_idx).unwrap();
            writeln!(dot, "    style=dashed; color=gray;").unwrap();
            for &pass_idx in &stage.passes {
                let name = self.names[pass_idx];
                let sanitized = name.replace('-', "_").replace("::", "__");
                let rule_deps = passes[pass_idx].rule_deps();
                if rule_deps.is_empty() {
                    // Simple node for passes without Ascent rules
                    writeln!(dot, "    {} [label=\"{}\"];", sanitized, name).unwrap();
                } else {
                    // Cluster subgraph showing internal rule dependencies
                    writeln!(dot, "    subgraph cluster_{} {{", sanitized).unwrap();
                    writeln!(dot, "      label=\"{}\";", name).unwrap();
                    writeln!(
                        dot,
                        "      style=filled; fillcolor=\"#e8e8ff\"; color=\"#8888cc\";"
                    )
                    .unwrap();

                    // Collect relation nodes used in this pass
                    let mut rels: Vec<&str> = Vec::new();
                    for (body, head) in rule_deps {
                        if !rels.contains(body) {
                            rels.push(body);
                        }
                        if !rels.contains(head) {
                            rels.push(head);
                        }
                    }

                    let inputs_set: std::collections::HashSet<&str> =
                        passes[pass_idx].inputs().iter().copied().collect();
                    let outputs_set: std::collections::HashSet<&str> =
                        passes[pass_idx].outputs().iter().copied().collect();

                    for rel in &rels {
                        let color = if inputs_set.contains(rel) && !outputs_set.contains(rel) {
                            "#d4edda" // green-ish for input-only
                        } else if outputs_set.contains(rel) && !inputs_set.contains(rel) {
                            "#f8d7da" // red-ish for output-only
                        } else if inputs_set.contains(rel) && outputs_set.contains(rel) {
                            "#fff3cd" // yellow for both
                        } else {
                            "#ffffff" // white for local
                        };
                        writeln!(
                            dot, "      {}_{} [label=\"{}\", shape=ellipse, fillcolor=\"{}\", style=filled, fontsize=9];",
                            sanitized, rel.replace('-', "_"), rel, color
                        ).unwrap();
                    }

                    // Internal edges (rule deps within this pass)
                    let mut seen_edges: std::collections::HashSet<(&str, &str)> =
                        std::collections::HashSet::new();
                    for (body, head) in rule_deps {
                        if body != head && seen_edges.insert((body, head)) {
                            writeln!(
                                dot,
                                "      {}_{} -> {}_{} [color=\"#666666\", arrowsize=0.6];",
                                sanitized,
                                body.replace('-', "_"),
                                sanitized,
                                head.replace('-', "_")
                            )
                            .unwrap();
                        }
                    }
                    writeln!(dot, "    }}").unwrap();
                }
            }
            writeln!(dot, "  }}").unwrap();
            writeln!(dot).unwrap();
        }

        // Inter-pass edges
        writeln!(dot, "  // Inter-pass dependency edges").unwrap();
        for edge in &self.edges {
            let from_name = self.names[edge.from].replace('-', "_").replace("::", "__");
            let to_name = self.names[edge.to].replace('-', "_").replace("::", "__");
            let from_has_rules = !passes[edge.from].rule_deps().is_empty();
            let to_has_rules = !passes[edge.to].rule_deps().is_empty();

            let label = if edge.relations.len() <= 3 {
                edge.relations.join("\\n")
            } else {
                format!(
                    "{}\\n... ({} total)",
                    edge.relations[..2].join("\\n"),
                    edge.relations.len()
                )
            };

            // Use lhead/ltail for cluster-to-cluster edges
            let mut attrs = format!("label=\"{}\"", label);
            if from_has_rules {
                attrs.push_str(&format!(", ltail=cluster_{}", from_name));
            }
            if to_has_rules {
                attrs.push_str(&format!(", lhead=cluster_{}", to_name));
            }

            // Pick a representative node inside each cluster (or the plain node)
            let from_node = if from_has_rules {
                let first_output = passes[edge.from].outputs().first().unwrap_or(&"");
                format!("{}_{}", from_name, first_output.replace('-', "_"))
            } else {
                from_name.clone()
            };
            let to_node = if to_has_rules {
                let first_input = passes[edge.to].inputs().first().unwrap_or(&"");
                format!("{}_{}", to_name, first_input.replace('-', "_"))
            } else {
                to_name.clone()
            };

            writeln!(dot, "  {} -> {} [{}];", from_node, to_node, attrs).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    /// Generate a simplified DOT showing only pass-level dependencies (no internal rule details).
    pub fn to_dot_summary(&self) -> String {
        use std::fmt::Write;
        let mut dot = String::new();
        writeln!(dot, "digraph pipeline {{").unwrap();
        writeln!(dot, "  rankdir=TB;").unwrap();
        writeln!(
            dot,
            "  node [shape=box, style=filled, fillcolor=\"#f0f0f0\", fontname=\"Helvetica\"];"
        )
        .unwrap();
        writeln!(dot, "  edge [fontname=\"Helvetica\", fontsize=10];").unwrap();
        writeln!(dot).unwrap();

        for (stage_idx, stage) in self.stages.iter().enumerate() {
            writeln!(dot, "  subgraph cluster_stage_{} {{", stage_idx).unwrap();
            writeln!(dot, "    label=\"Stage {}\";", stage_idx).unwrap();
            writeln!(dot, "    style=dashed; color=gray;").unwrap();
            for &pass_idx in &stage.passes {
                let name = self.names[pass_idx];
                let sanitized = name.replace('-', "_").replace("::", "__");
                writeln!(dot, "    {} [label=\"{}\"];", sanitized, name).unwrap();
            }
            writeln!(dot, "  }}").unwrap();
        }

        writeln!(dot).unwrap();
        for edge in &self.edges {
            let from = self.names[edge.from].replace('-', "_").replace("::", "__");
            let to = self.names[edge.to].replace('-', "_").replace("::", "__");
            let label = if edge.relations.len() <= 3 {
                edge.relations.join("\\n")
            } else {
                format!(
                    "{}\\n... ({} total)",
                    edge.relations[..2].join("\\n"),
                    edge.relations.len()
                )
            };
            writeln!(dot, "  {} -> {} [label=\"{}\"];", from, to, label).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}

// Builds a dependency graph from pass input/output declarations and produces a parallel schedule.
pub struct PassScheduler;

impl PassScheduler {
    // Compute dependency edges (read-after-write + write-after-write) and topological stage ordering.
    pub fn build_schedule(passes: &[Box<dyn IRPass>]) -> Schedule {
        let n = passes.len();
        let names: Vec<&'static str> = passes.iter().map(|p| p.name()).collect();

        // Include extra_reads in the input set so the schedule's RAW edges cover imperative reads outside the Ascent program (e.g., clight_emit_pass reading via clight_select).
        let inputs: Vec<HashSet<&'static str>> = passes
            .iter()
            .map(|p| {
                p.inputs()
                    .iter()
                    .chain(p.extra_reads().iter())
                    .copied()
                    .collect()
            })
            .collect();
        let outputs: Vec<HashSet<&'static str>> = passes
            .iter()
            .map(|p| p.outputs().iter().copied().collect())
            .collect();

        let mut in_edges: Vec<HashSet<usize>> = vec![HashSet::new(); n];
        let mut dep_edges: Vec<DepEdge> = Vec::new();

        for b in 0..n {
            for a in 0..b {
                let raw: Vec<&'static str> = inputs[b].intersection(&outputs[a]).copied().collect();

                let waw: Vec<&'static str> =
                    outputs[b].intersection(&outputs[a]).copied().collect();

                let mut relations: Vec<&'static str> = raw;
                relations.extend(waw);
                relations.sort();
                relations.dedup();

                if !relations.is_empty() {
                    in_edges[b].insert(a);
                    dep_edges.push(DepEdge {
                        from: a,
                        to: b,
                        relations,
                    });
                }
            }
        }

        let mut remaining_in: Vec<usize> = in_edges.iter().map(|s| s.len()).collect();
        let mut out_edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for b in 0..n {
            for &a in &in_edges[b] {
                out_edges[a].push(b);
            }
        }

        let mut stages: Vec<Stage> = Vec::new();
        let mut ready: VecDeque<usize> = VecDeque::new();
        for i in 0..n {
            if remaining_in[i] == 0 {
                ready.push_back(i);
            }
        }

        while !ready.is_empty() {
            let stage_passes: Vec<usize> = ready.drain(..).collect();
            for &p in &stage_passes {
                for &dep in &out_edges[p] {
                    remaining_in[dep] -= 1;
                    if remaining_in[dep] == 0 {
                        ready.push_back(dep);
                    }
                }
            }
            stages.push(Stage {
                passes: stage_passes,
            });
        }

        Schedule {
            names,
            edges: dep_edges,
            stages,
        }
    }
}

// Swap a list of relation fields between DecompileDB and an Ascent pass program.
#[macro_export]
macro_rules! swap_fields {
    ($db:expr, $prog:expr, [$($field:ident),* $(,)?]) => {
        $( $db.swap_relation_vec(stringify!($field), &mut $prog.$field); )*
    }
}

// Run an Ascent pass: swap relations in, execute fixpoint, swap results back.
#[macro_export]
macro_rules! run_pass {
    ($db:expr, $prog_ty:ty $(,)?) => {{
        let mut prog = <$prog_ty>::default();
        prog.swap_db_fields($db);
        prog.run();
        if $db.measure_rule_times {
            let pass_name = stringify!($prog_ty).to_string();
            let summary = format!(
                "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
                prog.scc_times_summary(),
                prog.relation_sizes_summary(),
            );
            // Flush per-pass so the breakdown is visible even when a later pass times out.
            eprintln!("[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]", pass_name, summary);
            $db.rule_time_reports.push((pass_name, summary));
        }
        prog.swap_db_fields($db);
    }};

    ($db:expr, $prog_ty:ty,
     inputs:  [$($input:ident),* $(,)?],
     outputs: [$($output:ident),* $(,)?] $(,)?
    ) => {{
        let mut prog = <$prog_ty>::default();
        $( $db.swap_relation_vec(stringify!($input), &mut prog.$input); )*
        $( $db.swap_relation_vec(stringify!($output), &mut prog.$output); )*
        prog.run();
        $( $db.swap_relation_vec(stringify!($input), &mut prog.$input); )*
        $( $db.swap_relation_vec(stringify!($output), &mut prog.$output); )*
    }};

    ($db:expr, $prog_ty:ty,
     relations: [$($rel:ident),* $(,)?] $(,)?
    ) => {{
        let mut prog = <$prog_ty>::default();
        $( $db.swap_relation_vec(stringify!($rel), &mut prog.$rel); )*
        prog.run();
        $( $db.swap_relation_vec(stringify!($rel), &mut prog.$rel); )*
    }};
}

// Generate inputs()/outputs() implementations for IRPass from explicit relation lists.
#[macro_export]
macro_rules! declare_io {
    (inputs: [$($input:ident),* $(,)?], outputs: [$($output:ident),* $(,)?] $(,)?) => {
        fn inputs(&self) -> &'static [&'static str] {
            &[$(stringify!($input)),*]
        }

        fn outputs(&self) -> &'static [&'static str] {
            &[$(stringify!($output)),*]
        }
    };
}

// Auto-derive inputs()/outputs()/rule_deps() from an Ascent program's generated metadata.
#[macro_export]
macro_rules! declare_io_from {
    ($prog_ty:ty) => {
        fn inputs(&self) -> &'static [&'static str] {
            <$prog_ty>::inputs_only()
        }

        fn outputs(&self) -> &'static [&'static str] {
            <$prog_ty>::rule_outputs()
        }

        fn rule_deps(&self) -> &'static [(&'static str, &'static str)] {
            <$prog_ty>::rule_dependencies()
        }
    };
}

#[cfg(test)]
mod schedule_tests {
    use super::{PassScheduler, Schedule};
    use crate::decompile::elevator::pipeline_passes;

    fn stage_of(schedule: &Schedule, name: &str) -> usize {
        for (s, stage) in schedule.stages.iter().enumerate() {
            if stage.passes.iter().any(|&i| schedule.names[i] == name) {
                return s;
            }
        }
        panic!("pass {name} is not in the schedule");
    }

    // Fall-through goto elision drops `goto L` on the evidence that L labels the
    // next statement.  Any pass that can still move a statement afterwards
    // invalidates that evidence and leaves control falling into an unrelated
    // section, so the elision has to be the last writer of the emitted tree.
    #[test]
    fn goto_elision_runs_after_every_writer_of_the_emitted_tree() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        let elide = stage_of(&schedule, "goto_elide");

        let mut writers = Vec::new();
        for pass in passes.iter() {
            if pass.name() == "goto_elide" {
                continue;
            }
            if pass
                .outputs()
                .iter()
                .any(|r| *r == "cast_optimized_translation_unit")
            {
                writers.push(pass.name());
            }
        }
        assert!(
            !writers.is_empty(),
            "expected the emit and postselect passes to write the optimized tree"
        );
        for writer in writers {
            let stage = stage_of(&schedule, writer);
            assert!(
                stage < elide,
                "{writer} rewrites the emitted tree in stage {stage}, at or after goto_elide's stage {elide}"
            );
        }
    }

    #[test]
    fn typed_c_ast_handoffs_stay_in_singleton_stages() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        for name in [
            "ClightEmit",
            "forloop",
            "var_reduce",
            "goto_elide",
            "coverage_audit",
        ] {
            let stage_index = stage_of(&schedule, name);
            let stage = &schedule.stages[stage_index];
            assert_eq!(
                stage.passes.len(),
                1,
                "{name} uses a typed DecompileDB handoff but shares stage {stage_index}"
            );
        }
    }

    #[test]
    fn direct_pointer_rtl_consumes_only_the_prepass_settled_dominator_summary() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        let dominators = passes
            .iter()
            .find(|pass| pass.name() == "rtl_dominators")
            .expect("RTL dominator pass must be registered");
        let rtl = passes
            .iter()
            .find(|pass| pass.name() == "rtl")
            .expect("RTL pass must be registered");
        let frame_writes = passes
            .iter()
            .find(|pass| pass.name() == "frame_write_state")
            .expect("frame-write state pass must be registered");
        let frame_coordinates = passes
            .iter()
            .find(|pass| pass.name() == "frame_coordinates")
            .expect("settled frame-coordinate pass must be registered");
        let stack_ptr_canonical = passes
            .iter()
            .find(|pass| pass.name() == "stack_ptr_canonical")
            .expect("settled stack-pointer projection must be registered");
        let type_pass = passes
            .iter()
            .find(|pass| pass.name() == "type")
            .expect("type pass must be registered");
        let producers: Vec<_> = passes
            .iter()
            .filter(|pass| pass.outputs().contains(&"settled_block_dom_set"))
            .map(|pass| pass.name())
            .collect();

        assert_eq!(producers, vec!["rtl_dominators"]);
        assert!(dominators.outputs().contains(&"settled_block_dom_set"));
        assert!(dominators.inputs().contains(&"call_targets_noreturn"));
        assert!(rtl.inputs().contains(&"settled_block_dom_set"));
        assert!(!rtl.outputs().contains(&"settled_block_dom_set"));
        let coordinate_producers: Vec<_> = passes
            .iter()
            .filter(|pass| pass.outputs().contains(&"settled_sp_frame_shift"))
            .map(|pass| pass.name())
            .collect();
        assert_eq!(coordinate_producers, vec!["frame_coordinates"]);
        assert!(frame_coordinates.inputs().contains(&"stack_delta"));
        assert!(frame_coordinates
            .inputs()
            .contains(&"settled_block_dom_set"));
        assert!(frame_coordinates
            .outputs()
            .contains(&"settled_sp_frame_shift"));
        assert!(frame_coordinates
            .outputs()
            .contains(&"settled_sp_entry_offset"));
        assert!(rtl.inputs().contains(&"settled_sp_entry_offset"));
        assert!(frame_writes.inputs().contains(&"decoded_stack_write_bytes"));
        assert!(frame_writes.inputs().contains(&"settled_sp_frame_shift"));
        assert!(frame_writes.inputs().contains(&"call_targets_noreturn"));
        assert!(frame_writes.inputs().contains(&"settled_block_dom_set"));
        assert!(frame_writes
            .outputs()
            .contains(&"settled_frame_write_state"));
        assert!(rtl.inputs().contains(&"settled_frame_write_state"));
        assert!(stack_ptr_canonical
            .inputs()
            .contains(&"exact_stack_addr_ptr_result"));
        assert!(stack_ptr_canonical.inputs().contains(&"xtl_canonical"));
        assert!(stack_ptr_canonical
            .outputs()
            .contains(&"canonical_exact_stack_addr_ptr_result"));
        assert!(type_pass
            .inputs()
            .contains(&"canonical_exact_stack_addr_ptr_result"));
        assert!(
            stage_of(&schedule, "linear") < stage_of(&schedule, "rtl_dominators"),
            "noreturn call fallthroughs must be removed before dominance settles"
        );
        assert!(
            stage_of(&schedule, "rtl_dominators") < stage_of(&schedule, "rtl"),
            "the final dominator summary must be published before RTL"
        );
        assert!(
            stage_of(&schedule, "linear") < stage_of(&schedule, "frame_write_state"),
            "noreturn call fallthroughs must be removed before frame writes settle"
        );
        assert!(
            stage_of(&schedule, "rtl_dominators") < stage_of(&schedule, "frame_coordinates"),
            "frame coordinates must consume only final structural dominators"
        );
        assert!(
            stage_of(&schedule, "frame_coordinates") < stage_of(&schedule, "frame_write_state"),
            "reaching writes must consume only settled exact frame coordinates"
        );
        assert!(
            stage_of(&schedule, "frame_coordinates") < stage_of(&schedule, "rtl"),
            "RTL stack consumers must receive only finalized entry coordinates"
        );
        assert!(
            stage_of(&schedule, "frame_write_state") < stage_of(&schedule, "rtl"),
            "the final reaching-write summary must be published before RTL"
        );
        assert!(
            stage_of(&schedule, "rtl") < stage_of(&schedule, "stack_ptr_canonical"),
            "exact pointer authority must wait for RTL alias closure"
        );
        assert!(
            stage_of(&schedule, "stack_ptr_canonical") < stage_of(&schedule, "type"),
            "hard pointer typing must consume the settled canonical result"
        );
    }

    #[test]
    fn relocation_proofs_consume_final_rtl_before_typing_and_layout_consumers() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        let rtl = passes
            .iter()
            .find(|pass| pass.name() == "rtl")
            .expect("RTL pass must be registered");
        let points = passes
            .iter()
            .find(|pass| pass.name() == "relocation_points_to")
            .expect("relocation points-to pass must be registered");
        let arrays = passes
            .iter()
            .find(|pass| pass.name() == "relocation_array")
            .expect("relocation array pass must be registered");

        assert!(rtl.outputs().contains(&"unknown_reg_value_reaches_use"));
        for input in [
            "arg_reg_param_live_at",
            "function_symbol",
            "main_function",
            "rtl_inst",
            "unknown_reg_value_reaches_use",
            "frame_stack_write_bytes",
            "unnormalized_frame_stack_write",
        ] {
            assert!(
                points.inputs().contains(&input),
                "missing points-to input {input}"
            );
        }
        for output in [
            "relocation_reachable_node",
            "relocation_pointer_target",
            "rtl_value_canonical",
            "must_be_ptr",
        ] {
            assert!(
                points.outputs().contains(&output),
                "missing points-to output {output}"
            );
        }
        for input in [
            "relocation_reachable_node",
            "relocation_pointer_target",
            "rtl_value_canonical",
            "retained_initialized_data_range",
        ] {
            assert!(
                arrays.inputs().contains(&input),
                "missing array input {input}"
            );
        }
        for output in [
            "relocation_target_array",
            "is_global_array",
            "global_var_ref",
        ] {
            assert!(
                arrays.outputs().contains(&output),
                "missing array output {output}"
            );
        }

        assert!(stage_of(&schedule, "rtl_optimize") < stage_of(&schedule, "relocation_points_to"));
        assert!(stage_of(&schedule, "relocation_points_to") < stage_of(&schedule, "type"));
        assert!(stage_of(&schedule, "global_array") < stage_of(&schedule, "relocation_array"));
        assert!(stage_of(&schedule, "relocation_array") < stage_of(&schedule, "struct_recovery"));
    }

    #[test]
    fn rtl_superset_waits_for_final_signatures_and_precedes_cminor() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        let optimizer = passes
            .iter()
            .find(|pass| pass.name() == "rtl_optimize")
            .expect("RTL optimizer must be registered");
        let superset = passes
            .iter()
            .find(|pass| pass.name() == "rtl_superset")
            .expect("RTL superset pass must be registered");
        let cminor = passes
            .iter()
            .find(|pass| pass.name() == "cminor")
            .expect("Cminor pass must be registered");

        assert!(optimizer.outputs().contains(&"rtl_inst_candidate"));
        assert!(superset.inputs().contains(&"rtl_inst_candidate"));
        assert!(superset.inputs().contains(&"rtl_inst"));
        assert!(superset.inputs().contains(&"rtl_expansion_edge"));
        assert!(superset.inputs().contains(&"emit_var_type_candidate"));
        assert!(superset.outputs().contains(&"rtl_inst_superset"));
        assert!(superset
            .outputs()
            .contains(&"rtl_superset_authoritative_chunk"));
        assert!(cminor.inputs().contains(&"rtl_inst_superset"));
        assert!(
            stage_of(&schedule, "signature-reconciliation") < stage_of(&schedule, "rtl_superset")
        );
        assert!(stage_of(&schedule, "rtl_superset") < stage_of(&schedule, "cminor"));
        assert!(stage_of(&schedule, "rtl_superset") < stage_of(&schedule, "clight_select"));
    }

    #[test]
    fn structure_world_superset_reaches_clight_before_selection() {
        let passes = pipeline_passes();
        let schedule = PassScheduler::build_schedule(&passes);
        let structuring = passes
            .iter()
            .find(|pass| pass.name() == "Structuring")
            .expect("Structuring pass must be registered");
        let clight = passes
            .iter()
            .find(|pass| pass.name() == "clight")
            .expect("Clight pass must be registered");
        let field = passes
            .iter()
            .find(|pass| pass.name() == "clight_field")
            .expect("Clight field pass must be registered");
        let select = passes
            .iter()
            .find(|pass| pass.name() == "clight_select")
            .expect("Clight selector must be registered");

        for relation in [
            "structure_world",
            "csharp_stmt_world",
            "structure_unchanged_node",
        ] {
            assert!(structuring.outputs().contains(&relation));
            assert!(clight.inputs().contains(&relation));
        }
        assert!(clight.outputs().contains(&"emit_clight_stmt_world"));
        assert!(clight.outputs().contains(&"emit_next_world"));
        assert!(field.inputs().contains(&"emit_clight_stmt_world"));
        assert!(field.outputs().contains(&"emit_clight_stmt_world"));
        assert!(select.inputs().contains(&"emit_clight_stmt_world"));
        assert!(stage_of(&schedule, "Structuring") < stage_of(&schedule, "clight"));
        assert!(stage_of(&schedule, "clight") < stage_of(&schedule, "clight_field"));
        assert!(stage_of(&schedule, "clight_field") < stage_of(&schedule, "clight_select"));
    }

    #[test]
    fn post_emit_audit_checkpoints_cover_every_tree_writer() {
        let passes = pipeline_passes();
        let writers: Vec<_> = passes
            .iter()
            .filter(|pass| pass.outputs().contains(&"cast_optimized_translation_unit"))
            .map(|pass| pass.name())
            .collect();
        assert_eq!(
            writers,
            vec!["ClightEmit", "forloop", "var_reduce", "goto_elide"],
            "a new emitted-tree writer needs an explicit post-emit checkpoint"
        );

        for name in ["ClightEmit", "forloop", "var_reduce"] {
            let pass = passes.iter().find(|pass| pass.name() == name).unwrap();
            assert!(
                pass.outputs().contains(&"cast_post_emit_audit_trail"),
                "{name} rewrites the emitted tree without publishing its checkpoint"
            );
        }
        let coverage = passes
            .iter()
            .find(|pass| pass.name() == "coverage_audit")
            .unwrap();
        assert!(coverage.inputs().contains(&"cast_post_emit_audit_trail"));
    }
}
