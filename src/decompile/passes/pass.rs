// IRPass trait, swap-run-swap macros, and dependency-based pass scheduler.
use std::collections::{HashSet, VecDeque};
use crate::decompile::elevator::DecompileDB;

// A single stage of the decompilation pipeline with declared input/output relations.
pub trait IRPass: Send + Sync {
    fn name(&self) -> &'static str;

    fn run(&self, db: &mut DecompileDB);

    fn inputs(&self) -> &'static [&'static str] { &[] }

    fn outputs(&self) -> &'static [&'static str] { &[] }

    /// Per-rule dependency edges within this pass's Ascent program: (body_rel, head_rel) pairs.
    fn rule_deps(&self) -> &'static [(&'static str, &'static str)] { &[] }
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
                    format!("{}, ... ({} relations)", shared[..3].join(", "), shared.len())
                };
                log::info!(
                    "    {} -> {} (via: {})",
                    self.names[edge.from], self.names[edge.to], shared_str
                );
            }
        }

        log::info!("  Execution stages:");
        for (i, stage) in self.stages.iter().enumerate() {
            let pass_names: Vec<_> = stage.passes.iter().map(|&idx| self.names[idx]).collect();
            let par_marker = if pass_names.len() > 1 { " [parallel]" } else { "" };
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
        writeln!(dot, "  node [shape=box, style=filled, fillcolor=\"#f0f0f0\", fontname=\"Helvetica\"];").unwrap();
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
                    writeln!(dot, "      style=filled; fillcolor=\"#e8e8ff\"; color=\"#8888cc\";").unwrap();

                    // Collect relation nodes used in this pass
                    let mut rels: Vec<&str> = Vec::new();
                    for (body, head) in rule_deps {
                        if !rels.contains(body) { rels.push(body); }
                        if !rels.contains(head) { rels.push(head); }
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
                    let mut seen_edges: std::collections::HashSet<(&str, &str)> = std::collections::HashSet::new();
                    for (body, head) in rule_deps {
                        if body != head && seen_edges.insert((body, head)) {
                            writeln!(
                                dot, "      {}_{} -> {}_{} [color=\"#666666\", arrowsize=0.6];",
                                sanitized, body.replace('-', "_"),
                                sanitized, head.replace('-', "_")
                            ).unwrap();
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
                format!("{}\\n... ({} total)", edge.relations[..2].join("\\n"), edge.relations.len())
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
        writeln!(dot, "  node [shape=box, style=filled, fillcolor=\"#f0f0f0\", fontname=\"Helvetica\"];").unwrap();
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
                format!("{}\\n... ({} total)", edge.relations[..2].join("\\n"), edge.relations.len())
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

        let inputs: Vec<HashSet<&'static str>> = passes
            .iter()
            .map(|p| p.inputs().iter().copied().collect())
            .collect();
        let outputs: Vec<HashSet<&'static str>> = passes
            .iter()
            .map(|p| p.outputs().iter().copied().collect())
            .collect();

        let mut in_edges: Vec<HashSet<usize>> = vec![HashSet::new(); n];
        let mut dep_edges: Vec<DepEdge> = Vec::new();

        for b in 0..n {
            for a in 0..b {
                let raw: Vec<&'static str> = inputs[b]
                    .intersection(&outputs[a])
                    .copied()
                    .collect();

                let waw: Vec<&'static str> = outputs[b]
                    .intersection(&outputs[a])
                    .copied()
                    .collect();

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
