//! Shared append-only construction before selection binds candidate indices.
use crate::decompile::passes::clight_select::query::FunctionData;
use crate::x86::types::{ClightStmt, Node};
use std::collections::BTreeSet;

pub(crate) fn inherit(function: &mut FunctionData, mut additions: Vec<(Node, usize, ClightStmt)>) {
    additions.sort_by_key(|(node, parent, _)| (*node, *parent));
    let all_worlds: BTreeSet<_> = function.structure_worlds.iter().copied().collect();
    for (node, parent, statement) in additions {
        let candidates = function
            .node_statements
            .get_mut(&node)
            .expect("candidate has a source node");
        let worlds = function
            .candidate_structure_worlds
            .entry(node)
            .or_insert_with(|| vec![all_worlds.clone(); candidates.len()]);
        worlds.resize(candidates.len(), all_worlds.clone());
        let inherited = worlds[parent].clone();
        if let Some(existing) = candidates.iter().position(|s| s == &statement) {
            worlds[existing].extend(inherited);
        } else {
            function
                .analysis_candidates
                .entry(node)
                .or_default()
                .insert(statement.clone());
            candidates.push(statement);
            worlds.push(inherited);
        }
    }
}
