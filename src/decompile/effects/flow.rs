//! Demand-bounded must-executed capture state on the actual RTL CFG.
//! Joins intersect; unknown/side-entry paths cannot donate a capture. No
//! address ordering and no pairwise reachability relation are used.
use crate::x86::types::{Address, Node};
use ascent::lattice::set::Set;
use ascent::{ascent, Dual};
use std::collections::{BTreeMap, BTreeSet};

ascent! {
    struct CaptureFlow;
    relation entry(Address, Node);
    relation edge(Address, Node, Node);
    relation capture(Address, Node);
    relation universe(Address, Set<Node>);
    lattice reachable(Address, Node, Set<()>);
    lattice before(Address, Node, Dual<Set<Node>>);
    lattice after(Address, Node, Dual<Set<Node>>);

    reachable(*f, *entry, Set::singleton(())) <-- entry(f, entry);
    reachable(*f, *to, state.clone()) <-- reachable(f, from, state), edge(f, from, to);
    before(*f, *n, Dual(all.clone())) <-- reachable(f, n, _), universe(f, all);
    before(*f, *n, Dual(Set::default())) <-- entry(f, n);
    before(*f, *to, state.clone()) <-- after(f, from, state), edge(f, from, to);
    after(*f, *n, state.clone()) <-- before(f, n, state), !capture(f, n);
    after(*f, *n, Dual(with_capture(&state.0, *n))) <-- before(f, n, state), capture(f, n);
}

fn with_capture(state: &Set<Node>, node: Node) -> Set<Node> {
    let mut next = state.clone();
    next.0.insert(node);
    next
}

pub(crate) fn must_captures(
    entry: (Address, Node),
    edges: &[(Node, Node)],
    captures: &BTreeSet<Node>,
) -> BTreeMap<Node, Set<Node>> {
    if captures.len() > 128 {
        return BTreeMap::new();
    }
    let mut p = CaptureFlow::default();
    p.entry.push(entry);
    p.universe.push((entry.0, Set(captures.clone())));
    p.capture.extend(captures.iter().map(|&n| (entry.0, n)));
    p.edge.extend(edges.iter().map(|&(a, b)| (entry.0, a, b)));
    p.run();
    p.before
        .into_iter()
        .map(|(_, n, state)| (n, state.0))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_side_entry_cannot_borrow_a_capture() {
        let captures = BTreeSet::from([900]);
        let known = must_captures((1, 500), &[(500, 900), (900, 100), (100, 30)], &captures);
        assert!(known[&30].0.contains(&900));
        let bypass = must_captures(
            (1, 500),
            &[(500, 900), (900, 100), (100, 30), (500, 30)],
            &captures,
        );
        assert!(!bypass[&30].0.contains(&900));
        assert!(
            !must_captures((1, 500), &[(500, 900), (10, 30), (30, 10)], &captures)
                .contains_key(&30)
        );
    }
}
