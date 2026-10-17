//! Selection-owned value partitions, before concrete declarations are bound.
//!
//! An RTL name is not a C variable identity. Definitions which meet at a read
//! must share a binding in this initial grammar; independent def/use webs may
//! have different declarations. This is a CFG-certified alpha expansion, not
//! a type assertion. Every expanded binding retains the original alternatives
//! and must pass the ordinary declaration/transfer checks. Storage coordinates
//! belong to native access events, never to every temporary derived from them.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::syntax::ArtifactKey;
use crate::decompile::passes::clight_select::{
    query::FunctionData,
    type_graph::{Entity, EvidenceGraph, Fact},
};
use crate::x86::types::*;
use ascent::{ascent, lattice::set::Set};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

pub(super) const INPUTS: &[&str] = &[
    "rtl_inst",
    "rtl_succ",
    "rtl_function_entry",
    "instr_in_function",
];
pub(crate) const PLAN: ArtifactKey<BindingPlan> = ArtifactKey::new("native-binding-plan");

/// Semantic identity is a native definition web, independent of its C name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Binding {
    pub native: RTLReg,
    pub definitions: BTreeSet<Node>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct BindingPlan {
    pub bindings: BTreeMap<RTLReg, Binding>,
    reads: BTreeMap<(Node, RTLReg), RTLReg>,
    writes: BTreeMap<(Node, RTLReg), RTLReg>,
    /// A storage event binds only the value at that event, not every web.
    pub storage: BTreeSet<(Node, RTLReg, RTLReg)>,
}

impl BindingPlan {
    #[cfg(test)]
    pub(crate) fn from_test_events(
        reads: impl IntoIterator<Item = ((Node, RTLReg), RTLReg)>,
        writes: impl IntoIterator<Item = ((Node, RTLReg), RTLReg)>,
    ) -> Self {
        Self {
            reads: reads.into_iter().collect(),
            writes: writes.into_iter().collect(),
            ..Self::default()
        }
    }
    pub(crate) fn native_register(&self, binding: RTLReg) -> RTLReg {
        self.bindings.get(&binding).map_or(binding, |b| b.native)
    }
    pub(crate) fn read(&self, node: Node, reg: RTLReg) -> RTLReg {
        self.reads.get(&(node, reg)).copied().unwrap_or(reg)
    }
    pub(crate) fn write(&self, node: Node, reg: RTLReg) -> RTLReg {
        self.writes.get(&(node, reg)).copied().unwrap_or(reg)
    }
    pub(super) fn alternatives(&self, reg: RTLReg) -> Vec<RTLReg> {
        let result: Vec<_> = self
            .bindings
            .iter()
            .filter_map(|(&id, b)| (b.native == reg).then_some(id))
            .collect();
        if result.is_empty() {
            vec![reg]
        } else {
            result
        }
    }
    pub(crate) fn native(&self, node: Node, inst: &RTLInst) -> RTLInst {
        use RTLInst::*;
        let args = |xs: &Args| Arc::new(xs.iter().map(|r| self.read(node, *r)).collect());
        match inst {
            Iop(op, xs, dst) => Iop(op.clone(), args(xs), self.write(node, *dst)),
            Iload(c, a, xs, dst) => Iload(*c, a.clone(), args(xs), self.write(node, *dst)),
            Istore(c, a, xs, src) => Istore(*c, a.clone(), args(xs), self.read(node, *src)),
            Icond(c, xs, yes, no) => Icond(c.clone(), args(xs), *yes, *no),
            _ => inst.clone(), // Eligible definitions are deliberately only Iop.
        }
    }
    pub(crate) fn statement(&self, node: Node, statement: &ClightStmt) -> ClightStmt {
        fn expr(plan: &BindingPlan, node: Node, e: &mut ClightExpr) {
            use ClightExpr::*;
            match e {
                Etempvar(r, _) => *r = plan.read(node, *r as RTLReg) as Ident,
                Ederef(e, _) | Eaddrof(e, _) | Ecast(e, _) | Eunop(_, e, _) | Efield(e, _, _) => {
                    expr(plan, node, e)
                }
                Ebinop(_, a, b, _) => {
                    expr(plan, node, a);
                    expr(plan, node, b);
                }
                Econdition(c, a, b, _) => {
                    expr(plan, node, c);
                    expr(plan, node, a);
                    expr(plan, node, b);
                }
                _ => {}
            }
        }
        fn visit(plan: &BindingPlan, node: Node, s: &mut ClightStmt) {
            use ClightStmt::*;
            match s {
                Sset(r, e) => {
                    expr(plan, node, e);
                    *r = plan.write(node, *r as RTLReg) as Ident;
                }
                Sassign(a, b) => {
                    expr(plan, node, a);
                    expr(plan, node, b);
                }
                Scall(dst, callee, xs) => {
                    if let Some(r) = dst {
                        *r = plan.write(node, *r as RTLReg) as Ident;
                    }
                    expr(plan, node, callee);
                    for x in xs {
                        expr(plan, node, x);
                    }
                }
                Sbuiltin(dst, _, _, xs) => {
                    if let Some(r) = dst {
                        *r = plan.write(node, *r as RTLReg) as Ident;
                    }
                    for x in xs {
                        expr(plan, node, x);
                    }
                }
                Sifthenelse(c, a, b) => {
                    expr(plan, node, c);
                    visit(plan, node, a);
                    visit(plan, node, b);
                }
                Sswitch(e, arms) => {
                    expr(plan, node, e);
                    for (_, s) in arms {
                        visit(plan, node, s);
                    }
                }
                Sreturn(Some(e)) => expr(plan, node, e),
                Slabel(_, body) | Seffect(_, body) => visit(plan, node, body),
                Ssequence(items) => {
                    for s in items {
                        visit(plan, node, s);
                    }
                }
                Sloop(a, b) => {
                    visit(plan, node, a);
                    visit(plan, node, b);
                }
                _ => {}
            }
        }
        let mut result = statement.clone();
        visit(self, node, &mut result);
        result
    }
}

type Definitions = Set<(RTLReg, Option<Node>)>;

fn transfer(before: &Definitions, node: Node, definition: Option<RTLReg>) -> Definitions {
    let mut after = before.0.clone();
    if let Some(reg) = definition {
        after.retain(|(r, _)| *r != reg);
        after.insert((reg, Some(node)));
    }
    Set(after)
}

ascent! {
    struct ReachingDefinitions;
    relation entry(Node, Definitions);
    relation edge(Node, Node);
    relation definition(Node, Option<RTLReg>);
    relation unknown(Node, Definitions);
    lattice before(Node, Definitions);
    before(*node, initial.clone()) <-- entry(node, initial);
    before(*next, transfer(state, *node, *destination)) <--
        before(node, state), edge(node, next), definition(node, destination);
    before(*next, top.clone()) <-- before(node, _), edge(node, next), unknown(node, top);
}

/// Restrict expansion to sites with one native effect. Moving a nested read
/// to its enclosing condition would invent reaching definitions. Such values
/// stay unsplit until region-origin contracts can describe their exact sites.
fn flat(statement: &ClightStmt) -> bool {
    use ClightStmt::*;
    match statement {
        Slabel(_, s) | Seffect(_, s) => flat(s),
        Ssequence(xs) if xs.len() == 1 => flat(&xs[0]),
        Sifthenelse(_, a, b) => {
            matches!(a.as_ref(), Sgoto(_) | Sskip) && matches!(b.as_ref(), Sgoto(_) | Sskip)
        }
        Sswitch(_, arms) => arms.iter().all(|(_, s)| matches!(s, Sgoto(_) | Sskip)),
        Ssequence(_) | Sloop(..) => false,
        _ => true,
    }
}

fn addressable_registers(statement: &ClightStmt) -> BTreeSet<RTLReg> {
    fn expr(e: &ClightExpr, address: bool, out: &mut BTreeSet<RTLReg>) {
        use ClightExpr::*;
        match e {
            Etempvar(r, _) if address => {
                out.insert(*r as RTLReg);
            }
            Evar(r, _) => {
                out.insert(*r as RTLReg);
            }
            Eaddrof(e, _) => expr(e, true, out),
            Ederef(e, _) | Ecast(e, _) | Eunop(_, e, _) | Efield(e, _, _) => expr(e, address, out),
            Ebinop(_, a, b, _) => {
                expr(a, address, out);
                expr(b, address, out);
            }
            Econdition(c, a, b, _) => {
                expr(c, address, out);
                expr(a, address, out);
                expr(b, address, out);
            }
            _ => {}
        }
    }
    fn stmt(s: &ClightStmt, out: &mut BTreeSet<RTLReg>) {
        use ClightStmt::*;
        match s {
            Sset(_, e) | Sreturn(Some(e)) => expr(e, false, out),
            Sassign(a, b) => {
                expr(a, true, out);
                expr(b, false, out);
            }
            Scall(_, callee, args) => {
                expr(callee, false, out);
                for arg in args {
                    expr(arg, false, out);
                }
            }
            Sbuiltin(_, _, _, args) => {
                for arg in args {
                    expr(arg, false, out);
                }
            }
            Sifthenelse(c, a, b) => {
                expr(c, false, out);
                stmt(a, out);
                stmt(b, out);
            }
            Sswitch(e, arms) => {
                expr(e, false, out);
                for (_, s) in arms {
                    stmt(s, out);
                }
            }
            Slabel(_, s) | Seffect(_, s) => stmt(s, out),
            Ssequence(ss) => {
                for s in ss {
                    stmt(s, out);
                }
            }
            Sloop(a, b) => {
                stmt(a, out);
                stmt(b, out);
            }
            _ => {}
        }
    }
    let mut result = BTreeSet::new();
    stmt(statement, &mut result);
    result
}

#[cfg(test)]
fn plan(
    function: &FunctionData,
    native: &BTreeMap<Node, RTLInst>,
    edges: &[(Node, Node)],
    entry: Node,
) -> BindingPlan {
    plan_with_reserved(function, native, edges, entry, &BTreeSet::new())
}

fn plan_with_reserved(
    function: &FunctionData,
    native: &BTreeMap<Node, RTLInst>,
    edges: &[(Node, Node)],
    entry: Node,
    reserved: &BTreeSet<RTLReg>,
) -> BindingPlan {
    let Some(graph) = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
        .get(&function.analysis_facts)
    else {
        return BindingPlan::default();
    };
    let mut definitions = BTreeMap::<RTLReg, BTreeSet<Node>>::new();
    for (&node, inst) in native {
        if let Some(reg) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0 {
            definitions.entry(reg).or_default().insert(node);
        }
    }
    let mut eligible: BTreeSet<_> = graph
        .hypotheses
        .iter()
        .filter_map(|(&r, ts)| {
            (!graph.fixed.contains(&r)
                && !function.param_regs.contains(&r)
                && function.return_reg != Some(r)
                && !function.must_pointer_regs.contains(&r)
                && !function.reg_struct_ids.contains_key(&r)
                && !ts.is_empty()
                && ts.iter().all(|t| t.is_integer())
                && definitions.get(&r).is_some_and(|d| d.len() > 1))
            .then_some(r)
        })
        .collect();
    for w in &function.storage_writes {
        eligible.remove(&w.root);
        for r in &w.locals {
            eligible.remove(r);
        }
    }
    for r in &function.storage_reads {
        eligible.remove(&r.root);
        eligible.remove(&r.destination);
    }
    for fact in &graph.facts {
        match fact {
            Fact::PointerAccess { base, .. } => {
                eligible.remove(base);
            }
            Fact::Interface { value: Some(r), .. } => {
                eligible.remove(r);
            }
            _ => {}
        }
    }
    let mut queries = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
    for (&node, candidates) in &function.node_statements {
        for statement in candidates {
            let dependencies =
                crate::decompile::passes::clight_select::syntax::declarations::dependencies(
                    statement,
                );
            if !flat(statement) {
                for r in dependencies {
                    eligible.remove(&r);
                }
                continue;
            }
            // Native->C coverage above is not enough: an extra C definition
            // without a native producer would otherwise keep the old name
            // while subsequent reads silently switch to a different binding.
            let destination =
                match crate::decompile::passes::clight_select::solvers::memory_theory::primitive(
                    statement,
                ) {
                    ClightStmt::Sset(r, _) => Some(*r as RTLReg),
                    ClightStmt::Scall(r, _, _) | ClightStmt::Sbuiltin(r, _, _, _) => {
                        r.map(|r| r as RTLReg)
                    }
                    _ => None,
                };
            if let Some(r) = destination {
                if native
                    .get(&node)
                    .and_then(|i| crate::decompile::passes::rtl_optimize_pass::inst_def_use(i).0)
                    != Some(r)
                {
                    eligible.remove(&r);
                }
            }
            for r in addressable_registers(statement) {
                eligible.remove(&r);
            }
            queries.entry(node).or_default().extend(
                crate::decompile::passes::cminor_pass::extract_var_reads_from_stmt(statement)
                    .into_iter()
                    .map(|r| r as RTLReg),
            );
        }
    }
    eligible.retain(|r| definitions[r].iter().all(|node| {
        matches!(native.get(node), Some(RTLInst::Iop(_, _, dst)) if dst == r)
            && function.node_statements.get(node).is_some_and(|candidates| !candidates.is_empty() && candidates.iter().all(|s|
                matches!(crate::decompile::passes::clight_select::solvers::memory_theory::primitive(s), ClightStmt::Sset(dst, _) if *dst as RTLReg == *r)))
    }));
    // A deterministic work bound only disables optional expansion. It does
    // not decide reachability or license a representation/type change.
    if eligible.is_empty() || edges.len().saturating_mul(eligible.len()) > 65_536 {
        return BindingPlan::default();
    }
    for (&node, inst) in native {
        queries
            .entry(node)
            .or_default()
            .extend(crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).1);
    }
    for (&(node, _), producer) in &function.value_producers {
        queries
            .entry(node)
            .or_default()
            .extend(producer.arguments.iter().copied());
    }
    let initial = Set(eligible.iter().map(|r| (*r, None)).collect());
    let mut program = ReachingDefinitions::default();
    program.entry.push((entry, initial.clone()));
    program.edge.extend(edges.iter().copied());
    let nodes: BTreeSet<_> = edges
        .iter()
        .flat_map(|(a, b)| [*a, *b])
        .chain([entry])
        .collect();
    for node in nodes {
        match native.get(&node) {
            Some(inst) => program.definition.push((
                node,
                crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst)
                    .0
                    .filter(|r| eligible.contains(r)),
            )),
            None => program.unknown.push((node, initial.clone())),
        }
    }
    program.run();
    let states: BTreeMap<_, _> = program.before.into_iter().collect();
    let mut result = BindingPlan::default();
    let mut used: BTreeSet<_> =
        function
            .used_regs
            .iter()
            .copied()
            .chain(function.var_type_candidates.keys().copied())
            .chain(function.var_types.keys().copied())
            .chain(native.values().flat_map(|i| {
                let (d, u) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(i);
                d.into_iter().chain(u).collect::<Vec<_>>()
            }))
            .chain(function.node_statements.values().flatten().flat_map(
                crate::decompile::passes::clight_select::syntax::declarations::dependencies,
            ))
            .collect();
    used.extend(reserved);
    let mut next_name = RTLReg::MAX.min(Ident::MAX as RTLReg);
    for reg in eligible {
        let mut groups: Vec<BTreeSet<Node>> = definitions[&reg]
            .iter()
            .map(|n| BTreeSet::from([*n]))
            .collect();
        let mut reads = BTreeMap::<Node, BTreeSet<Node>>::new();
        let mut complete = true;
        for (&node, uses) in &queries {
            if !uses.contains(&reg) {
                continue;
            }
            let Some(state) = states.get(&node) else {
                complete = false;
                break;
            };
            let defs: BTreeSet<_> = state
                .iter()
                .filter_map(|(r, d)| (*r == reg).then_some(*d))
                .collect();
            if defs.is_empty() || defs.contains(&None) {
                complete = false;
                break;
            }
            let defs: BTreeSet<_> = defs.into_iter().flatten().collect();
            let mut merged = defs.clone();
            groups.retain(|g| {
                if !g.is_disjoint(&defs) {
                    merged.extend(g);
                    false
                } else {
                    true
                }
            });
            groups.push(merged);
            reads.insert(node, defs);
        }
        if !complete || groups.len() < 2 {
            continue;
        }
        groups.sort(); // Naming only. No ordering is used for a dataflow decision.
        for group in groups {
            while used.contains(&next_name) {
                next_name = next_name
                    .checked_sub(1)
                    .expect("C binding namespace exhausted");
            }
            let id = next_name;
            used.insert(id);
            result.bindings.insert(
                id,
                Binding {
                    native: reg,
                    definitions: group.clone(),
                },
            );
            for &node in &group {
                result.writes.insert((node, reg), id);
            }
            for (&node, defs) in &reads {
                if !group.is_disjoint(defs) {
                    result.reads.insert((node, reg), id);
                }
            }
        }
    }
    for fact in &graph.facts {
        if let Fact::Access {
            object,
            node,
            write,
            ..
        } = fact
        {
            let id = if *write {
                result.write(*node, *object)
            } else {
                result.read(*node, *object)
            };
            if id != *object {
                result.storage.insert((*node, *object, id));
            }
        }
    }
    result
}

fn map_declarations<T: Clone>(values: &mut HashMap<RTLReg, T>, plan: &BindingPlan) {
    let old = std::mem::take(values);
    for (r, value) in old {
        for id in plan.alternatives(r) {
            values.insert(id, value.clone());
        }
    }
}

pub(super) fn remap_graph(graph: &EvidenceGraph, plan: &BindingPlan) -> EvidenceGraph {
    let mut result = graph.clone();
    result.facts.clear();
    result.entities.clear();
    result.hypotheses.clear();
    for (&r, terms) in &graph.hypotheses {
        for id in plan.alternatives(r) {
            result.hypotheses.insert(id, terms.clone());
        }
    }
    for fact in &graph.facts {
        let mapped = match fact {
            Fact::Definition { node, value } => Fact::Definition {
                node: *node,
                value: plan.write(*node, *value),
            },
            Fact::Carrier { node, value, bits } => Fact::Carrier {
                node: *node,
                value: plan.write(*node, *value),
                bits: *bits,
            },
            Fact::Access {
                object,
                node,
                offset,
                write,
                chunk,
            } => Fact::Access {
                object: if *write {
                    plan.write(*node, *object)
                } else {
                    plan.read(*node, *object)
                },
                node: *node,
                offset: *offset,
                write: *write,
                chunk: *chunk,
            },
            Fact::ValueHint { value, ty } => {
                for id in plan.alternatives(*value) {
                    result.facts.insert(Fact::ValueHint {
                        value: id,
                        ty: ty.clone(),
                    });
                }
                continue;
            }
            _ => fact.clone(),
        };
        result.facts.insert(mapped);
    }
    for entity in &graph.entities {
        if let Entity::Value(r) = entity {
            for id in plan.alternatives(*r) {
                result.entities.insert(Entity::Value(id));
            }
        } else if let Entity::Access(node, reg, offset, write) = entity {
            result.entities.insert(Entity::Access(
                *node,
                if *write {
                    plan.write(*node, *reg)
                } else {
                    plan.read(*node, *reg)
                },
                *offset,
                *write,
            ));
        } else {
            result.entities.insert(entity.clone());
        }
    }
    result.unknown_values = graph
        .unknown_values
        .iter()
        .flat_map(|r| plan.alternatives(*r))
        .collect();
    result.unknown_storage = graph
        .unknown_storage
        .iter()
        .flat_map(|r| plan.alternatives(*r))
        .collect();
    result
}

fn apply(function: &mut FunctionData, plan: BindingPlan) {
    if plan.bindings.is_empty() {
        return;
    }
    for (&node, candidates) in &mut function.node_statements {
        for statement in candidates {
            *statement = plan.statement(node, statement);
        }
    }
    for (&node, candidates) in &mut function.analysis_candidates {
        *candidates = candidates.iter().map(|s| plan.statement(node, s)).collect();
    }
    for anchors in [&mut function.integer_anchors, &mut function.memory_anchors] {
        for (&node, inst) in anchors {
            *inst = plan.native(node, inst);
        }
    }
    for (&node, (reg, _)) in &mut function.flow_anchors.chunk {
        *reg = if plan.writes.contains_key(&(node, *reg)) {
            plan.write(node, *reg)
        } else {
            plan.read(node, *reg)
        };
    }
    for (&node, values) in &mut function.word_inputs {
        *values = values.iter().map(|r| plan.read(node, *r)).collect();
    }
    function.value_producers = std::mem::take(&mut function.value_producers)
        .into_iter()
        .map(|((node, r), mut p)| {
            p.arguments = Arc::new(p.arguments.iter().map(|r| plan.read(node, *r)).collect());
            ((node, plan.read(node, r)), p)
        })
        .collect();
    map_declarations(&mut function.var_types, &plan);
    map_declarations(&mut function.var_type_candidates, &plan);
    map_declarations(&mut function.var_decl_idx, &plan);
    map_declarations(&mut function.reg_to_mreg, &plan);
    function.used_regs = function
        .used_regs
        .iter()
        .flat_map(|r| plan.alternatives(*r))
        .collect();
    function.analysis_facts.project_bindings(&plan);
    eprintln!(
        "[type-bindings] fn={:#x} native-names={} bindings={} storage-events={}",
        function.address,
        plan.bindings
            .values()
            .map(|b| b.native)
            .collect::<BTreeSet<_>>()
            .len(),
        plan.bindings.len(),
        plan.storage.len()
    );
    PLAN.insert(&mut function.analysis_facts, plan);
}

pub(super) fn prepare(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut native = BTreeMap::<Node, Option<RTLInst>>::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        native
            .entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut owners = BTreeMap::<Node, BTreeSet<Address>>::new();
    for &(node, owner) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(owner);
    }
    let mut entries = BTreeMap::<Address, BTreeSet<Node>>::new();
    for &(owner, node) in db.rel_iter::<(Address, Node)>("rtl_function_entry") {
        entries.entry(owner).or_default().insert(node);
    }
    let edges: Vec<_> = db.rel_iter::<(Node, Node)>("rtl_succ").copied().collect();
    // The C converter has program-wide name-keyed maps. Allocate unique
    // transport names over the whole program, with a stable owner order.
    let mut reserved: BTreeSet<_> = functions
        .iter()
        .flat_map(|f| {
            f.used_regs
                .iter()
                .copied()
                .chain(f.var_types.keys().copied())
                .chain(f.var_type_candidates.keys().copied())
                .chain(f.node_statements.values().flatten().flat_map(
                    crate::decompile::passes::clight_select::syntax::declarations::dependencies,
                ))
        })
        .chain(native.values().flatten().flat_map(|i| {
            let (d, u) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(i);
            d.into_iter().chain(u).collect::<Vec<_>>()
        }))
        .collect();
    let mut ordered: Vec<_> = functions.iter_mut().collect();
    ordered.sort_by_key(|f| f.address);
    for function in ordered {
        if PLAN.get(&function.analysis_facts).is_some() {
            continue;
        }
        let Some(&entry) = entries
            .get(&function.address)
            .filter(|e| e.len() == 1)
            .and_then(|e| e.first())
        else {
            continue;
        };
        let sole = BTreeSet::from([function.address]);
        let instructions: BTreeMap<_, _> = native
            .iter()
            .filter_map(|(&node, inst)| {
                (owners.get(&node) == Some(&sole))
                    .then(|| inst.clone().map(|i| (node, i)))
                    .flatten()
            })
            .collect();
        let edges: Vec<_> = edges
            .iter()
            .copied()
            .filter(|(_, b)| {
                owners
                    .get(b)
                    .is_some_and(|os| os.contains(&function.address))
            })
            .collect();
        let plan = plan_with_reserved(function, &instructions, &edges, entry, &reserved);
        reserved.extend(plan.bindings.keys().copied());
        apply(function, plan);
    }
}

pub(super) fn publish(db: &mut DecompileDB, functions: &[FunctionData]) {
    let mut events = Vec::new();
    for function in functions {
        if let Some(plan) = PLAN.get(&function.analysis_facts) {
            events.extend(
                plan.storage
                    .iter()
                    .map(|&(node, original, binding)| (function.address, node, original, binding)),
            );
        }
    }
    events.sort_unstable();
    events.dedup();
    db.rel_set(
        "selection_binding_storage",
        events.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::c_pass::types::CType;
    use crate::decompile::passes::clight_select::syntax::bindings::*;
    use crate::decompile::passes::clight_select::{
        candtype::{CandType, Sign},
        solvers::integer_semantics,
        type_graph::TypeTerm,
    };
    use crate::x86::op::Operation;

    fn long() -> ClightType {
        ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default())
    }
    fn fixture() -> (FunctionData, BTreeMap<Node, RTLInst>, Vec<(Node, Node)>) {
        let mut f = FunctionData::new(1, "partition".into(), vec![], vec![], None, 0, 90, true);
        let instructions = BTreeMap::from([
            (
                90,
                RTLInst::Iop(Operation::Olongconst(7), Arc::new(vec![]), 3),
            ),
            (10, RTLInst::Iop(Operation::Omove, Arc::new(vec![3]), 4)),
            (
                20,
                RTLInst::Iop(Operation::Olongconst(0x1_0000_0001), Arc::new(vec![]), 3),
            ),
            (30, RTLInst::Iop(Operation::Omove, Arc::new(vec![3]), 5)),
        ]);
        f.node_statements = HashMap::from([
            (
                90,
                vec![ClightStmt::Sset(3, ClightExpr::EconstLong(7, long()))],
            ),
            (
                10,
                vec![ClightStmt::Sset(4, ClightExpr::Etempvar(3, long()))],
            ),
            (
                20,
                vec![ClightStmt::Sset(
                    3,
                    ClightExpr::EconstLong(0x1_0000_0001, long()),
                )],
            ),
            (
                30,
                vec![ClightStmt::Sset(5, ClightExpr::Etempvar(3, long()))],
            ),
        ]);
        f.integer_anchors = instructions.iter().map(|(&n, i)| (n, i.clone())).collect();
        f.var_types.insert(3, CandType::I64(Sign::Unsigned));
        f.var_type_candidates.insert(
            3,
            vec![CandType::I64(Sign::Unsigned), CandType::I32(Sign::Signed)],
        );
        f.used_regs.extend([3, 4, 5]);
        let mut graph = EvidenceGraph::default();
        graph.hypotheses.insert(
            3,
            BTreeSet::from([
                TypeTerm::from_candidate(CandType::I64(Sign::Unsigned), f.data_model),
                TypeTerm::from_candidate(CandType::I32(Sign::Signed), f.data_model),
            ]),
        );
        graph.facts.extend([
            Fact::Definition { node: 90, value: 3 },
            Fact::Definition { node: 20, value: 3 },
            Fact::Access {
                object: 3,
                node: 90,
                offset: -8,
                write: true,
                chunk: MemoryChunk::MInt32,
            },
            Fact::Access {
                object: 3,
                node: 10,
                offset: -8,
                write: false,
                chunk: MemoryChunk::MInt32,
            },
        ]);
        crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
            .insert(&mut f.analysis_facts, graph);
        (f, instructions, vec![(90, 10), (10, 20), (20, 30)])
    }

    #[test]
    fn independent_definitions_have_distinct_bindings_and_point_local_storage_origins() {
        let (mut f, instructions, edges) = fixture();
        let p = plan(&f, &instructions, &edges, 90);
        let first = p.write(90, 3);
        let second = p.write(20, 3);
        assert_ne!(first, second);
        assert_eq!(p.read(10, 3), first);
        assert_eq!(p.read(30, 3), second);
        assert_eq!(p.storage, BTreeSet::from([(90, 3, first), (10, 3, first)]));
        apply(&mut f, p);
        assert!(!f.var_type_candidates.contains_key(&3));
        assert_eq!(
            f.var_type_candidates[&first],
            f.var_type_candidates[&second]
        );
        assert!(matches!(f.integer_anchors[&20],RTLInst::Iop(_,_,r) if r == second));
        assert!(
            matches!(&f.node_statements[&30][0],ClightStmt::Sset(_,ClightExpr::Etempvar(r,_)) if *r as RTLReg == second)
        );
    }

    #[test]
    fn declaration_checker_still_refutes_a_wide_value_in_a_narrow_binding() {
        let (mut f, instructions, edges) = fixture();
        let p = plan(&f, &instructions, &edges, 90);
        let first = p.write(90, 3);
        let second = p.write(20, 3);
        apply(&mut f, p);
        let checker = integer_semantics::Validator::new();
        let declarations = HashMap::from([(first, CType::int()), (second, CType::int())]);
        assert_eq!(
            checker
                .check_at(
                    90,
                    &f.integer_anchors[&90],
                    &f.node_statements[&90][0],
                    &declarations,
                    &f
                )
                .verdict,
            integer_semantics::Verdict::Equivalent
        );
        assert_eq!(
            checker
                .check_at(
                    20,
                    &f.integer_anchors[&20],
                    &f.node_statements[&20][0],
                    &declarations,
                    &f
                )
                .verdict,
            integer_semantics::Verdict::Refuted
        );
    }

    #[test]
    fn joining_definitions_share_a_binding_but_an_independent_definition_can_split() {
        let (mut f, mut instructions, _) = fixture();
        instructions.insert(1, RTLInst::Inop);
        instructions.insert(
            40,
            RTLInst::Iop(Operation::Olongconst(2), Arc::new(vec![]), 3),
        );
        instructions.insert(50, RTLInst::Iop(Operation::Omove, Arc::new(vec![3]), 6));
        f.node_statements.insert(
            40,
            vec![ClightStmt::Sset(3, ClightExpr::EconstLong(2, long()))],
        );
        f.node_statements.insert(
            50,
            vec![ClightStmt::Sset(6, ClightExpr::Etempvar(3, long()))],
        );
        let edges = vec![
            (1, 90),
            (1, 20),
            (90, 30),
            (20, 30),
            (30, 10),
            (10, 40),
            (40, 50),
        ];
        let p = plan(&f, &instructions, &edges, 1);
        assert_ne!(p.write(90, 3), 3);
        assert_eq!(p.write(90, 3), p.write(20, 3));
        assert_eq!(p.read(30, 3), p.write(90, 3));
        assert_ne!(p.write(40, 3), p.write(90, 3));
    }

    #[test]
    fn bypass_unknown_and_first_iteration_reads_do_not_invent_a_definition() {
        for variant in 0..3 {
            let (f, mut instructions, mut edges) = fixture();
            let entry = match variant {
                0 => {
                    instructions.insert(1, RTLInst::Inop);
                    edges.extend([(1, 90), (1, 10)]);
                    1
                }
                1 => {
                    edges.retain(|e| *e != (90, 10));
                    edges.extend([(90, 60), (60, 10)]);
                    90
                }
                _ => {
                    edges.push((30, 90));
                    10
                }
            };
            assert!(
                plan(&f, &instructions, &edges, entry).bindings.is_empty(),
                "variant {variant}"
            );
        }
    }

    #[test]
    fn nested_sites_and_storage_owners_are_not_silently_partitioned() {
        let (mut f, instructions, edges) = fixture();
        f.node_statements.get_mut(&30).unwrap()[0] = ClightStmt::Sloop(
            Box::new(ClightStmt::Sset(5, ClightExpr::Etempvar(3, long()))),
            Box::new(ClightStmt::Sskip),
        );
        assert!(plan(&f, &instructions, &edges, 90).bindings.is_empty());
        let (mut f, instructions, edges) = fixture();
        let mut graph = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
            .get(&f.analysis_facts)
            .unwrap()
            .clone();
        graph.fixed.insert(3);
        crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
            .rebind(&mut f.analysis_facts, graph);
        assert!(plan(&f, &instructions, &edges, 90).bindings.is_empty());
    }

    #[test]
    fn occupied_binding_names_and_input_fact_order_do_not_change_the_partition() {
        let (mut f, instructions, mut edges) = fixture();
        f.used_regs.insert(RTLReg::MAX);
        let a = plan(&f, &instructions, &edges, 90);
        assert!(!a.bindings.contains_key(&RTLReg::MAX));
        edges.reverse();
        let b = plan(&f, &instructions, &edges, 90);
        assert_eq!(a.bindings, b.bindings);
        assert_eq!(a.reads, b.reads);
        assert_eq!(a.writes, b.writes);
    }

    #[test]
    fn binding_names_are_disjoint_between_function_preparations() {
        let (f, instructions, edges) = fixture();
        let first = plan(&f, &instructions, &edges, 90);
        let reserved = first.bindings.keys().copied().collect();
        let second = plan_with_reserved(&f, &instructions, &edges, 90, &reserved);
        assert_eq!(first.bindings.len(), second.bindings.len());
        assert!(second
            .bindings
            .keys()
            .all(|id| !first.bindings.contains_key(id)));
    }

    #[test]
    fn unmatched_c_definitions_and_addressable_locals_keep_their_identity() {
        for variant in 0..3 {
            let (mut f, instructions, edges) = fixture();
            let statement = match variant {
                0 => ClightStmt::Sset(3, ClightExpr::EconstLong(99, long())),
                1 => ClightStmt::Sset(
                    9,
                    ClightExpr::Eaddrof(
                        Box::new(ClightExpr::Etempvar(3, long())),
                        ClightType::Tpointer(Arc::new(long()), ClightAttr::default()),
                    ),
                ),
                _ => ClightStmt::Sassign(
                    ClightExpr::Evar(3, long()),
                    ClightExpr::EconstLong(99, long()),
                ),
            };
            f.node_statements.insert(10, vec![statement]);
            assert!(
                plan(&f, &instructions, &edges, 90).bindings.is_empty(),
                "variant {variant}"
            );
        }
    }

    #[test]
    fn preparing_a_partition_preserves_the_original_function_facts() {
        let (mut f, instructions, edges) = fixture();
        let original = f.clone();
        let p = plan(&f, &instructions, &edges, 90);
        apply(&mut f, p);
        assert!(
            crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
                .get(&original.analysis_facts)
                .unwrap()
                .hypotheses
                .contains_key(&3)
        );
        assert!(
            !crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
                .get(&f.analysis_facts)
                .unwrap()
                .hypotheses
                .contains_key(&3)
        );
        assert!(matches!(
            &original.node_statements[&90][0],
            ClightStmt::Sset(3, _)
        ));
    }

    #[test]
    fn artifact_owners_project_read_and_write_identities_without_a_central_module_list() {
        let (mut f, instructions, edges) = fixture();
        let key = ArtifactKey::<(Node, RTLReg, RTLReg)>::projected(
            "independent-analysis",
            |&(node, src, dst), plan| (node, plan.read(node, src), plan.write(node, dst)),
        );
        key.insert(&mut f.analysis_facts, (20, 3, 3));
        let retained = f.analysis_facts.clone();
        let p = plan(&f, &instructions, &edges, 90);
        let expected = (20, p.read(20, 3), p.write(20, 3));
        assert_ne!(expected.1, expected.2);
        apply(&mut f, p);
        assert_eq!(key.get(&f.analysis_facts), Some(&expected));
        assert_eq!(key.get(&retained), Some(&(20, 3, 3)));
    }

    #[test]
    fn type_flow_is_recomputed_after_separating_an_unrelated_writer() {
        use crate::decompile::passes::clight_select::solvers::integer_semantics::CopyValue;
        use crate::decompile::passes::clight_select::{
            solvers::transfers,
            syntax::{type_evidence, type_flow, Component},
        };
        let (mut f, mut instructions, edges) = fixture();
        // Start from raw relation evidence, not the fixture's prepared graph.
        f.analysis_facts = Default::default();
        f.param_regs = vec![1];
        f.param_types = vec![ParamType::Typed(XType::Xint)];
        instructions.insert(90, RTLInst::Iop(Operation::Omove, Arc::new(vec![1]), 3));
        f.node_statements.insert(
            90,
            vec![ClightStmt::Sset(3, ClightExpr::Etempvar(1, long()))],
        );
        let copies = [(90, 1, 3, 32), (10, 3, 4, 32), (30, 3, 5, 64)]
            .into_iter()
            .map(|(node, source, destination, bits)| {
                (
                    node,
                    CopyValue {
                        node,
                        source,
                        destination,
                        bits,
                        storage: false,
                        memory_input: None,
                    },
                )
            })
            .collect();
        transfers::COPIES.insert(&mut f.analysis_facts, copies);
        let mut db = DecompileDB::default();
        for (&node, inst) in &instructions {
            db.rel_push("rtl_inst", (node, inst.clone()));
            db.rel_push("instr_in_function", (node, f.address));
        }
        for edge in edges {
            db.rel_push("rtl_succ", edge);
        }
        db.rel_push("rtl_function_entry", (f.address, 90_u64));
        db.rel_push(
            "ltl_inst",
            (
                90_u64,
                LTLInst::Lop(
                    Operation::Omove,
                    Arc::new(vec![crate::mreg::Mreg::CX]),
                    crate::mreg::Mreg::AX,
                ),
            ),
        );
        db.rel_push(
            "machine_register_write_view",
            (90_u64, crate::mreg::Mreg::AX, 32_u32),
        );
        db.rel_push("rtl_available_value", (f.address, 10_u64, 3_u64, 90_u64));
        db.rel_push(
            "type_storage_access",
            (f.address, 90_u64, 3_u64, -8_i64, true, MemoryChunk::MInt32),
        );
        db.rel_push(
            "type_storage_access",
            (f.address, 20_u64, 3_u64, -8_i64, true, MemoryChunk::Unknown),
        );

        let mut merged = f.clone();
        type_evidence::collect(&db, std::slice::from_mut(&mut merged));
        assert!(!type_flow::HINTS
            .get(&merged.analysis_facts)
            .unwrap()
            .iter()
            .any(|h| h.value == 4));

        crate::decompile::passes::clight_select::syntax::type_recovery::TypeRecovery
            .prepare(&db, std::slice::from_mut(&mut f));
        let p = PLAN.get(&f.analysis_facts).unwrap();
        let first = p.write(90, 3);
        let second = p.write(20, 3);
        assert_ne!(first, second);
        assert!(f.word_inputs[&10].contains(&first));
        assert!(!f
            .word_inputs
            .get(&30)
            .is_some_and(|inputs| inputs.contains(&second)));
        assert_eq!(f.value_producers[&(10, first)].definition, 90);
        assert!(!f.value_producers.contains_key(&(10, 3)));
        let graph = type_evidence::GRAPH.get(&f.analysis_facts).unwrap();
        assert!(!graph.unknown_storage.contains(&first));
        assert!(graph.unknown_storage.contains(&second));
        let integer = TypeTerm::from_candidate(CandType::I32(Sign::Signed), f.data_model);
        assert!(type_flow::HINTS
            .get(&f.analysis_facts)
            .unwrap()
            .iter()
            .any(|h| h.value == 4 && h.ty() == &integer));
        assert!(!type_flow::HINTS
            .get(&f.analysis_facts)
            .unwrap()
            .iter()
            .any(|h| h.value == 5));
    }
}
