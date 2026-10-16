//! Demand-driven validation of concrete declaration changes.
//!
//! Evidence ranks hypotheses; it does not discharge a representation change.
//! A missing proof is not a counterexample, but it cannot authorize changing
//! a representation. Evidence keeps a hypothesis in the domain and ranks it;
//! every nonlegacy integer choice still needs complete transfer coverage.
//! Check the selected profile at every affected native definition/use, cache
//! by its declaration dependencies, and learn clauses in the same Optimize.
use crate::decompile::passes::clight_select::solvers::obligations::{Check, Obligations, Validator, Verdict};
use crate::decompile::passes::clight_select::type_graph::{Fact, TypeTerm};
use super::Checker;
use crate::decompile::passes::clight_select::syntax::{ArtifactKey, Artifacts, FunctionContext};
use crate::decompile::passes::c_pass::types::CType;
use crate::x86::types::{Node, RTLReg};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use z3::ast::{Ast, Bool};
use z3::{Model, Optimize};

pub(crate) const VALIDATED: ArtifactKey<BTreeSet<RTLReg>> =
    ArtifactKey::new("validated-type-transfers");
pub(crate) const PRESERVED: ArtifactKey<BTreeMap<RTLReg, TypeTerm>> =
    ArtifactKey::new("type-proof-bindings");
pub(crate) const FALLBACK_PRESERVED: ArtifactKey<BTreeSet<RTLReg>> =
    ArtifactKey::new("type-counterexample-bindings");

struct Cached {
    inputs: Vec<(RTLReg, Option<CType>)>,
    check: Check,
}

/// Complete declaration-local proof, guarded by every selected definition,
/// use and declaration it depended on. It is not an independent type vote.
struct Certificate {
    register: RTLReg,
    term: TypeTerm,
    guard: Bool,
    declarations: BTreeMap<RTLReg, TypeTerm>,
    sites: BTreeMap<Node, Option<usize>>,
}

pub(crate) struct Profiles<'a> {
    cx: FunctionContext<'a>,
    obligations: Obligations<'a>,
    sites: BTreeMap<Node, BTreeSet<RTLReg>>,
    native_definitions: BTreeMap<Node, BTreeSet<RTLReg>>,
    checker: Validator,
    cache: HashMap<(Node, usize, usize), Vec<Cached>>,
    coupled: BTreeSet<Node>,
    validated: BTreeSet<RTLReg>,
    unproved: BTreeSet<RTLReg>,
    optimizer: &'a Optimize,
    repair_preferences: BTreeSet<Node>,
    learned: Vec<Bool>,
    preserved: BTreeMap<RTLReg, TypeTerm>,
    refuted_registers: BTreeSet<RTLReg>,
    counts: [usize; 4],
    hits: usize,
    certificates: Vec<Certificate>,
}

impl<'a> Profiles<'a> {
    pub(crate) fn start(
        cx: &FunctionContext<'a>,
        obligations: Obligations<'a>,
        optimizer: &'a Optimize,
    ) -> Option<Self> {
        if !cx.concrete_declarations.0.values().any(|choice| {
            choice.alternatives.iter().any(|(id, _)| {
                !choice.legacy.contains(id) && cx.concrete_declarations.term(*id).is_integer()
            })
        }) {
            return None;
        }
        let mut sites = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
        for (&node, candidates) in &cx.function.node_statements {
            sites.entry(node).or_default().extend(
                candidates
                    .iter()
                    .flat_map(crate::decompile::passes::clight_select::syntax::declarations::dependencies),
            );
        }
        let mut native_definitions = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
        if let Some(graph) = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH.get(&cx.function.analysis_facts) {
            for fact in &graph.facts {
                if let Fact::Definition { node, value } = fact {
                    sites.entry(*node).or_default().insert(*value);
                    native_definitions.entry(*node).or_default().insert(*value);
                }
            }
        }
        for (&node, checks) in &obligations.0 {
            sites
                .entry(node)
                .or_default()
                .extend(checks.iter().flat_map(|c| c.native_registers()));
        }
        // A producer check may read operands absent from the selected C AST.
        for (&(node, reg), producer) in &cx.function.value_producers {
            sites.entry(node).or_default().insert(reg);
            sites
                .entry(node)
                .or_default()
                .extend(producer.arguments.iter().copied());
        }
        Some(Self {
            cx: *cx,
            obligations,
            sites,
            native_definitions,
            checker: Validator::new(),
            cache: HashMap::new(),
            coupled: BTreeSet::new(),
            validated: BTreeSet::new(),
            unproved: BTreeSet::new(),
            optimizer,
            repair_preferences: BTreeSet::new(),
            learned: Vec::new(),
            preserved: BTreeMap::new(),
            refuted_registers: BTreeSet::new(),
            counts: [0; 4],
            hits: 0,
            certificates: Vec::new(),
        })
    }

    fn declarations(&self, model: &Model) -> HashMap<RTLReg, CType> {
        let mut result = crate::decompile::passes::clight_select::solvers::semantics::integer_declarations(self.cx.function);
        let fixed = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH
            .get(&self.cx.function.analysis_facts)
            .map(|g| &g.fixed_storage);
        for &reg in self.cx.registers {
            if fixed.is_some_and(|fixed| fixed.contains(&reg)) {
                continue;
            }
            result.insert(
                reg,
                self.cx
                    .concrete_declarations
                    .render(
                        self.cx.types,
                        model,
                        &self.cx.declarations[&reg],
                        reg,
                        self.cx.function,
                        false,
                    )
                    .to_c(self.cx.function.data_model),
            );
        }
        result
    }

    fn changed(&self, model: &Model) -> BTreeSet<RTLReg> {
        self.cx
            .concrete_declarations
            .0
            .iter()
            .filter_map(|(&reg, choice)| {
                choice
                    .alternatives
                    .iter()
                    .any(|(id, selected)| {
                        !choice.legacy.contains(id)
                            && self.cx.concrete_declarations.term(*id).is_integer()
                            && model.eval(selected, true).and_then(|b| b.as_bool()) == Some(true)
                    })
                    .then_some(reg)
            })
            .collect()
    }

    /// Origin evidence is not a representation invariant. Existing and newly
    /// constructed hypotheses have the same admission obligation.
    fn requires_certificate(&self, model: &Model, reg: RTLReg) -> bool {
        self.cx
            .concrete_declarations
            .0
            .get(&reg)
            .is_some_and(|choice| {
                choice.alternatives.iter().any(|(id, selected)| {
                    !choice.legacy.contains(id)
                        && model.eval(selected, true).and_then(|b| b.as_bool()) == Some(true)
                })
            })
    }

    fn guard(&self, model: &Model, registers: &BTreeSet<RTLReg>) -> Bool {
        Bool::and(
            &registers
                .iter()
                .filter_map(|reg| {
                    if let Some(term) = self.cx.concrete_declarations.selected(model, *reg) {
                        Some(Bool::or(
                            &self
                                .cx
                                .concrete_declarations
                                .options(*reg)
                                .filter_map(|(candidate, b)| {
                                    (candidate == term).then_some(b.clone())
                                })
                                .collect::<Vec<_>>(),
                        ))
                    } else {
                        self.cx
                            .declarations
                            .get(reg)
                            .and_then(|v| model.eval(v, true).map(|value| v._eq(value)))
                    }
                })
                .collect::<Vec<_>>(),
        )
    }
}

impl Checker for Profiles<'_> {
    fn round_limit(&self) -> usize {
        // Linear search-work budget in the concrete domain, not a Cartesian
        // profile cap. Exhaustion disables changes; it never certifies them.
        self.cx
            .concrete_declarations
            .0
            .values()
            .map(|c| c.alternatives.len())
            .sum()
    }

    fn check(&mut self, answer: &Model) -> super::Verdict {

        self.inspect(answer).into()

    }

    fn coupled_nodes(&self) -> BTreeSet<Node> {
        self.coupled.clone()
    }

    fn fallback_constraints(&self) -> Vec<Bool> {
        self.cx
            .concrete_declarations
            .0
            .iter()
            .flat_map(|(&reg, choice)| {
                choice.alternatives.iter().filter_map(move |(id, b)| {
                    (!choice.legacy.contains(id)
                        && self.cx.concrete_declarations.term(*id).is_integer())
                    .then(|| {
                        b.implies(Bool::or(
                            &self
                                .certificates
                                .iter()
                                .filter(|c| {
                                    c.register == reg
                                        && &c.term == self.cx.concrete_declarations.term(*id)
                                })
                                .map(|c| c.guard.clone())
                                .collect::<Vec<_>>(),
                        ))
                    })
                })
            })
            .chain(self.learned.iter().cloned())
            .collect()
    }

    fn finish_fallback(
        mut self: Box<Self>,
        model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    ) {
        self.validated.clear();
        self.preserved.clear();
        self.unproved.clear();
        if let Some(model) = model {
            for certificate in &self.certificates {
                if model
                    .eval(&certificate.guard, true)
                    .and_then(|b| b.as_bool())
                    != Some(true)
                {
                    continue;
                }
                self.validated.insert(certificate.register);
                self.preserved.extend(
                    certificate
                        .declarations
                        .iter()
                        .map(|(&r, t)| (r, t.clone())),
                );
                let declarations = certificate
                    .declarations
                    .iter()
                    .map(|(&r, t)| (r, t.to_c(self.cx.function.data_model)))
                    .collect();
                let dependencies = certificate.declarations.keys().copied().collect();
                for (&node, &choice) in &certificate.sites {
                    if let Some(ci) = choice {
                        self.cx.concrete_declarations.record_profile(
                            node,
                            ci,
                            certificate.guard.clone(),
                            &dependencies,
                            &declarations,
                            self.cx.function.data_model,
                        );
                    }
                }
            }
        }
        eprintln!(
            "[type-certificate-fallback] fn={:#x} certificates={} retained={}",
            self.cx.function.address,
            self.certificates.len(),
            self.validated.len()
        );
        self.finish(model, reason, results);
    }

    fn finish(
        self: Box<Self>,
        model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    ) {
        eprintln!("[type-transfer-validation] fn={:#x} equivalent={} refuted={} unsupported={} unknown={} cache-hits={} repair-guides={} committed={} uncertified={} status={}",
            self.cx.function.address, self.counts[0], self.counts[1], self.counts[2], self.counts[3],
            self.hits, self.repair_preferences.len(), if model.is_some() { self.validated.len() } else { 0 },
            if model.is_some() { self.unproved.len() } else { 0 }, reason);
        VALIDATED.insert(
            results,
            if model.is_some() {
                self.validated
            } else {
                BTreeSet::new()
            },
        );
        PRESERVED.insert(
            results,
            if model.is_some() {
                self.preserved
            } else {
                BTreeMap::new()
            },
        );
        FALLBACK_PRESERVED.insert(results, self.refuted_registers);
    }
}

impl Profiles<'_> {

    fn inspect(&mut self, model: &Model) -> Result<Vec<Bool>, &'static str> {
        let declarations = self.declarations(model);
        let changed = self.changed(model);
        let mut clauses = Vec::new();
        let mut proofs = Vec::new();
        let mut coupled = BTreeSet::new();
        let mut checked = BTreeSet::new();
        let mut preserved = BTreeMap::new();
        let mut unproved = BTreeSet::new();
        let mut rejected = BTreeSet::<RTLReg>::new();
        let mut local_proofs = BTreeMap::<Node, (Option<usize>, Bool, BTreeSet<RTLReg>)>::new();
        let trace = std::env::var("MANIFOLD_DUMP_CANDS")
            .is_ok_and(|name| !name.is_empty() && self.cx.function.name.contains(&name));
        // A use check assumes a representation relation for its inputs. It
        // cannot establish that same relation from itself: require native
        // definitions (parameters/interfaces are fixed by preparation).
        for &reg in &changed {
            if !self
                .native_definitions
                .values()
                .any(|definitions| definitions.contains(&reg))
            {
                unproved.insert(reg);
                if self.requires_certificate(model, reg) {
                    if trace {
                        eprintln!(
                            "[type-transfer-gap] fn={} reg={} no native definition",
                            self.cx.function.name, reg
                        );
                    }
                    clauses.push(self.guard(model, &BTreeSet::from([reg])).not());
                }
            }
        }
        for (&node, dependencies) in &self.sites {
            let affected: BTreeSet<_> = dependencies.intersection(&changed).copied().collect();
            if affected.is_empty() {
                continue;
            }
            self.coupled.insert(node);
            let candidates = self.cx.function.node_statements.get(&node);
            let choice = match self.cx.selections.get(&node) {
                Some(bs) => bs
                    .iter()
                    .position(|b| model.eval(b, true).and_then(|v| v.as_bool()) == Some(true)),
                None => candidates.filter(|c| !c.is_empty()).map(|_| 0),
            };
            let selection_guard = self
                .cx
                .selections
                .get(&node)
                .map(|bs| match choice {
                    Some(ci) => bs[ci].clone(),
                    None => Bool::or(bs).not(),
                })
                .unwrap_or_else(|| Bool::from_bool(true));
            let mut guard_dependencies = dependencies.clone();
            let Some((ci, statement)) =
                choice.and_then(|ci| candidates.and_then(|c| c.get(ci)).map(|s| (ci, s)))
            else {
                // Omitting a native definition does not remove its declaration
                // obligation. A different structural world may restore it.
                // A use-only comparison absorbed by this world's switch has
                // no C read here. Check the surviving switch discriminant;
                // do not require a flat CFG just to recover its integer type.
                let lost_definition = self
                    .native_definitions
                    .get(&node)
                    .is_some_and(|definitions| !definitions.is_disjoint(&affected));
                if lost_definition {
                    unproved.extend(&affected);
                    if affected
                        .iter()
                        .any(|reg| self.requires_certificate(model, *reg))
                    {
                        clauses.push(
                            Bool::and(&[selection_guard, self.guard(model, dependencies)]).not(),
                        );
                    }
                } else {
                    // Absence of a use is itself conditional on this choice.
                    local_proofs.insert(node, (None, selection_guard, BTreeSet::new()));
                }
                continue;
            };
            let mut covered = BTreeSet::new();
            let mut invalid = false;
            let mut refuted = false;
            let mut proof_inputs = BTreeSet::new();
            for (oi, obligation) in self
                .obligations
                .0
                .get(&node)
                .into_iter()
                .flatten()
                .enumerate()
            {
                let inputs: Vec<_> = dependencies
                    .iter()
                    .map(|reg| (*reg, declarations.get(reg).cloned()))
                    .collect();
                let key = (node, ci, oi);
                let cached = self
                    .cache
                    .get(&key)
                    .and_then(|entries| entries.iter().find(|e| e.inputs == inputs));
                let check = if let Some(cached) = cached {
                    self.hits += 1;
                    cached.check.clone()
                } else {
                    let check = self.checker.check(
                        obligation.as_ref(),
                        statement,
                        &declarations,
                        self.cx.function,
                    );
                    // Do not memoize a proof unless its actual dependencies
                    // are covered by the key (including inlined producers).
                    if check.registers.is_subset(dependencies) {
                        self.cache.entry(key).or_default().push(Cached {
                            inputs,
                            check: check.clone(),
                        });
                    }
                    self.counts[match check.verdict {
                        Verdict::Equivalent => 0,
                        Verdict::Refuted => 1,
                        Verdict::Unsupported => 2,
                        Verdict::Unknown => 3,
                    }] += 1;
                    check
                };
                guard_dependencies.extend(&check.registers);
                let relevant = !check.registers.is_disjoint(&affected)
                    || !obligation.native_registers().is_disjoint(&affected);
                if !relevant {
                    continue;
                }
                match check.verdict {
                    Verdict::Equivalent => {
                        proof_inputs.extend(&check.registers);
                        for reg in &check.registers {
                            if let Some(term) = declarations
                                .get(reg)
                                .and_then(|ty| TypeTerm::from_c(ty, self.cx.function.data_model))
                            {
                                preserved.insert(*reg, term);
                            }
                        }
                        covered.extend(check.registers.intersection(&affected).copied());
                        proofs.push((
                            node,
                            ci,
                            self.guard(model, &check.registers),
                            check.registers,
                        ));
                    }
                    Verdict::Refuted => {
                        refuted = true;
                        if std::env::var("MANIFOLD_DUMP_CANDS").is_ok_and(|name| {
                            !name.is_empty() && self.cx.function.name.contains(&name)
                        }) {
                            eprintln!("[type-transfer-refutation] fn={} node={:#x} family={} candidate={} inputs={:?} witness={:?}",
                                self.cx.function.name, node, obligation.family(), ci,
                                check.registers.iter().map(|reg| (*reg, declarations.get(reg))).collect::<Vec<_>>(), check.witness);
                        }
                        // Generalize only over the declarations the witness
                        // actually read. Unrelated address/input classes must
                        // not let Optimize evade a lost destination bit.
                        guard_dependencies = check.registers.union(&affected).copied().collect();
                        self.refuted_registers.extend(&guard_dependencies);
                        // Search only the siblings of an actual counterexample
                        // under this profile, instead of all type combinations.
                        // A positive local proof guides preference; it never
                        // exempts another definition/use from validation.
                        if !self.repair_preferences.contains(&node) {
                            if let (Some(candidates), Some(choices)) =
                                (candidates, self.cx.selections.get(&node))
                            {
                                let mut repairs = Vec::new();
                                for (index, candidate) in
                                    candidates.iter().enumerate().filter(|(i, _)| *i != ci)
                                {
                                    let repair = self.checker.check(
                                        obligation.as_ref(),
                                        candidate,
                                        &declarations,
                                        self.cx.function,
                                    );
                                    self.counts[match repair.verdict {
                                        Verdict::Equivalent => 0,
                                        Verdict::Refuted => 1,
                                        Verdict::Unsupported => 2,
                                        Verdict::Unknown => 3,
                                    }] += 1;
                                    if repair.verdict == Verdict::Equivalent {
                                        let context: BTreeSet<_> =
                                            repair.registers.union(&affected).copied().collect();
                                        repairs.push(Bool::and(&[
                                            choices[index].clone(),
                                            self.guard(model, &context),
                                        ]));
                                    }
                                }
                                if !repairs.is_empty() {
                                    self.cx.soft_groups.assert_soft(
                                        self.optimizer,
                                        &Bool::or(&repairs),
                                        self.cx.primary_unit,
                                    );
                                    self.repair_preferences.insert(node);
                                }
                            }
                        }
                        invalid = true;
                        break;
                    }
                    Verdict::Unsupported | Verdict::Unknown => {
                        // Another independent obligation may establish the
                        // transfer (e.g. a scalar-cell access vs its RTL move).
                    }
                }
            }
            if !invalid {
                for &reg in affected.difference(&covered) {
                    let native_definition = self
                        .native_definitions
                        .get(&node)
                        .is_some_and(|defs| defs.contains(&reg));
                    if native_definition
                        || !crate::decompile::passes::clight_select::solvers::type_projection::integer_view_use(
                            statement,
                            reg,
                            &declarations,
                            self.cx.function,
                            self.cx.names,
                        )
                    {
                        unproved.insert(reg);
                        if self.requires_certificate(model, reg) {
                            if trace {
                                eprintln!("[type-transfer-gap] fn={} node={:#x} reg={} type={:?} native-definition={} stmt={:?}", self.cx.function.name, node, reg, declarations.get(&reg), native_definition, statement);
                            }
                            invalid = true;
                            break;
                        }
                        continue;
                    }
                    // The substitution theorem may rely on the receiving
                    // declaration's implicit assignment conversion too.
                    let mut bindings = vec![reg];
                    if let crate::x86::types::ClightStmt::Sset(destination, _) =
                        crate::decompile::passes::clight_select::solvers::memory_theory::primitive(statement)
                    {
                        bindings.push(*destination as RTLReg);
                    }
                    for binding in bindings {
                        proof_inputs.insert(binding);
                        if let Some(term) = declarations
                            .get(&binding)
                            .and_then(|ty| TypeTerm::from_c(ty, self.cx.function.data_model))
                        {
                            preserved.insert(binding, term);
                        }
                    }
                }
            }
            if invalid {
                rejected.extend(&affected);
                let clause =
                    Bool::and(&[selection_guard, self.guard(model, &guard_dependencies)]).not();
                // Missing proof may reject a search profile, but is not a
                // machine counterexample. Fallback admission below separately
                // requires a complete positive certificate for every change.
                if refuted {
                    self.learned.push(clause.clone());
                }
                clauses.push(clause);
            } else {
                checked.extend(&affected);
                coupled.insert(node);
                local_proofs.insert(
                    node,
                    (
                        choice,
                        Bool::and(&[selection_guard, self.guard(model, &proof_inputs)]),
                        proof_inputs,
                    ),
                );
            }
        }
        // Another declaration's failure must not discard an otherwise
        // complete proof. Its dependencies remain guards, never assumptions
        // that the fallback is allowed to forget.
        for &register in checked
            .difference(&unproved)
            .filter(|r| !rejected.contains(*r))
        {
            let Some(term) = self
                .cx
                .concrete_declarations
                .selected(model, register)
                .cloned()
            else {
                continue;
            };
            let mut guards = vec![self.guard(model, &BTreeSet::from([register]))];
            let mut inputs = BTreeSet::from([register]);
            let mut sites = BTreeMap::new();
            let mut complete = true;
            for (&node, dependencies) in &self.sites {
                if !dependencies.contains(&register) {
                    continue;
                }
                let Some((choice, guard, dependencies)) = local_proofs.get(&node) else {
                    complete = false;
                    break;
                };
                guards.push(guard.clone());
                inputs.extend(dependencies);
                sites.insert(node, *choice);
            }
            if !complete {
                continue;
            }
            let bindings: BTreeMap<_, _> = inputs
                .iter()
                .filter_map(|r| {
                    declarations
                        .get(r)
                        .and_then(|ty| TypeTerm::from_c(ty, self.cx.function.data_model))
                        .map(|ty| (*r, ty))
                })
                .collect();
            if bindings.len() != inputs.len() {
                continue;
            }
            if self.certificates.iter().any(|c| {
                c.register == register
                    && c.term == term
                    && c.declarations == bindings
                    && c.sites == sites
            }) {
                continue;
            }
            self.certificates.push(Certificate {
                register,
                term,
                guard: Bool::and(&guards),
                declarations: bindings,
                sites,
            });
        }
        if clauses.is_empty() {
            self.validated = checked.difference(&unproved).copied().collect();
            self.unproved = unproved;
            self.preserved = preserved;
            self.coupled.extend(coupled);
            for (node, ci, guard, registers) in proofs {
                self.cx.concrete_declarations.record_profile(
                    node,
                    ci,
                    guard,
                    &registers,
                    &declarations,
                    self.cx.function.data_model,
                );
            }
        }
        Ok(clauses)
    }
}
