use crate::decompile::passes::clight_select::syntax::solve::*;
use crate::decompile::passes::clight_select::syntax::ctyping;
use crate::decompile::passes::clight_select::query::{
    CommittedFunctionInterface, InterfaceAuthority,
};
use crate::x86::types::{
    ClightAttr, ClightFloatSize, ClightIntSize, ClightSignedness, ClightUnaryOp,
};
use std::sync::Arc;
use z3::ast::Ast; // for `.simplify()` on Bool, used in tests below

fn synthetic_ids<const N: usize>() -> [u64; N] {
    std::array::from_fn(|index| index as u64 + 1)
}

#[test]
fn exact_repick_cannot_trade_a_hard_constraint_for_frontend_legality() {
    let mut func = FunctionData::new(1, "hard_repick".into(), vec![], vec![], None, 0, 2, true);
    func.return_type = ClightType::Tlong(ClightSignedness::Signed, a());
    func.node_statements
        .insert(2, vec![ClightStmt::Sskip, ClightStmt::Sreturn(None)]);
    let opt = Optimize::new();
    let backend = OptimizeBackend::new(&opt);
    let mut built =
        build_function_constraints(TypeDt::build(), &func, &HashMap::new(), &[], &backend);
    opt.assert(&built.selvar[&2][0].not());
    built.recorded.get_mut(&2).unwrap()[0].push((Some(Bool::from_bool(false)), u64::MAX));
    assert_eq!(opt.check(&[]), SatResult::Sat);
    let model = opt.get_model().unwrap();
    let (choices, _, _, _) = extract_selection(
        &model,
        &built,
        &func,
        &HashMap::new(),
        true,
        &BTreeSet::new(),
    );
    assert_eq!(choices[&2], Some(1));
}

#[test]
fn theory_models_are_not_independently_repicked() {
    let mut func = FunctionData::new(1, "theory_pick".into(), vec![], vec![], None, 0, 2, true);
    func.node_statements
        .insert(2, vec![ClightStmt::Sskip, ClightStmt::Sskip]);
    let opt = Optimize::new();
    let backend = OptimizeBackend::new(&opt);
    let built = build_function_constraints(TypeDt::build(), &func, &HashMap::new(), &[], &backend);
    opt.assert(&built.selvar[&2][1]);
    assert_eq!(opt.check(&[]), SatResult::Sat);
    let (choices, _, _, _) = extract_selection(
        &opt.get_model().unwrap(),
        &built,
        &func,
        &HashMap::new(),
        false,
        &BTreeSet::new(),
    );
    assert_eq!(choices[&2], Some(1));
}

#[test]
fn production_selects_defined_modular_arithmetic_over_its_signed_sibling() {
    let mut func = FunctionData::new(
        10,
        "integer_semantics".into(),
        vec![],
        vec![],
        None,
        0,
        20,
        true,
    );
    for reg in [1, 2, 3] {
        func.var_type_candidates
            .insert(reg, vec![CandType::I64(Sign::Signed)]);
    }
    let expr = |sign| {
        let ty = ClightType::Tlong(sign, a());
        ClightStmt::Sset(
            3,
            ClightExpr::Ebinop(
                ClightBinaryOp::Oadd,
                Box::new(ClightExpr::Etempvar(1, ty.clone())),
                Box::new(ClightExpr::Etempvar(2, ty.clone())),
                ty,
            ),
        )
    };
    func.node_statements.insert(
        20,
        vec![
            expr(ClightSignedness::Signed),
            expr(ClightSignedness::Unsigned),
        ],
    );
    func.integer_anchors.insert(
        20,
        crate::x86::types::RTLInst::Iop(crate::x86::op::Operation::Oaddl, Arc::new(vec![1, 2]), 3),
    );
    let (choices, _, _, _, _) = solve_function(&func, &HashMap::new(), false);
    assert_eq!(choices[&20], Some(1));
}

fn a() -> ClightAttr {
    ClightAttr::default()
}

fn committed_param(address: Address, xtype: XType) -> CommittedInterfaces {
    let mut committed = CommittedInterfaces::default();
    committed.functions.insert(
        address as Ident,
        CommittedFunctionInterface {
            signature: CalleeSignature {
                param_count: 1,
                return_type: XType::Xvoid,
                param_types: vec![xtype],
                is_varargs: false,
            },
            authority: InterfaceAuthority::Reconciled,
        },
    );
    committed
}

#[test]
fn structure_world_selection_never_mixes_correlated_node_candidates() {
    let func_addr = 0x1000;
    let first = 0x1010;
    let second = 0x1020;
    let structured = crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_STRUCTURED;
    let flat = crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_FLAT;
    let mut func = FunctionData::new(
        func_addr,
        "world_atomicity".into(),
        Vec::new(),
        Vec::new(),
        None,
        0,
        first,
        true,
    );
    func.structure_worlds = vec![structured, flat];
    func.authoritative_structure_world = structured;
    // Opposite local candidate orders make an independent node selector
    // prefer the unsound mixed pair.  World masks must force (0, 1) or
    // (1, 0), never (0, 0) or (1, 1).
    func.node_statements
        .insert(first, vec![ClightStmt::Sgoto(1), ClightStmt::Sgoto(2)]);
    func.candidate_structure_worlds.insert(
        first,
        vec![BTreeSet::from([structured]), BTreeSet::from([flat])],
    );
    func.node_statements
        .insert(second, vec![ClightStmt::Sgoto(3), ClightStmt::Sgoto(4)]);
    func.candidate_structure_worlds.insert(
        second,
        vec![BTreeSet::from([flat]), BTreeSet::from([structured])],
    );

    let (choices, _, _, selected_world, _) = solve_function(&func, &HashMap::new(), false);
    let first_choice = choices[&first].expect("first node is active");
    let second_choice = choices[&second].expect("second node is active");
    assert!(func.candidate_structure_worlds[&first][first_choice].contains(&selected_world));
    assert!(func.candidate_structure_worlds[&second][second_choice].contains(&selected_world));
    assert!(matches!((first_choice, second_choice), (0, 1) | (1, 0)));
}

#[test]
fn dirty_unsat_preserves_stage_a_candidate_indices() {
    let [address] = synthetic_ids();
    let reg = 11;
    let mut func = FunctionData::new(
        address,
        "unsat_dirty".into(),
        vec![reg],
        vec![ParamType::Integer],
        None,
        0,
        1,
        true,
    );
    func.var_type_candidates
        .insert(reg, vec![CandType::I64(Sign::Signed), CandType::PtrVoid]);
    let before = func.var_type_candidates.clone();
    let stage_a = ProgramSelectionState {
        candidate_idx: HashMap::new(),
        structure_world: HashMap::new(),
        var_decl_idx: [((address, reg), 1)].into_iter().collect(),
        var_type_override: HashMap::new(),
        analysis_results: BTreeMap::new(),
    };
    let (state, stats) = resolve_dirty_functions(
        std::slice::from_mut(&mut func),
        &HashMap::new(),
        &stage_a,
        &[address].into_iter().collect(),
        &committed_param(address, XType::Xvoid),
        &BTreeMap::new(),
        false,
    );
    assert_eq!(stats.fallback_count, 1);
    assert_eq!(func.var_type_candidates, before);
    assert_eq!(state.var_decl_idx, stage_a.var_decl_idx);
    assert_eq!(state.candidate_idx, stage_a.candidate_idx);
}

#[test]
fn dirty_float_pin_overrides_stage_a_float_pruning() {
    let [address] = synthetic_ids();
    let reg = 12;
    let mut func = FunctionData::new(
        address,
        "float_dirty".into(),
        vec![reg],
        vec![ParamType::Pointer],
        None,
        0,
        1,
        true,
    );
    func.var_type_candidates
        .insert(reg, vec![CandType::PtrVoid, CandType::F64]);
    let stage_a = ProgramSelectionState {
        candidate_idx: HashMap::new(),
        structure_world: HashMap::new(),
        var_decl_idx: [((address, reg), 0)].into_iter().collect(),
        var_type_override: HashMap::new(),
        analysis_results: BTreeMap::new(),
    };
    let (state, stats) = resolve_dirty_functions(
        std::slice::from_mut(&mut func),
        &HashMap::new(),
        &stage_a,
        &[address].into_iter().collect(),
        &committed_param(address, XType::Xfloat),
        &BTreeMap::new(),
        false,
    );
    assert_eq!(stats.resolved_count, 1);
    assert_eq!(stats.fallback_count, 0);
    let chosen = state.var_decl_idx[&(address, reg)];
    assert!(func.var_type_candidates[&reg][chosen].is_float());
}

#[test]
fn dirty_scalar_pin_overrides_stage_a_pointer_pruning() {
    let [address] = synthetic_ids();
    let reg = 13;
    let mut func = FunctionData::new(
        address,
        "scalar_dirty".into(),
        vec![reg],
        vec![ParamType::Pointer],
        None,
        0,
        1,
        true,
    );
    func.var_type_candidates
        .insert(reg, vec![CandType::PtrVoid, CandType::I64(Sign::Signed)]);
    func.must_pointer_regs.insert(reg);
    let stage_a = ProgramSelectionState {
        candidate_idx: HashMap::new(),
        structure_world: HashMap::new(),
        var_decl_idx: [((address, reg), 0)].into_iter().collect(),
        var_type_override: HashMap::new(),
        analysis_results: BTreeMap::new(),
    };
    let (state, stats) = resolve_dirty_functions(
        std::slice::from_mut(&mut func),
        &HashMap::new(),
        &stage_a,
        &[address].into_iter().collect(),
        &committed_param(address, XType::Xlong),
        &BTreeMap::new(),
        false,
    );

    assert_eq!(stats.resolved_count, 1);
    assert_eq!(stats.fallback_count, 0);
    let chosen = state.var_decl_idx[&(address, reg)];
    assert_eq!(
        func.var_type_candidates[&reg][chosen],
        CandType::I64(Sign::Signed)
    );
}

#[test]
fn stage_c_refreshes_flow_global_anchors_even_when_body_is_clean() {
    let [address] = synthetic_ids();
    let symbol = 0x9000usize;
    let mut func = FunctionData::new(
        address,
        "global_anchor".into(),
        Vec::new(),
        Vec::new(),
        None,
        0,
        1,
        true,
    );
    func.flow_anchors.global.insert(
        symbol,
        crate::decompile::passes::clight_select::solvers::flow::anchor_of_xtype(&XType::Xint, true),
    );
    let mut committed = CommittedInterfaces::default();
    committed.globals.insert(symbol, XType::Xfloat);
    let stage_a = ProgramSelectionState {
        candidate_idx: HashMap::new(),
        structure_world: HashMap::new(),
        var_decl_idx: HashMap::new(),
        var_type_override: HashMap::new(),
        analysis_results: BTreeMap::new(),
    };
    let (_, stats) = resolve_dirty_functions(
        std::slice::from_mut(&mut func),
        &HashMap::new(),
        &stage_a,
        &BTreeSet::new(),
        &committed,
        &BTreeMap::new(),
        false,
    );
    assert_eq!(stats.dirty_count, 0);
    assert_eq!(
        func.flow_anchors.global[&symbol],
        crate::decompile::passes::clight_select::solvers::flow::anchor_of_xtype(&XType::Xfloat, true,)
    );
}

#[test]
fn maximal_certification_plans_one_deterministic_new_site_per_retry() {
    let injected: BTreeSet<Node> = [0x30, 0x10, 0x20].into_iter().collect();
    let mut exempt: BTreeSet<Node> = [0x10].into_iter().collect();
    assert_eq!(first_new_flow_exemption(&injected, &exempt), Some(0x20));
    exempt.insert(0x20);
    assert_eq!(first_new_flow_exemption(&injected, &exempt), Some(0x30));
    exempt.insert(0x30);
    assert_eq!(first_new_flow_exemption(&injected, &exempt), None);
}

#[test]
fn maximal_certification_selects_propagator_without_environment_gate() {
    assert_eq!(selected_solve_engine(true), SolveEngine::Propagator);
    assert_eq!(selected_solve_engine(false), SolveEngine::Optimize);
}

// Class-level representatives: every Ty variant, both composite-id cases.
fn type_set() -> Vec<ClightType> {
    use ClightFloatSize::*;
    use ClightIntSize::*;
    use ClightSignedness::*;
    vec![
        ClightType::Tvoid,
        ClightType::Tint(I32, Signed, a()),
        ClightType::Tint(I32, Unsigned, a()),
        ClightType::Tlong(Signed, a()),
        ClightType::Tlong(Unsigned, a()),
        ClightType::Tfloat(F32, a()),
        ClightType::Tfloat(F64, a()),
        ClightType::Tpointer(Arc::new(ClightType::Tlong(Signed, a())), a()),
        ClightType::Tpointer(Arc::new(ClightType::Tvoid), a()),
        ClightType::Tpointer(Arc::new(ClightType::Tfloat(F64, a())), a()),
        ClightType::Tpointer(Arc::new(ClightType::Tstruct(1, a())), a()),
        ClightType::Tstruct(1, a()),
        ClightType::Tstruct(2, a()),
        ClightType::Tunion(7, a()),
        ClightType::Tunion(8, a()),
        ClightType::Tfunction(
            Arc::new(vec![]),
            Arc::new(ClightType::Tvoid),
            Default::default(),
        ),
    ]
}

// A closed (variable-free) Bool term is valid iff it is true; the solver check is the robust ground-truth evaluator (simplify alone can leave datatype tester applications unreduced).
fn eval_closed(b: &Bool) -> bool {
    if let Some(v) = b.clone().simplify().as_bool() {
        return v;
    }
    let s = z3::Solver::new();
    s.assert(&b.not());
    matches!(s.check(), SatResult::Unsat)
}

/// The Z3 relaxation and the executable checker must agree on every concrete class-level pair except the composite-id relaxation, where the test asserts soundness only.
#[test]
fn wt_cast_term_matches_ctyping() {
    z3::with_z3_config(&z3::Config::new(), || {
        let t = TypeDt::build();
        for from in type_set() {
            for to in type_set() {
                let term = wt_cast_term(&t, &clight_to_ty(&t, &from), &clight_to_ty(&t, &to));
                let z3_legal = eval_closed(&term);
                let same_kind_composites = matches!(
                    (&from, &to),
                    (ClightType::Tstruct(..), ClightType::Tstruct(..))
                        | (ClightType::Tunion(..), ClightType::Tunion(..))
                );
                // Pointer width moves a cast between non-Default cases only (Pointer/I2I/L2L/I2L/L2I/...), never in or out of Default, so LEGALITY is width-independent and parity must hold at both.
                for ptr64 in [true, false] {
                    let ct_legal = ctyping::wt_cast(ptr64, &from, &to);
                    if same_kind_composites {
                        assert!(
                            z3_legal || !ct_legal,
                            "wt_cast soundness (ptr64={}): {} -> {}",
                            ptr64,
                            ctyping::ty_str(&from),
                            ctyping::ty_str(&to)
                        );
                    } else {
                        assert_eq!(
                            z3_legal,
                            ct_legal,
                            "wt_cast parity (ptr64={}): {} -> {} (z3 {}, ctyping {})",
                            ptr64,
                            ctyping::ty_str(&from),
                            ctyping::ty_str(&to),
                            z3_legal,
                            ct_legal
                        );
                    }
                }
            }
        }
    });
}

/// wt_cast_to_reg is wt_cast_term specialized to the pruned register domain (no bare func/void/union targets) -- they must agree there.
#[test]
fn wt_cast_to_reg_matches_full_on_pruned_domain() {
    use ClightFloatSize::*;
    use ClightSignedness::*;
    let reg_targets = vec![
        ClightType::Tint(ClightIntSize::I32, Signed, a()),
        ClightType::Tlong(Unsigned, a()),
        ClightType::Tfloat(F64, a()),
        ClightType::Tpointer(Arc::new(ClightType::Tlong(Signed, a())), a()),
        ClightType::Tstruct(1, a()),
    ];
    z3::with_z3_config(&z3::Config::new(), || {
        let t = TypeDt::build();
        for from in type_set() {
            for to in &reg_targets {
                let full = eval_closed(&wt_cast_term(
                    &t,
                    &clight_to_ty(&t, &from),
                    &clight_to_ty(&t, to),
                ));
                let spec = eval_closed(&wt_cast_to_reg(
                    &t,
                    &clight_to_ty(&t, &from),
                    &clight_to_ty(&t, to),
                ));
                assert_eq!(
                    full,
                    spec,
                    "to-reg specialization: {} -> {}",
                    ctyping::ty_str(&from),
                    ctyping::ty_str(to)
                );
            }
        }
    });
}

#[test]
fn binop_legality_matches_ctyping() {
    use ClightBinaryOp::*;
    let ops = [
        Oadd, Osub, Omul, Odiv, Omod, Oand, Oor, Oxor, Oshl, Oshr, Oeq, One, Olt, Ogt, Ole, Oge,
    ];
    z3::with_z3_config(&z3::Config::new(), || {
        let t = TypeDt::build();
        for op in ops {
            for l in type_set() {
                for r in type_set() {
                    let term =
                        binop_legal_term(&t, op, &clight_to_ty(&t, &l), &clight_to_ty(&t, &r));
                    let z3_legal = eval_closed(&term);
                    // The z3 encoding classifies with width-agnostic is_ptrish/is_intish, so legality must agree at BOTH pointer widths; only the ptr-minus-ptr RESULT type moves with the width.
                    for ptr64 in [true, false] {
                        let ct_legal = ctyping::type_binop(ptr64, op, &l, &r).is_some();
                        assert_eq!(
                            z3_legal,
                            ct_legal,
                            "binop parity (ptr64={}): {:?} on ({}, {})",
                            ptr64,
                            op,
                            ctyping::ty_str(&l),
                            ctyping::ty_str(&r)
                        );
                    }
                }
            }
        }
    });
}

// Soundness of hardening the pointer/float arm: whenever the hard clause is violated, EVERY binop is
// ill-typed under ctyping, so the clause can never cut off a selection that would have printed valid C.
// A pair the clause rejects but some op accepts would be a silent loss of a legal program.
#[test]
fn ptr_float_mix_is_illegal_for_every_binop() {
    use ClightBinaryOp::*;
    let ops = [
        Oadd, Osub, Omul, Odiv, Omod, Oand, Oor, Oxor, Oshl, Oshr, Oeq, One, Olt, Ogt, Ole, Oge,
    ];
    z3::with_z3_config(&z3::Config::new(), || {
        let t = TypeDt::build();
        let mut violations = 0usize;
        for l in type_set() {
            for r in type_set() {
                let (ltm, rtm) = (clight_to_ty(&t, &l), clight_to_ty(&t, &r));
                for (ptr_side, float_side, lhs_is_ptr) in [(&ltm, &rtm, true), (&rtm, &ltm, false)]
                {
                    if eval_closed(&no_ptr_float_term(&t, ptr_side, float_side)) {
                        continue;
                    }
                    violations += 1;
                    for op in ops {
                        for ptr64 in [true, false] {
                            assert!(
                                ctyping::type_binop(ptr64, op, &l, &r).is_none(),
                                "hard ptr/float clause rejects a pair ctyping accepts (ptr64={}, lhs_is_ptr={}): {:?} on ({}, {})",
                                ptr64,
                                lhs_is_ptr,
                                op,
                                ctyping::ty_str(&l),
                                ctyping::ty_str(&r)
                            );
                        }
                    }
                }
            }
        }
        // Guard against the clause silently becoming vacuous (e.g. if is_ptrish or is_float lost a variant).
        assert!(
            violations > 0,
            "the ptr/float clause never fired over type_set(); it is no longer constraining anything"
        );
    });
}

#[test]
fn unop_legality_matches_ctyping() {
    use ClightUnaryOp::*;
    z3::with_z3_config(&z3::Config::new(), || {
        let t = TypeDt::build();
        for op in [Onotbool, Onotint, Oneg, Oabsfloat] {
            for x in type_set() {
                let term = unop_legal_term(&t, op, &clight_to_ty(&t, &x));
                let z3_legal = eval_closed(&term);
                // Width-agnostic on the z3 side, so parity must hold at both widths.
                for ptr64 in [true, false] {
                    let ct_legal = ctyping::type_unop(ptr64, op, &x).is_some();
                    assert_eq!(
                        z3_legal,
                        ct_legal,
                        "unop parity (ptr64={}): {:?} on {}",
                        ptr64,
                        op,
                        ctyping::ty_str(&x)
                    );
                }
            }
        }
    });
}

/// D8 lockstep: both declaration consumers agree, for EVERY candidate variant, on whether it
/// is a pointer and whether it is a float. Both are total matches now, so this catches a new
/// variant being classified inconsistently rather than a string falling to a `long` default.
#[test]
fn candidate_vocabulary_lockstep() {
    use crate::decompile::passes::c_pass::types::CType;
    use crate::decompile::passes::clight_select::candtype::all_variants;
    use crate::decompile::passes::clight_select::wt_audit::candtype_to_clight;
    for candidate in all_variants() {
        let ctype = crate::decompile::passes::c_pass::helpers::candtype_to_ctype(
            candidate,
            crate::abi::DataModel::Lp64,
        );
        let clight = candtype_to_clight(candidate);
        assert_eq!(
            matches!(ctype, CType::Pointer(..)),
            candidate.is_pointer(),
            "emitter disagrees on pointerness of {:?}",
            candidate
        );
        assert_eq!(
            matches!(clight, ClightType::Tpointer(..)),
            candidate.is_pointer(),
            "checker disagrees on pointerness of {:?}",
            candidate
        );
        assert_eq!(
            matches!(ctype, CType::Float(_)),
            candidate.is_float(),
            "emitter disagrees on floatness of {:?}",
            candidate
        );
        assert_eq!(
            matches!(clight, ClightType::Tfloat(..)),
            candidate.is_float(),
            "checker disagrees on floatness of {:?}",
            candidate
        );
    }
}

#[test]
fn authoritative_global_type_drives_exact_statement_repick() {
    use crate::decompile::passes::clight_select::query::KnownGlobalTypes;

    let attr = ClightAttr::default();
    let tlong = ClightType::Tlong(ClightSignedness::Signed, attr.clone());
    let tdouble = ClightType::Tfloat(ClightFloatSize::F64, attr.clone());
    let tchar_ptr = ClightType::Tpointer(
        Arc::new(ClightType::Tint(
            ClightIntSize::I8,
            ClightSignedness::Signed,
            attr,
        )),
        ClightAttr::default(),
    );

    // The machine load is annotated `long`, while the authoritative emitted
    // declaration is a character pointer. Synthetic identifiers keep this
    // regression independent of any particular binary layout.
    let [global_raw, reg, func_addr, load_node, other_use] = synthetic_ids();
    let global = global_raw as Ident;
    let mut func = FunctionData::new(
        func_addr,
        "authoritative-global-repick".to_string(),
        Vec::new(),
        Vec::new(),
        None,
        0,
        func_addr,
        true,
    );
    func.used_regs.insert(reg);
    func.var_types.insert(reg, CandType::F64);
    func.var_type_candidates
        .insert(reg, vec![CandType::F64, CandType::I64(Sign::Signed)]);
    func.known_global_types = Arc::new(KnownGlobalTypes {
        by_ident: [(global, tchar_ptr)].into_iter().collect(),
        ..KnownGlobalTypes::default()
    });
    func.node_statements.insert(
        load_node,
        vec![
            ClightStmt::Sset(
                reg as Ident,
                ClightExpr::Ecast(Box::new(ClightExpr::Evar(global, tlong.clone())), tdouble),
            ),
            ClightStmt::Sset(reg as Ident, ClightExpr::Evar(global, tlong.clone())),
        ],
    );
    // Keep the model on the integer declaration, as the real function's
    // other uses did, so this specifically tests post-model re-picking.
    func.node_statements.insert(
        other_use,
        vec![ClightStmt::Sswitch(
            ClightExpr::Etempvar(reg as Ident, tlong),
            Vec::new(),
        )],
    );

    let (statement_idx, declaration_idx, _, _, _) = solve_function(&func, &HashMap::new(), false);
    assert_eq!(declaration_idx.get(&reg), Some(&1));
    assert_eq!(statement_idx.get(&load_node), Some(&Some(1)));
}

#[test]
fn exact_statement_repick_rejects_a_void_lvalue_store() {
    let attr = ClightAttr::default();
    let tlong = ClightType::Tlong(ClightSignedness::Signed, attr.clone());
    let tint = ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, attr.clone());
    let tchar = ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, attr.clone());
    let ptr_void = ClightType::Tpointer(Arc::new(ClightType::Tvoid), attr.clone());
    let ptr_char = ClightType::Tpointer(Arc::new(tchar.clone()), attr);

    let [reg, func_addr, store_node] = synthetic_ids();
    let mut func = FunctionData::new(
        func_addr,
        "void-lvalue-repick".to_string(),
        Vec::new(),
        Vec::new(),
        None,
        0,
        func_addr,
        true,
    );
    func.used_regs.insert(reg);
    func.var_types.insert(reg, CandType::PtrVoid);
    func.var_type_candidates
        .insert(reg, vec![CandType::PtrVoid, CandType::PtrChar]);

    let base = ClightExpr::Etempvar(reg as Ident, tlong);
    let rhs = ClightExpr::EconstInt(0, tint);
    func.node_statements.insert(
        store_node,
        vec![
            ClightStmt::Sassign(
                ClightExpr::Ederef(
                    Box::new(ClightExpr::Ecast(Box::new(base.clone()), ptr_void)),
                    ClightType::Tvoid,
                ),
                rhs.clone(),
            ),
            ClightStmt::Sassign(
                ClightExpr::Ederef(Box::new(ClightExpr::Ecast(Box::new(base), ptr_char)), tchar),
                rhs,
            ),
        ],
    );

    let (statement_idx, _, _, _, _) = solve_function(&func, &HashMap::new(), false);
    assert_eq!(statement_idx.get(&store_node), Some(&Some(1)));
}

#[test]
fn must_pointer_fact_overrides_an_integer_declaration_prior() {
    let [reg, func_addr] = synthetic_ids();
    let mut func = FunctionData::new(
        func_addr,
        "must-pointer".to_string(),
        Vec::new(),
        Vec::new(),
        None,
        0,
        func_addr,
        true,
    );
    func.used_regs.insert(reg);
    func.must_pointer_regs.insert(reg);
    func.var_types.insert(reg, CandType::I32(Sign::Signed));
    func.var_type_candidates
        .insert(reg, vec![CandType::I32(Sign::Signed), CandType::PtrChar]);

    let (_, declarations, _, _, _) = solve_function(&func, &HashMap::new(), false);

    assert_eq!(declarations.get(&reg), Some(&1));
}
