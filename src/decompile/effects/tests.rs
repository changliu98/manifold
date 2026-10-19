use super::flags::*;
use super::*;
use crate::decompile::passes::c_pass::types::CType;
use crate::decompile::passes::clight_select::{
    solvers::integer_semantics::Validator, solvers::obligations::Verdict,
};
use crate::decompile::passes::{clight_pass, cminor_pass};
use crate::x86::op::Operation;
use crate::x86::types::*;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

const CONDITIONS: [&str; 16] = [
    "CMOVO", "CMOVNO", "CMOVB", "CMOVAE", "CMOVE", "CMOVNE", "CMOVBE", "CMOVA", "CMOVS", "CMOVNS",
    "CMOVP", "CMOVNP", "CMOVL", "CMOVGE", "CMOVLE", "CMOVG",
];

fn statement(spec: FlagSelect) -> ClightStmt {
    let expr = cminor_pass::csharp_expr_from_cminor(&CminorExpr::Eop(
        Operation::Oflagselect(spec),
        Arc::new(vec![1, 2, 3]),
    ))
    .unwrap();
    let ty = ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default());
    let types = HashMap::from([(1, ty.clone()), (2, ty.clone()), (3, ty.clone()), (4, ty)]);
    ClightStmt::Sset(
        4,
        clight_pass::clight_expr_from_csharp_with_types(&expr, &types, 8),
    )
}

#[test]
fn flag_select_c_matches_machine_bits_and_is_defined() {
    for producer in [Producer::Compare, Producer::Test] {
        for width in [1, 2, 4, 8] {
            for name in CONDITIONS {
                for result_bits in [32, 64] {
                    let spec = FlagSelect {
                        capture: 10,
                        producer,
                        predicate: Predicate::cmov(name).unwrap(),
                        width,
                        immediate: -1,
                        result_bits,
                    };
                    let inst =
                        RTLInst::Iop(Operation::Oflagselect(spec), Arc::new(vec![1, 2, 3]), 4);
                    let declarations = HashMap::from([
                        (1, CType::long()),
                        (2, CType::long()),
                        (3, CType::long()),
                        (4, CType::long()),
                    ]);
                    let check = Validator::new().check(
                        &inst,
                        &statement(spec),
                        &declarations,
                        crate::abi::DataModel::Lp64,
                    );
                    assert_eq!(check.verdict, Verdict::Equivalent, "{spec:?}: {check:?}");
                }
            }
        }
    }
}

#[test]
fn sign_flag_is_not_signed_comparison_after_overflow() {
    use z3::ast::BV;
    let spec = FlagSelect {
        capture: 10,
        producer: Producer::Compare,
        predicate: Predicate::NonSign,
        width: 1,
        immediate: 1,
        result_bits: 32,
    };
    let value = BV::from_u64(128, 8); // -128 - 1 wraps to +127: NS is true, GE false.
    use z3::ast::Ast;
    assert_eq!(
        machine_predicate(spec, &value)
            .unwrap()
            .simplify()
            .as_bool(),
        Some(true)
    );
    assert_eq!(
        machine_predicate(
            FlagSelect {
                predicate: Predicate::GreaterEqual,
                ..spec
            },
            &value
        )
        .unwrap()
        .simplify()
        .as_bool(),
        Some(false)
    );
}

#[test]
fn transfer_requires_all_members_in_the_same_epoch() {
    use contracts::*;
    let input = ArtifactId {
        epoch: 1,
        stage: Stage::Machine,
        node: 50,
        alternative: 0,
    };
    let load = ArtifactId {
        epoch: 1,
        stage: Stage::Rtl,
        node: 70,
        alternative: 0,
    };
    let op = ArtifactId {
        epoch: 1,
        stage: Stage::Rtl,
        node: 20,
        alternative: 0,
    };
    let claim = Transfer {
        effect: EffectId {
            instruction: 50,
            slot: 0,
        },
        inputs: vec![input],
        outputs: vec![load, op],
    };
    let available = BTreeSet::from([input]);
    assert_eq!(
        check_transfer(&claim, &available, &BTreeSet::from([load]), 1),
        Outcome::Missing
    );
    assert_eq!(
        check_transfer(&claim, &available, &BTreeSet::from([load, op]), 1),
        Outcome::Carried
    );
    assert_eq!(
        check_transfer(&claim, &available, &BTreeSet::from([load, op]), 2),
        Outcome::Missing
    );
    let duplicate = Transfer {
        outputs: vec![load, load],
        ..claim
    };
    assert_eq!(
        check_transfer(&duplicate, &available, &BTreeSet::from([load]), 1),
        Outcome::Refuted
    );
}

fn emission_fixture() -> (
    crate::decompile::elevator::DecompileDB,
    crate::decompile::passes::clight_select::solvers::completeness::SelectedContract,
) {
    use crate::decompile::passes::c_pass::types::*;
    use crate::decompile::passes::clight_select::solvers::completeness::SelectedContract;
    let contract = SelectedContract {
        function: 1,
        node: 30,
        spec: FlagSelect {
            capture: 900,
            producer: Producer::Compare,
            predicate: Predicate::NonSign,
            width: 1,
            immediate: 1,
            result_bits: 64,
        },
        epoch: 7,
        captured: true,
        ordered: true,
        select_present: true,
        capture_present: true,
        refuted: false,
        select_alternative: Some(1),
        capture_alternative: Some(2),
    };
    let mut db = crate::decompile::elevator::DecompileDB::default();
    db.effect_epoch = 7;
    db.rel_push("effect_selected_contract", contract.clone());
    db.rel_push(
        "effect_receipt",
        (
            1_u64,
            Receipt {
                effect: contract.spec.read_effect(),
                artifact: ArtifactId {
                    epoch: 7,
                    stage: Stage::Selection,
                    node: 30,
                    alternative: 1,
                },
                outcome: Outcome::Carried,
                reason: "test prerequisite",
            },
        ),
    );
    let body = CStmt::Sequence(vec![
        CStmt::Effect(contract.site(900), Box::new(CStmt::Expr(CExpr::int(1)))),
        CStmt::Effect(
            contract.site(30),
            Box::new(CStmt::Return(Some(CExpr::int(1)))),
        ),
    ]);
    let mut tu = TranslationUnit::new();
    tu.add_function(FuncDef {
        name: "test".into(),
        return_type: CType::int(),
        params: vec![],
        is_variadic: false,
        storage_class: StorageClass::Auto,
        body,
        local_vars: vec![],
        loc: SourceLoc::unknown(),
    });
    db.cast_raw_translation_unit = Some(tu.clone());
    db.cast_optimized_translation_unit = Some(tu);
    (db, contract)
}

#[test]
fn emission_admission_rejects_missing_duplicated_stale_or_wrong_candidate_occurrences() {
    use crate::decompile::passes::c_pass::types::*;
    for mutation in 0..6 {
        let (mut db, contract) = emission_fixture();
        if mutation == 3 {
            db.effect_epoch = 8;
        }
        if mutation == 5 {
            db.rel_set(
                "effect_receipt",
                vec![(
                    1_u64,
                    Receipt {
                        effect: contract.spec.read_effect(),
                        artifact: ArtifactId {
                            epoch: 7,
                            stage: Stage::Selection,
                            node: 30,
                            alternative: 1,
                        },
                        outcome: Outcome::Missing,
                        reason: "no-model fallback cannot satisfy prerequisite",
                    },
                )]
                .into_iter()
                .collect::<ascent::boxcar::Vec<_>>(),
            );
        }
        let TopLevelDecl::FuncDef(f) =
            &mut db.cast_optimized_translation_unit.as_mut().unwrap().decls[0]
        else {
            unreachable!()
        };
        let CStmt::Sequence(items) = &mut f.body else {
            unreachable!()
        };
        match mutation {
            1 => {
                items.remove(0);
            }
            2 => items.push(items[0].clone()),
            4 => {
                if let CStmt::Effect(site, _) = &mut items[0] {
                    site.alternative = 0;
                }
            }
            _ => {}
        }
        finalize(&mut db);
        assert_eq!(
            db.unresolved_effect_count(),
            usize::from(mutation != 0),
            "mutation {mutation}"
        );
        assert_eq!(db.cast_optimized_translation_unit.is_some(), mutation == 0);
    }
}

#[test]
fn clight_to_c_preserves_explicit_effect_identity() {
    let site = EffectSite {
        function: 1,
        node: 900,
        epoch: 4,
        alternative: 3,
    };
    let stmt = ClightStmt::Seffect(
        site,
        Box::new(ClightStmt::Sreturn(Some(ClightExpr::EconstInt(
            1,
            ClightType::Tint(
                ClightIntSize::I32,
                ClightSignedness::Signed,
                ClightAttr::default(),
            ),
        )))),
    );
    let mut ctx = crate::decompile::passes::c_pass::convert::from_relations::ConversionContext::new(
        HashMap::new(),
        crate::abi::DataModel::Lp64,
    );
    let result =
        crate::decompile::passes::c_pass::convert::from_relations::convert_stmt(&stmt, &mut ctx);
    let occurrences = c::occurrences(&result);
    assert_eq!(occurrences.len(), 1);
    assert_eq!(occurrences[0].0, site);
}

#[test]
fn emitted_shared_nodes_keep_each_functions_selected_statement_and_identity() {
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::c_pass::types::*;
    use crate::decompile::passes::clight_select::select::SelectedFunction;
    let node = 900;
    let mut functions = Vec::new();
    let mut statements = HashMap::new();
    for function in [10, 20] {
        let site = EffectSite {
            function,
            node,
            epoch: 0,
            alternative: 0,
        };
        functions.push(SelectedFunction {
            address: function,
            name: format!("shared_owner_{function}"),
            entry_node: node,
            return_type: ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default()),
            param_regs: vec![],
            param_types: vec![],
            stack_size: 0,
            statements: HashMap::from([(
                node,
                ClightStmt::Sreturn(Some(ClightExpr::EconstLong(
                    function as i64,
                    ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default()),
                ))),
            )]),
            selected_candidate_nodes: Default::default(),
            selected_write_bytes: Default::default(),
            successors: Default::default(),
            used_regs: Default::default(),
            struct_fields: Default::default(),
            sseq_groups: Default::default(),
            var_types: Default::default(),
            var_type_candidates: Default::default(),
            var_decl_idx: Default::default(),
            concrete_declarations: Default::default(),
            binding_plan: Default::default(),
            reg_struct_ids: Default::default(),
            loop_info: Default::default(),
        });
        statements.insert(
            (function, node),
            CStmt::Effect(
                site,
                Box::new(CStmt::Return(Some(CExpr::int(function as i64)))),
            ),
        );
    }
    let mut db = DecompileDB::default();
    db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
    let tu = crate::decompile::passes::c_pass::convert::from_relations::build_translation_unit_from_stmt_map_with_types(
        &db, &functions, &[], &HashMap::new(), &HashMap::new(), &statements, &HashMap::new(), &HashMap::new());
    let mut seen = BTreeSet::new();
    for declaration in &tu.decls {
        if let TopLevelDecl::FuncDef(function) = declaration {
            let occurrences = c::occurrences(&function.body);
            assert_eq!(occurrences.len(), 1);
            let site = occurrences[0].0;
            assert_eq!(function.name, format!("shared_owner_{}", site.function));
            assert_eq!(
                occurrences[0].1,
                CStmt::Return(Some(CExpr::int(site.function as i64)))
            );
            seen.insert(site.function);
        }
    }
    assert_eq!(seen, BTreeSet::from([10, 20]));
}
