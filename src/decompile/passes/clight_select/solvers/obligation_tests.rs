use crate::abi::DataModel;
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::decompile::passes::clight_select::solvers::obligations::*;
use crate::decompile::passes::semantic_counterexample::ledger::ObjectId;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use std::sync::Arc;

fn int(size: ClightIntSize, signed: bool) -> ClightType {
    ClightType::Tint(
        size,
        if signed {
            ClightSignedness::Signed
        } else {
            ClightSignedness::Unsigned
        },
        ClightAttr::default(),
    )
}

fn constant(value: i32) -> ClightExpr {
    ClightExpr::EconstInt(value, int(ClightIntSize::I32, true))
}

fn cell(offset: i64, size: ClightIntSize, signed: bool) -> ClightExpr {
    let byte = int(ClightIntSize::I8, false);
    let array = ClightType::Tarray(Arc::new(byte.clone()), 16, ClightAttr::default());
    let pointer = ClightType::Tpointer(Arc::new(byte), ClightAttr::default());
    let base = ClightExpr::Ecast(
        Box::new(ClightExpr::Eaddrof(
            Box::new(ClightExpr::Evar(10, array.clone())),
            ClightType::Tpointer(Arc::new(array), ClightAttr::default()),
        )),
        pointer.clone(),
    );
    ClightExpr::Ederef(
        Box::new(ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(base),
            Box::new(ClightExpr::EconstLong(
                offset,
                ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default()),
            )),
            pointer,
        )),
        int(size, signed),
    )
}

fn fixture() -> (FunctionData, memory_theory::WriteContract) {
    let mut f = FunctionData::new(1, "effects".into(), vec![], vec![], None, 32, 30, true);
    f.used_regs.insert(10);
    f.var_type_candidates.insert(10, vec![CandType::PtrChar]);
    let w = memory_theory::WriteContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 30,
        root: 10,
        offset: 4,
        width: 4,
        locals: BTreeSet::from([12]),
    };
    (f, w)
}

#[test]
fn a_correct_byte_target_does_not_validate_the_wrong_value() {
    let (f, w) = fixture();
    let machine = RTLInst::Iop(Operation::Ointconst(7), Arc::new(vec![]), 12);
    let good = ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(7));
    let bad = ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(6));
    let v = Validator::new();
    assert_eq!(
        v.check(WriteTarget(&w), &bad, &HashMap::new(), &f).verdict,
        Verdict::Equivalent
    );
    let check = v.check(WriteValue(&machine, &w), &bad, &HashMap::new(), &f);
    assert_eq!(check.verdict, Verdict::Refuted);
    assert!(matches!(
        check.witness,
        Some(Witness::Value {
            machine: 7,
            source: 6,
            source_defined: true,
            ..
        })
    ));
    assert_eq!(
        v.check(WriteValue(&machine, &w), &good, &HashMap::new(), &f)
            .verdict,
        Verdict::Equivalent
    );
}

#[test]
fn final_selection_and_repick_respect_the_value_counterexample() {
    let (mut f, w) = fixture();
    f.storage_writes.push(w);
    f.memory_anchors.insert(
        30,
        RTLInst::Iop(Operation::Ointconst(7), Arc::new(vec![]), 12),
    );
    f.node_statements.insert(
        30,
        vec![
            ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(6)),
            ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(7)),
        ],
    );
    let outcome = crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
        &f,
        &HashMap::new(),
        &[],
    )
    .unwrap();
    assert_eq!(outcome.0[&30], Some(1));
}

#[test]
fn signed_overflow_is_a_refutation_even_when_written_bits_agree() {
    let (mut f, w) = fixture();
    let signed = int(ClightIntSize::I32, true);
    let unsigned = int(ClightIntSize::I32, false);
    let var = |r| ClightExpr::Etempvar(r, signed.clone());
    let add = |unsigned_operands| {
        let operand = |r| {
            if unsigned_operands {
                ClightExpr::Ecast(Box::new(var(r)), unsigned.clone())
            } else {
                var(r)
            }
        };
        ClightStmt::Sassign(
            cell(4, ClightIntSize::I32, false),
            ClightExpr::Ebinop(
                ClightBinaryOp::Oadd,
                Box::new(operand(1)),
                Box::new(operand(2)),
                if unsigned_operands {
                    unsigned.clone()
                } else {
                    signed.clone()
                },
            ),
        )
    };
    let machine = RTLInst::Iop(Operation::Oadd, Arc::new(vec![1, 2]), 12);
    let declarations = HashMap::from([(1, CType::int()), (2, CType::int())]);
    let v = Validator::new();
    let bad = v.check(WriteValue(&machine, &w), &add(false), &declarations, &f);
    assert_eq!(bad.verdict, Verdict::Refuted);
    let Some(Witness::Value {
        machine: expected,
        source,
        source_defined,
        ..
    }) = bad.witness
    else {
        panic!("missing value witness");
    };
    assert_eq!(expected, source);
    assert!(!source_defined);
    assert_eq!(
        v.check(WriteValue(&machine, &w), &add(true), &declarations, &f)
            .verdict,
        Verdict::Equivalent
    );
    for r in [1, 2] {
        f.used_regs.insert(r);
        f.var_type_candidates
            .insert(r, vec![CandType::I32(Sign::Signed)]);
    }
    f.memory_anchors.insert(30, machine);
    f.storage_writes.push(w);
    f.node_statements.insert(30, vec![add(false), add(true)]);
    let outcome = crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
        &f,
        &HashMap::new(),
        &[],
    )
    .unwrap();
    assert_eq!(outcome.0[&30], Some(1));
}

#[test]
fn store_conversion_truncates_only_after_evaluating_the_payload() {
    let (f, mut w) = fixture();
    w.width = 1;
    let machine = RTLInst::Istore(
        MemoryChunk::MInt8Unsigned,
        Addressing::Ainstack(4),
        Arc::new(vec![]),
        1,
    );
    let rhs = ClightExpr::Etempvar(1, int(ClightIntSize::I32, false));
    let good = ClightStmt::Sassign(cell(4, ClightIntSize::I8, false), rhs.clone());
    let bad = ClightStmt::Sassign(
        cell(4, ClightIntSize::I8, false),
        ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(rhs),
            Box::new(constant(1)),
            int(ClightIntSize::I32, false),
        ),
    );
    let declarations = HashMap::from([(1, CType::int())]);
    let v = Validator::new();
    assert_eq!(
        v.check(WriteValue(&machine, &w), &good, &declarations, &f)
            .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        v.check(WriteValue(&machine, &w), &bad, &declarations, &f)
            .verdict,
        Verdict::Refuted
    );
}

#[test]
fn frame_read_compares_extension_of_the_same_symbolic_bytes() {
    let (mut f, _) = fixture();
    let r = memory_theory::ReadContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 40,
        root: 10,
        offset: 4,
        width: 1,
        chunk: MemoryChunk::MInt8Unsigned,
        destination: 13,
        write_bits: None,
        signed_word_load: false,
    };
    let good = ClightStmt::Sset(13, cell(4, ClightIntSize::I8, false));
    let bad = ClightStmt::Sset(13, cell(4, ClightIntSize::I8, true));
    let declarations = HashMap::from([(13, CType::int())]);
    let v = Validator::new();
    let check = v.check(ReadValue(&r), &bad, &declarations, &f);
    assert_eq!(check.verdict, Verdict::Refuted);
    let Some(Witness::Value {
        memory: Some(byte),
        machine,
        source,
        source_defined,
        ..
    }) = check.witness
    else {
        panic!("missing memory witness");
    };
    assert!(byte >= 128);
    assert_eq!(machine, byte);
    assert_ne!(machine, source);
    assert!(source_defined);
    assert_eq!(
        v.check(ReadValue(&r), &good, &declarations, &f).verdict,
        Verdict::Equivalent
    );
    f.used_regs.insert(13);
    f.var_type_candidates
        .insert(13, vec![CandType::I32(Sign::Signed)]);
    f.storage_reads.push(r);
    f.node_statements.insert(40, vec![bad, good]);
    assert_eq!(
        crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
            &f,
            &HashMap::new(),
            &[]
        )
        .unwrap()
        .0[&40],
        Some(1)
    );
}

#[test]
fn extra_writes_and_unrelated_input_names_are_not_certified() {
    let (f, w) = fixture();
    let machine = RTLInst::Iop(Operation::Omove, Arc::new(vec![1]), 12);
    let statement = ClightStmt::Sassign(
        cell(4, ClightIntSize::I32, false),
        ClightExpr::Etempvar(2, int(ClightIntSize::I32, false)),
    );
    let declarations = HashMap::from([(1, CType::int()), (2, CType::int())]);
    let v = Validator::new();
    assert_eq!(
        v.check(WriteValue(&machine, &w), &statement, &declarations, &f)
            .verdict,
        Verdict::Unsupported
    );
    let compound = ClightStmt::Ssequence(vec![statement.clone(), statement]);
    assert_eq!(
        v.check(WriteTarget(&w), &compound, &declarations, &f)
            .verdict,
        Verdict::Unsupported
    );
}

#[test]
fn volatile_float_and_widened_unproven_reads_stay_unsupported() {
    let (f, _) = fixture();
    let r = memory_theory::ReadContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 40,
        root: 10,
        offset: 4,
        width: 1,
        chunk: MemoryChunk::MInt8Unsigned,
        destination: 13,
        write_bits: None,
        signed_word_load: false,
    };
    let statement = ClightStmt::Sset(13, cell(4, ClightIntSize::I8, false));
    let v = Validator::new();
    assert_eq!(
        v.check(
            ReadValue(&r),
            &statement,
            &HashMap::from([(13, CType::long())]),
            &f
        )
        .verdict,
        Verdict::Unsupported
    );
    let mut float = r.clone();
    float.chunk = MemoryChunk::MFloat32;
    assert_eq!(
        v.check(
            ReadValue(&float),
            &statement,
            &HashMap::from([(13, CType::int())]),
            &f
        )
        .verdict,
        Verdict::Unsupported
    );
    let mut volatile = cell(4, ClightIntSize::I8, false);
    if let ClightExpr::Ederef(_, ClightType::Tint(_, _, attr)) = &mut volatile {
        attr.attr_volatile = true;
    }
    assert_eq!(
        v.check(
            ReadValue(&r),
            &ClightStmt::Sset(13, volatile),
            &HashMap::from([(13, CType::int())]),
            &f
        )
        .verdict,
        Verdict::Unsupported
    );
}

#[test]
fn scheduler_declares_memory_effect_anchor_inputs() {
    use crate::decompile::passes::pass::IRPass;
    let pass = crate::decompile::passes::clight_emit_pass::ClightSelectPass;
    for input in [
        "rtl_inst",
        "frame_stack_read_bytes",
        "frame_read_storage_access_owner",
        "rtl_available_value",
        "machine_register_write_view",
    ] {
        assert!(
            pass.inputs().contains(&input) || pass.extra_reads().contains(&input),
            "undeclared {input}"
        );
    }
}

#[test]
fn memory_coverage_cannot_starve_existing_integer_semantic_checks() {
    let (f, w) = fixture();
    let v = Validator::new();
    let machine = RTLInst::Iop(Operation::Ointconst(7), Arc::new(vec![]), 12);
    let store = ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(7));
    for _ in 0..256 {
        assert_eq!(
            v.check(WriteValue(&machine, &w), &store, &HashMap::new(), &f)
                .verdict,
            Verdict::Equivalent
        );
    }
    assert_eq!(
        v.check(WriteValue(&machine, &w), &store, &HashMap::new(), &f)
            .verdict,
        Verdict::Unknown
    );
    let bad = ClightStmt::Sset(12, constant(6));
    let check = v.check(
        Integer(&machine),
        &bad,
        &HashMap::from([(12, CType::int())]),
        &f,
    );
    assert_eq!(check.verdict, Verdict::Refuted);
    assert!(check.witness.is_some());
}

#[test]
fn an_available_producer_connects_an_inlined_constant_to_the_machine_store() {
    let (mut f, w) = fixture();
    let machine = RTLInst::Iop(Operation::Omove, Arc::new(vec![7]), 12);
    let store = |value| ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), constant(value));
    let v = Validator::new();
    assert_eq!(
        v.check(WriteValue(&machine, &w), &store(6), &HashMap::new(), &f)
            .verdict,
        Verdict::Unsupported,
        "a single-definition guess is not an input relation"
    );
    f.value_producers.insert(
        (30, 7),
        crate::decompile::passes::clight_select::solvers::producer_values::Producer {
            definition: 90,
            operation: Operation::Ointconst(7),
            arguments: Arc::new(vec![]),
            write_bits: Some(32),
        },
    );
    let bad = v.check(WriteValue(&machine, &w), &store(6), &HashMap::new(), &f);
    assert_eq!(bad.verdict, Verdict::Refuted);
    assert!(
        bad.registers.is_empty(),
        "the removed temporary needs no invented C declaration"
    );
    assert!(matches!(
        bad.witness,
        Some(Witness::Value {
            machine: 7,
            source: 6,
            ..
        })
    ));
    assert_eq!(
        v.check(WriteValue(&machine, &w), &store(7), &HashMap::new(), &f)
            .verdict,
        Verdict::Equivalent
    );
    f.storage_writes.push(w);
    f.memory_anchors.insert(30, machine);
    f.node_statements.insert(30, vec![store(6), store(7)]);
    assert_eq!(
        crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
            &f,
            &HashMap::new(),
            &[]
        )
        .unwrap()
        .0[&30],
        Some(1)
    );
}

#[test]
fn decoder_zero_extension_is_not_a_signed_literal_heuristic() {
    let (mut f, mut w) = fixture();
    w.width = 8;
    let mut lhs = cell(4, ClightIntSize::I32, false);
    let ClightExpr::Ederef(_, ty) = &mut lhs else {
        unreachable!()
    };
    *ty = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
    let bad = ClightStmt::Sassign(
        lhs.clone(),
        ClightExpr::EconstLong(
            -1,
            ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default()),
        ),
    );
    let good = ClightStmt::Sassign(
        lhs,
        ClightExpr::Ecast(Box::new(constant(-1)), int(ClightIntSize::I32, false)),
    );
    let machine = RTLInst::Iop(Operation::Omove, Arc::new(vec![7]), 12);
    f.value_producers.insert(
        (30, 7),
        crate::decompile::passes::clight_select::solvers::producer_values::Producer {
            definition: 90,
            operation: Operation::Ointconst(-1),
            arguments: Arc::new(vec![]),
            write_bits: None,
        },
    );
    let v = Validator::new();
    assert_eq!(
        v.check(WriteValue(&machine, &w), &good, &HashMap::new(), &f)
            .verdict,
        Verdict::Unsupported
    );
    f.value_producers.get_mut(&(30, 7)).unwrap().write_bits = Some(32);
    let check = v.check(WriteValue(&machine, &w), &bad, &HashMap::new(), &f);
    assert_eq!(check.verdict, Verdict::Refuted);
    assert!(matches!(
        check.witness,
        Some(Witness::Value {
            machine: 0xffff_ffff,
            source: u64::MAX,
            ..
        })
    ));
    assert_eq!(
        v.check(WriteValue(&machine, &w), &good, &HashMap::new(), &f)
            .verdict,
        Verdict::Equivalent
    );
    f.value_producers.get_mut(&(30, 7)).unwrap().write_bits = Some(16);
    assert_eq!(
        v.check(WriteValue(&machine, &w), &good, &HashMap::new(), &f)
            .verdict,
        Verdict::Unsupported
    );
}

#[test]
fn available_arithmetic_retains_its_operand_dependencies_and_c_definedness() {
    let (mut f, w) = fixture();
    let machine = RTLInst::Iop(Operation::Omove, Arc::new(vec![7]), 12);
    f.value_producers.insert(
        (30, 7),
        crate::decompile::passes::clight_select::solvers::producer_values::Producer {
            definition: 90,
            operation: Operation::Oadd,
            arguments: Arc::new(vec![1, 2]),
            write_bits: Some(32),
        },
    );
    let signed = int(ClightIntSize::I32, true);
    let rhs = ClightExpr::Ebinop(
        ClightBinaryOp::Oadd,
        Box::new(ClightExpr::Etempvar(1, signed.clone())),
        Box::new(ClightExpr::Etempvar(2, signed.clone())),
        signed,
    );
    let store = ClightStmt::Sassign(cell(4, ClightIntSize::I32, false), rhs);
    let check = Validator::new().check(
        WriteValue(&machine, &w),
        &store,
        &HashMap::from([(1, CType::int()), (2, CType::int())]),
        &f,
    );
    assert_eq!(check.verdict, Verdict::Refuted);
    assert_eq!(check.registers, BTreeSet::from([1, 2]));
    assert!(matches!(
        check.witness,
        Some(Witness::Value {
            source_defined: false,
            ..
        })
    ));
    // A proof at a different use must not be borrowed for this store.
    let producer = f.value_producers.remove(&(30, 7)).unwrap();
    f.value_producers.insert((29, 7), producer);
    assert_eq!(
        Validator::new()
            .check(
                WriteValue(&machine, &w),
                &store,
                &HashMap::from([(1, CType::int()), (2, CType::int())]),
                &f
            )
            .verdict,
        Verdict::Unsupported
    );
}

#[test]
fn decoded_zero_upper_word_guides_the_c_load_view_in_final_selection() {
    let (mut f, _) = fixture();
    let read = memory_theory::ReadContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 40,
        root: 10,
        offset: 4,
        width: 4,
        chunk: MemoryChunk::MAny32,
        destination: 13,
        write_bits: Some(32),
        signed_word_load: false,
    };
    let original = ClightStmt::Sset(13, cell(4, ClightIntSize::I32, true));
    let declarations = HashMap::from([(13, CType::long())]);
    let check = Validator::new().check(ReadValue(&read), &original, &declarations, &f);
    assert_eq!(check.verdict, Verdict::Refuted);
    let Some(Witness::Value {
        memory: Some(word),
        machine,
        source,
        ..
    }) = check.witness
    else {
        panic!("missing word witness");
    };
    assert!(word >= 0x8000_0000);
    assert_eq!(machine, word);
    assert_ne!(source, machine);
    f.used_regs.insert(13);
    f.var_type_candidates
        .insert(13, vec![CandType::I64(Sign::Signed)]);
    f.storage_reads.push(read);
    f.node_statements.insert(40, vec![original.clone()]);
    crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(&mut f);
    assert_eq!(f.node_statements[&40].len(), 2);
    assert_eq!(
        f.node_statements[&40][0], original,
        "ordinary fallback must remain available"
    );
    let generated = &f.node_statements[&40][1];
    assert!(f.analysis_candidates[&40].contains(generated));
    assert_eq!(
        Validator::new()
            .check(ReadValue(&f.storage_reads[0]), generated, &declarations, &f)
            .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
            &f,
            &HashMap::new(),
            &[]
        )
        .unwrap()
        .0[&40],
        Some(1)
    );
    crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(&mut f);
    assert_eq!(
        f.node_statements[&40].len(),
        2,
        "the word-view grammar must be finite/idempotent"
    );
}

#[test]
fn signed_load_extension_depends_on_the_machine_destination_not_c_signedness() {
    let (f, _) = fixture();
    let mut read = memory_theory::ReadContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 40,
        root: 10,
        offset: 4,
        width: 1,
        chunk: MemoryChunk::MInt8Signed,
        destination: 13,
        write_bits: Some(64),
        signed_word_load: false,
    };
    let statement = ClightStmt::Sset(13, cell(4, ClightIntSize::I8, true));
    let declarations = HashMap::from([(13, CType::long())]);
    let v = Validator::new();
    assert_eq!(
        v.check(ReadValue(&read), &statement, &declarations, &f)
            .verdict,
        Verdict::Equivalent
    );
    read.write_bits = Some(32);
    assert_eq!(
        v.check(ReadValue(&read), &statement, &declarations, &f)
            .verdict,
        Verdict::Refuted
    );
    // A 32-bit C carrier still represents the low result word correctly.
    assert_eq!(
        v.check(
            ReadValue(&read),
            &statement,
            &HashMap::from([(13, CType::int())]),
            &f
        )
        .verdict,
        Verdict::Equivalent
    );
    read.write_bits = Some(8);
    assert_eq!(
        v.check(ReadValue(&read), &statement, &declarations, &f)
            .verdict,
        Verdict::Unsupported
    );
    read.write_bits = Some(64);
    read.width = 4;
    read.chunk = MemoryChunk::MInt32;
    let statement = ClightStmt::Sset(13, cell(4, ClightIntSize::I32, true));
    assert_eq!(
        v.check(ReadValue(&read), &statement, &declarations, &f)
            .verdict,
        Verdict::Unsupported
    );
    read.signed_word_load = true;
    assert_eq!(
        v.check(ReadValue(&read), &statement, &declarations, &f)
            .verdict,
        Verdict::Equivalent
    );
}

#[test]
fn analysis_candidates_keep_the_parent_structural_world_and_effect_scope() {
    let (mut f, _) = fixture();
    let read = memory_theory::ReadContract {
        object: ObjectId {
            function: 1,
            base: 0,
        },
        node: 40,
        root: 10,
        offset: 4,
        width: 4,
        chunk: MemoryChunk::MAny32,
        destination: 13,
        write_bits: Some(32),
        signed_word_load: false,
    };
    let statement = ClightStmt::Slabel(
        40,
        Box::new(ClightStmt::Sset(13, cell(4, ClightIntSize::I32, true))),
    );
    f.structure_worlds = vec![0, 1];
    f.storage_reads.push(read);
    f.node_statements.insert(40, vec![statement.clone()]);
    f.candidate_structure_worlds
        .insert(40, vec![BTreeSet::from([1])]);
    crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(&mut f);
    assert_eq!(
        f.candidate_structure_worlds[&40],
        vec![BTreeSet::from([1]); 2]
    );
    assert!(matches!(
        &f.node_statements[&40][1],
        ClightStmt::Slabel(40, _)
    ));
    f.node_statements.insert(
        40,
        vec![ClightStmt::Ssequence(vec![statement.clone(), statement])],
    );
    f.candidate_structure_worlds.remove(&40);
    crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(&mut f);
    assert_eq!(
        f.node_statements[&40].len(),
        1,
        "a compound effect must not be replaced by one load view"
    );
}

#[test]
fn a_signed_carrier_requires_a_word_view_at_its_inlined_64_bit_use() {
    let (mut f, _) = fixture();
    let ulong = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
    let carrier = ClightExpr::Etempvar(13, int(ClightIntSize::I32, true));
    let widened = ClightExpr::Ecast(Box::new(carrier), ulong.clone());
    let triple = ClightExpr::Ebinop(
        ClightBinaryOp::Oadd,
        Box::new(widened.clone()),
        Box::new(ClightExpr::Ebinop(
            ClightBinaryOp::Omul,
            Box::new(widened),
            Box::new(ClightExpr::EconstLong(2, ulong.clone())),
            ulong.clone(),
        )),
        ulong.clone(),
    );
    let original = ClightStmt::Sset(
        14,
        ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Etempvar(15, ulong.clone())),
            Box::new(triple),
            ulong,
        ),
    );
    let machine = RTLInst::Iop(
        Operation::Oleal(Addressing::Aindexed2(0)),
        Arc::new(vec![15, 7]),
        14,
    );
    f.word_inputs.insert(40, BTreeSet::from([13]));
    f.value_producers.insert(
        (40, 7),
        crate::decompile::passes::clight_select::solvers::producer_values::Producer {
            definition: 90,
            operation: Operation::Oleal(Addressing::Aindexed2scaled(2, 0)),
            arguments: Arc::new(vec![13, 13]),
            write_bits: Some(64),
        },
    );
    let declarations = HashMap::from([
        (13, CType::int()),
        (14, CType::ulong()),
        (15, CType::ulong()),
    ]);
    let check = Validator::new().check(IntegerAt(40, &machine), &original, &declarations, &f);
    assert_eq!(check.verdict, Verdict::Refuted);
    assert!(matches!(
        check.witness,
        Some(Witness::Value {
            source_defined: true,
            ..
        })
    ));
    f.node_statements.insert(40, vec![original]);
    f.integer_anchors.insert(40, machine.clone());
    for (reg, candidate) in [
        (13, CandType::I32(Sign::Signed)),
        (14, CandType::I64(Sign::Unsigned)),
        (15, CandType::I64(Sign::Unsigned)),
    ] {
        f.used_regs.insert(reg);
        f.var_type_candidates.insert(reg, vec![candidate]);
    }
    crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(&mut f);
    assert_eq!(f.node_statements[&40].len(), 2);
    assert_eq!(
        Validator::new()
            .check(
                IntegerAt(40, &machine),
                &f.node_statements[&40][1],
                &declarations,
                &f
            )
            .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
            &f,
            &HashMap::new(),
            &[]
        )
        .unwrap()
        .0[&40],
        Some(1)
    );
}
