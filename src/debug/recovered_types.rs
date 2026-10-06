//! Read-only observation of final C declarations and native frame provenance.
//! No DWARF, source names, offset calibration, or additional selection occurs.
use crate::abi::DataModel;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::{print::Printer, types::*};
use crate::x86::types::{Address, Node, RTLReg, Symbol};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

pub fn export(db: &DecompileDB, path: &str) -> Result<(), String> {
    let document = collect(db)?;
    let encoded = serde_json::to_vec_pretty(&document).map_err(|e| e.to_string())?;
    if let Some(parent) = std::path::Path::new(path)
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    std::fs::write(path, encoded).map_err(|e| e.to_string())
}

fn describe(ty: &CType, model: DataModel) -> Value {
    let mut printer = Printer::with_default_config();
    printer.print_type(ty);
    let (kind, size) = match ty {
        CType::Int(size, _) => (
            "integer",
            Some(match size {
                IntSize::Char => 1,
                IntSize::Short => 2,
                IntSize::Int => 4,
                IntSize::Long => model.long_size(),
                IntSize::LongLong => 8,
                IntSize::Int128 => 16,
            }),
        ),
        CType::Bool => ("boolean", Some(1)),
        CType::Float(FloatSize::Float) => ("float", Some(4)),
        CType::Float(FloatSize::Double) => ("float", Some(8)),
        CType::Float(_) => ("float", None),
        CType::Pointer(..) => ("pointer", Some(model.pointer_size())),
        CType::Array(element, count) => (
            "array",
            count.and_then(|n| {
                describe(element, model)["size"]
                    .as_u64()
                    .and_then(|s| n.checked_mul(s as usize))
            }),
        ),
        CType::Struct(_) => ("struct", None),
        CType::Union(_) => ("union", None),
        CType::Enum(_) => ("enum", None),
        CType::Function(..) => ("function", None),
        CType::Qualified(inner, _) => return describe(inner, model),
        _ => ("unknown", None),
    };
    let spelling = if matches!(ty, CType::Bool) {
        "_Bool".to_string() // matches the printed declaration (print_var_decl)
    } else {
        printer.into_string()
    };
    let mut result = json!({"spelling":spelling, "kind":kind, "size":size});
    match ty {
        CType::Pointer(inner, _) => result["pointee"] = describe(inner, model),
        CType::Array(inner, n) => {
            result["element"] = describe(inner, model);
            result["count"] = json!(n);
        }
        _ => {}
    }
    result
}

#[derive(Default)]
struct Declarations(BTreeMap<String, Option<CType>>);
impl Declarations {
    fn add(&mut self, name: &str, ty: &CType) {
        self.0
            .entry(name.into())
            .and_modify(|previous| {
                if previous.as_ref() != Some(ty) {
                    *previous = None;
                }
            })
            .or_insert_with(|| Some(ty.clone()));
    }
}
impl ExprTransform for Declarations {
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for Declarations {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        match &stmt {
            CStmt::Decl(decls) | CStmt::For(Some(ForInit::Decl(decls)), _, _, _) => {
                for decl in decls {
                    self.add(&decl.name, &decl.ty);
                }
            }
            CStmt::Block(items) => {
                for item in items {
                    if let CBlockItem::Decl(decls) = item {
                        for decl in decls {
                            self.add(&decl.name, &decl.ty);
                        }
                    }
                }
            }
            _ => {}
        }
        self.walk_stmt(stmt)
    }
}

pub fn collect(db: &DecompileDB) -> Result<Value, String> {
    let tu = db
        .cast_optimized_translation_unit
        .as_ref()
        .ok_or("no admitted C translation unit")?;
    let mut declarations = BTreeMap::new();
    for declaration in &tu.decls {
        if let TopLevelDecl::FuncDef(function) = declaration {
            let mut vars = Declarations::default();
            for var in &function.local_vars {
                vars.add(&var.name, &var.ty);
            }
            for param in &function.params {
                if let Some(name) = &param.name {
                    vars.add(name, &param.ty);
                }
            }
            vars.transform_stmt(function.body.clone());
            declarations.insert(function.name.clone(), vars.0);
        }
    }
    let canonical: BTreeMap<RTLReg, RTLReg> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let canonical_reg = |r: RTLReg| canonical.get(&r).copied().unwrap_or(r);
    let mut origins = BTreeMap::<(Address, RTLReg), BTreeSet<(String, String)>>::new();
    for (function, reg, owner, name) in
        db.rel_iter::<(Address, RTLReg, String, String)>("emit_c_variable_origin")
    {
        origins
            .entry((*function, canonical_reg(*reg)))
            .or_default()
            .insert((owner.clone(), name.clone()));
    }
    let proven_bp: BTreeSet<_> = db
        .rel_iter::<(Address, Node, i64)>("settled_bp_frame_base")
        .map(|&(f, n, _)| (f, n))
        .collect();
    let memories: BTreeMap<_, _> = db
        .rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
        .filter(|(_, s, b, i, _, _, _)| {
            (*s == "NONE" || s.is_empty()) && *b == "RBP" && (*i == "NONE" || i.is_empty())
        })
        .map(|(symbol, _, _, _, _, disp, _)| (*symbol, *disp))
        .collect();
    let mut raw_offsets = BTreeMap::<Node, BTreeSet<i64>>::new();
    for (n, _, _, _, a, b, c, d, _, _) in db.rel_iter::<(
        Address,
        usize,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        usize,
        usize,
    )>("instruction")
    {
        for operand in [a, b, c, d] {
            if let Some(offset) = memories.get(operand) {
                raw_offsets.entry(*n).or_default().insert(*offset);
            }
        }
    }
    let mut slots = BTreeMap::<(Address, Node), BTreeSet<(i64, RTLReg)>>::new();
    for &(f, n, o, r) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        slots
            .entry((f, n))
            .or_default()
            .insert((o, canonical_reg(r)));
    }
    let mut rows = BTreeMap::<(Address, String, String, i64), BTreeSet<Node>>::new();
    // A selected value partition projects only the binding at this native
    // storage event. Other temporaries sharing its old RTL name cannot acquire
    // a stack coordinate merely by copying that name's provenance.
    let mut binding_storage = BTreeMap::<(Address, Node, RTLReg), BTreeSet<RTLReg>>::new();
    for &(f, n, native, binding) in
        db.rel_iter::<(Address, Node, RTLReg, RTLReg)>("selection_binding_storage")
    {
        binding_storage
            .entry((f, n, canonical_reg(native)))
            .or_default()
            .insert(binding);
    }
    let mut unmapped = 0;
    for ((f, n), cells) in slots {
        let offsets = raw_offsets.get(&n);
        // A native event may associate several SSA incarnations of one cell,
        // but cannot donate a displacement to a different cell at that event.
        if !proven_bp.contains(&(f, n))
            || offsets.is_none_or(|o| o.len() != 1)
            || cells.iter().map(|(o, _)| o).collect::<BTreeSet<_>>().len() != 1
        {
            unmapped += 1;
            continue;
        }
        let offset = *offsets.unwrap().first().unwrap();
        for (_, reg) in cells {
            let bindings: Vec<_> = binding_storage
                .get(&(f, n, reg))
                .map(|ids| ids.iter().copied().collect())
                .unwrap_or_else(|| vec![reg]);
            for reg in bindings {
                if let Some(names) = origins.get(&(f, reg)) {
                    for (owner, name) in names {
                        if declarations
                            .get(owner)
                            .and_then(|v| v.get(name))
                            .and_then(Option::as_ref)
                            .is_some()
                        {
                            rows.entry((f, owner.clone(), name.clone(), offset))
                                .or_default()
                                .insert(n);
                        }
                    }
                }
            }
        }
    }
    let variables: Vec<_> = rows
        .into_iter()
        .map(|((f, owner, name, offset), points)| {
            json!({
                "function_address":f, "function_name":owner, "name":name, "rbp_offset":offset,
                "type":describe(declarations[&owner][&name].as_ref().unwrap(),db.data_model()),
                "evidence_nodes":points,
            })
        })
        .collect();
    use crate::decompile::passes::clight_select::type_graph::TypeAdmission;
    let mut type_admissions = BTreeMap::<&str, usize>::new();
    for (_, _, status) in
        db.rel_iter::<(Address, RTLReg, TypeAdmission)>("selection_type_admission")
    {
        let label = match status {
            TypeAdmission::LegacyFallback => "legacy_unverified",
            TypeAdmission::EvidenceSupported => "evidence_unverified",
            TypeAdmission::ValueAndDefinedness => "value_definedness",
            TypeAdmission::ExplicitPointerViews => "explicit_pointer_views",
        };
        *type_admissions.entry(label).or_default() += 1;
    }
    Ok(
        json!({"schema_version":1, "representation":"final-c", "coordinate":"rbp",
        "mapping":"unambiguous-native-frame-access", "unmapped_events":unmapped,
        "type_admissions":type_admissions,
        "variables":variables}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> DecompileDB {
        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        let (function, node, reg) = (100_u64, 7_u64, 11_u64);
        let mut tu = TranslationUnit::new();
        tu.add_function(FuncDef {
            name: "FUN_64".into(),
            return_type: CType::ulong(),
            params: vec![],
            is_variadic: false,
            storage_class: StorageClass::Auto,
            body: CStmt::Return(Some(CExpr::Var("var_0".into()))),
            local_vars: vec![VarDecl::new("var_0", CType::ulong())],
            loc: SourceLoc::unknown(),
        });
        db.cast_optimized_translation_unit = Some(tu);
        db.rel_push(
            "emit_c_variable_origin",
            (function, reg, "FUN_64".to_owned(), "var_0".to_owned()),
        );
        db.rel_push("stack_var", (function, node, -24_i64, reg));
        db.rel_push("settled_bp_frame_base", (function, node, -8_i64));
        db.rel_push(
            "instruction",
            (
                node,
                4_usize,
                "",
                "MOV",
                "slot",
                "destination",
                "",
                "",
                0_usize,
                0_usize,
            ),
        );
        db.rel_push(
            "op_indirect",
            ("slot", "NONE", "RBP", "NONE", 1_i64, -24_i64, 8_usize),
        );
        db
    }
    #[test]
    fn descriptors_preserve_width_and_array_shape() {
        assert_eq!(describe(&CType::ulong(), DataModel::Lp64)["size"], 8);
        assert_eq!(
            describe(&CType::array(CType::uint(), 3), DataModel::Lp64)["size"],
            12
        );
        assert_eq!(
            describe(&CType::ptr(CType::uint()), DataModel::Lp64)["pointee"]["size"],
            4
        );
    }
    #[test]
    fn shadowed_different_declarations_are_not_guessed() {
        let mut vars = Declarations::default();
        vars.add("v", &CType::int());
        vars.add("v", &CType::long());
        assert_eq!(vars.0["v"], None);
    }
    #[test]
    fn reads_final_types_without_reselection_or_debug_names() {
        let mut db = fixture();
        db.effect_epoch = 9;
        let before = collect(&db).unwrap();
        assert_eq!(before["variables"][0]["function_address"], 100);
        assert_eq!(before["variables"][0]["rbp_offset"], -24);
        assert_eq!(before["variables"][0]["type"]["size"], 8);
        if let TopLevelDecl::FuncDef(f) =
            &mut db.cast_optimized_translation_unit.as_mut().unwrap().decls[0]
        {
            f.local_vars[0].ty = CType::uint();
        }
        assert_eq!(collect(&db).unwrap()["variables"][0]["type"]["size"], 4);
        assert_eq!(db.effect_epoch, 9);
        assert!(db.clight_selected_functions.is_empty());
    }
    #[test]
    fn removed_declarations_and_foreign_point_proofs_get_no_credit() {
        let mut db = fixture();
        let wrong: Vec<(Address, Node, i64)> = vec![(100, 8, -8)];
        db.rel_set(
            "settled_bp_frame_base",
            wrong.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
        assert_eq!(
            collect(&db).unwrap()["variables"].as_array().unwrap().len(),
            0
        );
        db = fixture();
        if let TopLevelDecl::FuncDef(f) =
            &mut db.cast_optimized_translation_unit.as_mut().unwrap().decls[0]
        {
            f.local_vars.clear();
            f.body = CStmt::Return(Some(CExpr::int(0)));
        }
        assert_eq!(
            collect(&db).unwrap()["variables"].as_array().unwrap().len(),
            0
        );
    }
    #[test]
    fn partitioned_bindings_keep_every_exact_event_origin_and_no_foreign_one() {
        let mut db = fixture();
        if let TopLevelDecl::FuncDef(f) =
            &mut db.cast_optimized_translation_unit.as_mut().unwrap().decls[0]
        {
            f.local_vars.extend([
                VarDecl::new("before", CType::uint()),
                VarDecl::new("after", CType::uint()),
                VarDecl::new("temporary", CType::ulong()),
            ]);
        }
        for (binding, name, node) in [
            (21_u64, "before", 7_u64),
            (22, "after", 7),
            (23, "temporary", 8),
        ] {
            db.rel_push(
                "emit_c_variable_origin",
                (100_u64, binding, "FUN_64".to_owned(), name.to_owned()),
            );
            db.rel_push(
                "selection_binding_storage",
                (100_u64, node, 11_u64, binding),
            );
        }
        let result = collect(&db).unwrap();
        let names: BTreeSet<_> = result["variables"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v["name"].as_str().unwrap())
            .collect();
        assert_eq!(names, BTreeSet::from(["before", "after"]));
        assert!(result["variables"]
            .as_array()
            .unwrap()
            .iter()
            .all(|v| v["rbp_offset"] == -24));
    }
    #[test]
    fn export_creates_the_requested_output_directory() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "manifold-type-export-{}-{unique}",
            std::process::id()
        ));
        std::fs::create_dir(&directory).unwrap();
        let output = directory.join("nested/result.types.json");
        export(&fixture(), output.to_str().unwrap()).unwrap();
        let value: Value = serde_json::from_slice(&std::fs::read(&output).unwrap()).unwrap();
        assert_eq!(value["representation"], "final-c");
        std::fs::remove_dir_all(directory).unwrap();
    }
}
