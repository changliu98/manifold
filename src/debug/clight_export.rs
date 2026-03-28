// Export selected Clight IR to JSON mirroring CompCert's Clight AST for OCaml-side reconstruction.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::query::{extract_globals, extract_struct_definitions};
use crate::decompile::passes::clight_select::select::{select_clight_stmts, SelectedFunction};
use crate::x86::types::*;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

/// Export the selected Clight IR from the decompile DB to a JSON file.
pub fn export_clight_json(db: &DecompileDB, output_path: &str) -> Result<(), String> {
    // Diagnostics
    let csharp_count = db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt").count();
    let clight_wf_count = db.rel_iter::<(Node, ClightStmt)>("clight_stmt_without_field").count();
    let clight_count = db.rel_iter::<(Node, ClightStmt)>("clight_stmt").count();
    let emit_wf_count = db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt_without_field").count();
    let emit_count = db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt").count();
    let var_type_count = db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate").count();
    eprintln!("=== Clight Pipeline Diagnostics ===");
    eprintln!("  csharp_stmt:                    {}", csharp_count);
    eprintln!("  clight_stmt_without_field:      {}", clight_wf_count);
    eprintln!("  clight_stmt:                    {}", clight_count);
    eprintln!("  emit_clight_stmt_without_field: {}", emit_wf_count);
    eprintln!("  emit_clight_stmt:               {}", emit_count);
    eprintln!("  emit_var_type:                  {}", var_type_count);

    // Check specific nodes for square function
    for (node, stmt) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
        if *node == 0x1137 || *node == 0x113b || *node == 0x1129 || *node == 0x1134 {
            eprintln!("  csharp_stmt(0x{:x}): {:?}", node, stmt);
        }
    }
    let reg_dst: u64 = 9223372036855057664;
    let reg_src: u64 = 9223372036855056965;
    for (reg, xty) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
        if *reg == reg_dst || *reg == reg_src {
            eprintln!("  emit_var_type(reg={}): {:?}", reg, xty);
        }
    }
    for (reg,) in db.rel_iter::<(RTLReg,)>("is_ptr") {
        if *reg == reg_dst || *reg == reg_src {
            eprintln!("  is_ptr(reg={})", reg);
        }
    }
    for (node, stmt) in db.rel_iter::<(Node, ClightStmt)>("clight_stmt_without_field") {
        if *node >= 0x1129 && *node <= 0x113b {
            eprintln!("  clight_stmt_without_field(0x{:x}): {:?}", node, stmt);
        }
    }
    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        if *addr == 0x1129 {
            eprintln!("  emit_clight_stmt(func=0x{:x}, node=0x{:x}): {:?}", addr, node, stmt);
        }
    }
    eprintln!("=== End Diagnostics ===\n");

    let selected_functions = select_clight_stmts(db)?;

    let binary_path = db
        .binary_path
        .as_ref()
        .ok_or("binary_path not set")?;

    // Build id_to_name mapping
    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        id_to_name
            .entry(*id)
            .and_modify(|existing| {
                if name.len() < existing.len() {
                    *existing = name.to_string();
                }
            })
            .or_insert_with(|| name.to_string());
    }
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        id_to_name.entry(*addr as usize).or_insert_with(|| name.to_string());
    }
    for func in &selected_functions {
        id_to_name
            .entry(func.address as usize)
            .or_insert_with(|| func.name.clone());
    }

    let external_funcs: std::collections::HashSet<u64> = db
        .rel_iter::<(Address,)>("is_external_function")
        .map(|(a,)| *a)
        .collect();

    const CRT_FUNCTIONS: &[&str] = &[
        "_start", "_init", "_fini",
        "__libc_csu_init", "__libc_csu_fini", "__libc_start_main",
        "deregister_tm_clones", "register_tm_clones",
        "__do_global_dtors_aux", "frame_dummy",
        "__x86.get_pc_thunk.bx",
    ];

    let internal_functions: Vec<&SelectedFunction> = selected_functions
        .iter()
        .filter(|func| {
            !external_funcs.contains(&func.address)
                && !func.name.starts_with('.')
                && !func.name.starts_with("__")
                && !CRT_FUNCTIONS.contains(&func.name.as_str())
                && !func.name.starts_with("FUN_")
                && !db.should_skip_function(func.name.as_str())
        })
        .collect();

    // Extract struct definitions (composites)
    let struct_defs = extract_struct_definitions(db);
    let composites: Vec<Value> = struct_defs
        .iter()
        .map(|s| {
            let fields: Vec<Value> = s.definition.fields.iter().map(|f| {
                json!({
                    "name": f.name,
                    "ty": serialize_ctype_from_field(&f.ty)
                })
            }).collect();
            json!({
                "id": s.struct_id,
                "name": format!("struct_{:x}", s.struct_id),
                "su": "Struct",
                "members": fields
            })
        })
        .collect();

    // Extract globals
    let globals = extract_globals(db, binary_path).unwrap_or_default();
    let globals_json: Vec<Value> = globals
        .iter()
        .map(|g| {
            let mut obj = json!({
                "name": g.name,
                "id": g.id,
                "is_string": g.is_string,
                "is_pointer": g.is_pointer,
            });
            if g.is_string {
                let s = String::from_utf8_lossy(&g.content)
                    .trim_end_matches('\0')
                    .to_string();
                obj["string_value"] = json!(s);
            }
            obj
        })
        .collect();

    // Collect names of functions that are actually called from internal functions
    let internal_names: std::collections::HashSet<&str> = internal_functions
        .iter()
        .map(|f| f.name.as_str())
        .collect();
    let mut called_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    for func in &internal_functions {
        for stmt in func.statements.values() {
            collect_called_functions(stmt, &mut called_names);
        }
    }

    // Build external function declarations (only for actually-called externals)
    let extern_sigs: Vec<Value> = db
        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        .filter(|(name, _, _, _)| {
            called_names.contains(*name) && !internal_names.contains(*name)
        })
        .map(|(name, param_count, ret_type, param_types)| {
            json!({
                "name": name.to_string(),
                "param_count": param_count,
                "return_type": serialize_xtype(ret_type),
                "param_types": param_types.iter().map(serialize_xtype).collect::<Vec<_>>()
            })
        })
        .collect();

    // Serialize internal functions
    let functions_json: Vec<Value> = internal_functions
        .iter()
        .map(|func| serialize_function(func, &id_to_name))
        .collect();

    let program = json!({
        "compcert_clight": true,
        "arch": "x86_64",
        "composites": composites,
        "globals": globals_json,
        "externals": extern_sigs,
        "functions": functions_json,
    });

    let json_str = serde_json::to_string_pretty(&program)
        .map_err(|e| format!("JSON serialization error: {}", e))?;

    std::fs::write(output_path, json_str)
        .map_err(|e| format!("Failed to write {}: {}", output_path, e))?;

    Ok(())
}

fn serialize_function(func: &SelectedFunction, id_to_name: &HashMap<usize, String>) -> Value {
    // Build a local name map including param/temp register names for consistent identifiers.
    let mut local_names = id_to_name.clone();
    for reg in &func.param_regs {
        local_names.entry(*reg as usize).or_insert_with(|| format!("param_{}", reg));
    }
    let param_set: std::collections::HashSet<RTLReg> =
        func.param_regs.iter().copied().collect();
    for reg in &func.used_regs {
        if !param_set.contains(reg) {
            local_names.entry(*reg as usize).or_insert_with(|| format!("var_{}", reg));
        }
    }

    // Serialize parameters
    let params: Vec<Value> = func
        .param_regs
        .iter()
        .zip(func.param_types.iter())
        .map(|(reg, pty)| {
            json!({
                "id": *reg as usize,
                "name": resolve_name(*reg as usize, &local_names),
                "ty": serialize_param_type(pty)
            })
        })
        .collect();

    // Collect local variables (temps): all used regs minus params
    let mut temps: Vec<Value> = func
        .used_regs
        .iter()
        .filter(|r| !param_set.contains(r))
        .map(|reg| {
            let ty = func
                .var_types
                .get(reg)
                .map(|s| xtype_string_to_clight_type(s))
                .unwrap_or_else(|| json!({"tag": "Tlong", "sign": "Unsigned"}));
            json!({
                "id": *reg as usize,
                "name": resolve_name(*reg as usize, &local_names),
                "ty": ty
            })
        })
        .collect();
    temps.sort_by_key(|v| v["id"].as_u64().unwrap_or(0));

    // Build the function body: right-fold Ssequence over sorted nodes
    let body = serialize_function_body(func, &local_names);

    // Serialize successors (CFG edges)
    let cfg: Vec<Value> = func
        .successors
        .iter()
        .flat_map(|(src, dsts)| dsts.iter().map(move |dst| json!([*src, *dst])))
        .collect();

    json!({
        "name": func.name,
        "address": format!("0x{:x}", func.address),
        "entry_node": func.entry_node,
        "return_type": serialize_clight_type(&func.return_type),
        "callconv": "cc_default",
        "params": params,
        "temps": temps,
        "vars": [],
        "body": body,
        "cfg": cfg,
        "stack_size": func.stack_size,
    })
}

/// Serialize all statements for a function, providing both per-node and flattened CFG representations.
fn serialize_function_body(
    func: &SelectedFunction,
    id_to_name: &HashMap<usize, String>,
) -> Value {
    // Per-node statements (preserves CFG structure)
    let mut node_stmts: Vec<(Node, Value)> = func
        .statements
        .iter()
        .map(|(node, stmt)| (*node, serialize_stmt(stmt, id_to_name)))
        .collect();
    node_stmts.sort_by_key(|(n, _)| *n);

    // Build a right-folded Ssequence from address-ordered statements
    if node_stmts.is_empty() {
        return json!({"tag": "Sskip"});
    }

    // Return as a structured object with both representations
    json!({
        "node_stmts": node_stmts.iter().map(|(n, s)| {
            json!({"node": *n, "stmt": s.clone()})
        }).collect::<Vec<_>>(),
        "sequence": fold_ssequence(&node_stmts.iter().map(|(_, s)| s.clone()).collect::<Vec<_>>()),
    })
}

/// Right-fold a list of statements into nested Ssequence (CompCert's binary form).
fn fold_ssequence(stmts: &[Value]) -> Value {
    match stmts.len() {
        0 => json!({"tag": "Sskip"}),
        1 => stmts[0].clone(),
        _ => json!({
            "tag": "Ssequence",
            "s1": stmts[0].clone(),
            "s2": fold_ssequence(&stmts[1..])
        }),
    }
}

fn serialize_stmt(stmt: &ClightStmt, id_to_name: &HashMap<usize, String>) -> Value {
    match stmt {
        ClightStmt::Sskip => json!({"tag": "Sskip"}),

        ClightStmt::Sassign(lhs, rhs) => json!({
            "tag": "Sassign",
            "lhs": serialize_expr(lhs, id_to_name),
            "rhs": serialize_expr(rhs, id_to_name),
        }),

        ClightStmt::Sset(id, expr) => json!({
            "tag": "Sset",
            "id": *id,
            "name": resolve_name(*id, id_to_name),
            "rhs": serialize_expr(expr, id_to_name),
        }),

        ClightStmt::Scall(opt_id, func_expr, args) => {
            let mut obj = json!({
                "tag": "Scall",
                "func": serialize_expr(func_expr, id_to_name),
                "args": args.iter().map(|a| serialize_expr(a, id_to_name)).collect::<Vec<_>>(),
            });
            if let Some(id) = opt_id {
                obj["result_id"] = json!(*id);
                obj["result_name"] = json!(resolve_name(*id, id_to_name));
            }
            obj
        }

        ClightStmt::Sbuiltin(opt_id, ef, tys, args) => {
            let mut obj = json!({
                "tag": "Sbuiltin",
                "ef": serialize_external_function(ef),
                "arg_types": tys.iter().map(serialize_clight_type).collect::<Vec<_>>(),
                "args": args.iter().map(|a| serialize_expr(a, id_to_name)).collect::<Vec<_>>(),
            });
            if let Some(id) = opt_id {
                obj["result_id"] = json!(*id);
            }
            obj
        }

        ClightStmt::Ssequence(stmts) => {
            let serialized: Vec<Value> = stmts
                .iter()
                .map(|s| serialize_stmt(s, id_to_name))
                .collect();
            fold_ssequence(&serialized)
        }

        ClightStmt::Sifthenelse(cond, then_s, else_s) => json!({
            "tag": "Sifthenelse",
            "cond": serialize_expr(cond, id_to_name),
            "then": serialize_stmt(then_s, id_to_name),
            "else": serialize_stmt(else_s, id_to_name),
        }),

        ClightStmt::Sloop(s1, s2) => json!({
            "tag": "Sloop",
            "body1": serialize_stmt(s1, id_to_name),
            "body2": serialize_stmt(s2, id_to_name),
        }),

        ClightStmt::Sbreak => json!({"tag": "Sbreak"}),
        ClightStmt::Scontinue => json!({"tag": "Scontinue"}),

        ClightStmt::Sreturn(opt_expr) => {
            let mut obj = json!({"tag": "Sreturn"});
            if let Some(expr) = opt_expr {
                obj["expr"] = serialize_expr(expr, id_to_name);
            }
            obj
        }

        ClightStmt::Sswitch(expr, cases) => json!({
            "tag": "Sswitch",
            "expr": serialize_expr(expr, id_to_name),
            "cases": cases.iter().map(|(label, s)| {
                json!({
                    "label": match label {
                        Some(z) => json!(*z),
                        None => json!("default"),
                    },
                    "stmt": serialize_stmt(s, id_to_name),
                })
            }).collect::<Vec<_>>(),
        }),

        ClightStmt::Slabel(id, s) => json!({
            "tag": "Slabel",
            "label": *id,
            "label_name": resolve_name(*id, id_to_name),
            "stmt": serialize_stmt(s, id_to_name),
        }),

        ClightStmt::Sgoto(id) => json!({
            "tag": "Sgoto",
            "label": *id,
            "label_name": resolve_name(*id, id_to_name),
        }),
    }
}

fn serialize_expr(expr: &ClightExpr, id_to_name: &HashMap<usize, String>) -> Value {
    match expr {
        ClightExpr::EconstInt(v, ty) => json!({
            "tag": "Econst_int",
            "value": *v,
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::EconstLong(v, ty) => json!({
            "tag": "Econst_long",
            "value": *v,
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::EconstFloat(v, ty) => json!({
            "tag": "Econst_float",
            "value": v.0,
            "bits": v.0.to_bits(),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::EconstSingle(v, ty) => json!({
            "tag": "Econst_single",
            "value": v.0,
            "bits": v.0.to_bits(),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Evar(id, ty) => json!({
            "tag": "Evar",
            "id": *id,
            "name": resolve_name(*id, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::EvarSymbol(name, ty) => json!({
            "tag": "Evar",
            "name": name,
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Etempvar(id, ty) => json!({
            "tag": "Etempvar",
            "id": *id,
            "name": resolve_name(*id, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Ederef(inner, ty) => json!({
            "tag": "Ederef",
            "expr": serialize_expr(inner, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Eaddrof(inner, ty) => json!({
            "tag": "Eaddrof",
            "expr": serialize_expr(inner, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Eunop(op, inner, ty) => json!({
            "tag": "Eunop",
            "op": serialize_unop(op),
            "expr": serialize_expr(inner, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Ebinop(op, lhs, rhs, ty) => json!({
            "tag": "Ebinop",
            "op": serialize_binop(op),
            "lhs": serialize_expr(lhs, id_to_name),
            "rhs": serialize_expr(rhs, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Ecast(inner, ty) => json!({
            "tag": "Ecast",
            "expr": serialize_expr(inner, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Efield(base, field_id, ty) => json!({
            "tag": "Efield",
            "base": serialize_expr(base, id_to_name),
            "field": *field_id,
            "field_name": resolve_name(*field_id, id_to_name),
            "ty": serialize_clight_type(ty),
        }),

        ClightExpr::Esizeof(ty1, ty2) => json!({
            "tag": "Esizeof",
            "sizeof_ty": serialize_clight_type(ty1),
            "ty": serialize_clight_type(ty2),
        }),

        ClightExpr::Ealignof(ty1, ty2) => json!({
            "tag": "Ealignof",
            "alignof_ty": serialize_clight_type(ty1),
            "ty": serialize_clight_type(ty2),
        }),

        ClightExpr::Econdition(cond, then_e, else_e, ty) => json!({
            "tag": "Econdition",
            "cond": serialize_expr(cond, id_to_name),
            "then": serialize_expr(then_e, id_to_name),
            "else": serialize_expr(else_e, id_to_name),
            "ty": serialize_clight_type(ty),
        }),
    }
}

fn serialize_clight_type(ty: &ClightType) -> Value {
    match ty {
        ClightType::Tvoid => json!({"tag": "Tvoid"}),

        ClightType::Tint(size, sign, attr) => json!({
            "tag": "Tint",
            "size": match size {
                ClightIntSize::I8 => "I8",
                ClightIntSize::I16 => "I16",
                ClightIntSize::I32 => "I32",
                ClightIntSize::IBool => "IBool",
            },
            "sign": match sign {
                ClightSignedness::Signed => "Signed",
                ClightSignedness::Unsigned => "Unsigned",
            },
            "attr": serialize_attr(attr),
        }),

        ClightType::Tlong(sign, attr) => json!({
            "tag": "Tlong",
            "sign": match sign {
                ClightSignedness::Signed => "Signed",
                ClightSignedness::Unsigned => "Unsigned",
            },
            "attr": serialize_attr(attr),
        }),

        ClightType::Tfloat(size, attr) => json!({
            "tag": "Tfloat",
            "size": match size {
                ClightFloatSize::F32 => "F32",
                ClightFloatSize::F64 => "F64",
            },
            "attr": serialize_attr(attr),
        }),

        ClightType::Tpointer(inner, attr) => json!({
            "tag": "Tpointer",
            "inner": serialize_clight_type(inner),
            "attr": serialize_attr(attr),
        }),

        ClightType::Tarray(elem, size, attr) => json!({
            "tag": "Tarray",
            "elem": serialize_clight_type(elem),
            "size": *size,
            "attr": serialize_attr(attr),
        }),

        ClightType::Tfunction(param_types, ret_type, cc) => json!({
            "tag": "Tfunction",
            "params": param_types.iter().map(serialize_clight_type).collect::<Vec<_>>(),
            "return": serialize_clight_type(ret_type),
            "cc": serialize_callconv(cc),
        }),

        ClightType::Tstruct(id, attr) => json!({
            "tag": "Tstruct",
            "id": *id,
            "attr": serialize_attr(attr),
        }),

        ClightType::Tunion(id, attr) => json!({
            "tag": "Tunion",
            "id": *id,
            "attr": serialize_attr(attr),
        }),
    }
}

fn serialize_attr(attr: &ClightAttr) -> Value {
    if !attr.attr_volatile && attr.attr_alignas.is_none() {
        return json!(null);
    }
    let mut obj = json!({});
    if attr.attr_volatile {
        obj["volatile"] = json!(true);
    }
    if let Some(align) = attr.attr_alignas {
        obj["alignas"] = json!(align);
    }
    obj
}

fn serialize_callconv(cc: &CallConv) -> Value {
    if cc.varargs.is_none() && !cc.unproto && !cc.structured_ret {
        return json!("cc_default");
    }
    json!({
        "varargs": cc.varargs,
        "unproto": cc.unproto,
        "structret": cc.structured_ret,
    })
}

fn serialize_unop(op: &ClightUnaryOp) -> &'static str {
    match op {
        ClightUnaryOp::Onotbool => "Onotbool",
        ClightUnaryOp::Onotint => "Onotint",
        ClightUnaryOp::Oneg => "Oneg",
        ClightUnaryOp::Oabsfloat => "Oabsfloat",
    }
}

fn serialize_binop(op: &ClightBinaryOp) -> &'static str {
    match op {
        ClightBinaryOp::Oadd => "Oadd",
        ClightBinaryOp::Osub => "Osub",
        ClightBinaryOp::Omul => "Omul",
        ClightBinaryOp::Odiv => "Odiv",
        ClightBinaryOp::Omod => "Omod",
        ClightBinaryOp::Oand => "Oand",
        ClightBinaryOp::Oor => "Oor",
        ClightBinaryOp::Oxor => "Oxor",
        ClightBinaryOp::Oshl => "Oshl",
        ClightBinaryOp::Oshr => "Oshr",
        ClightBinaryOp::Oeq => "Oeq",
        ClightBinaryOp::One => "One",
        ClightBinaryOp::Olt => "Olt",
        ClightBinaryOp::Ogt => "Ogt",
        ClightBinaryOp::Ole => "Ole",
        ClightBinaryOp::Oge => "Oge",
    }
}

fn serialize_param_type(pty: &ParamType) -> Value {
    match pty {
        ParamType::Pointer => json!({"tag": "Tpointer", "inner": {"tag": "Tvoid"}, "attr": null}),
        ParamType::StructPointer(id) => json!({
            "tag": "Tpointer",
            "inner": {"tag": "Tstruct", "id": *id, "attr": null},
            "attr": null,
        }),
        ParamType::Typed(xtype) => xtype_to_clight_type_json(xtype),
        ParamType::Integer => json!({"tag": "Tlong", "sign": "Unsigned", "attr": null}),
        ParamType::Unknown => json!({"tag": "Tlong", "sign": "Unsigned", "attr": null}),
    }
}

fn serialize_xtype(xtype: &XType) -> Value {
    json!(match xtype {
        XType::Xbool => "Xbool",
        XType::Xint8signed => "Xint8signed",
        XType::Xint8unsigned => "Xint8unsigned",
        XType::Xint16signed => "Xint16signed",
        XType::Xint16unsigned => "Xint16unsigned",
        XType::Xint => "Xint",
        XType::Xintunsigned => "Xintunsigned",
        XType::Xlong => "Xlong",
        XType::Xlongunsigned => "Xlongunsigned",
        XType::Xfloat => "Xfloat",
        XType::Xsingle => "Xsingle",
        XType::Xptr => "Xptr",
        XType::Xcharptr => "Xcharptr",
        XType::Xintptr => "Xintptr",
        XType::Xfloatptr => "Xfloatptr",
        XType::Xsingleptr => "Xsingleptr",
        XType::Xfuncptr => "Xfuncptr",
        XType::Xvoid => "Xvoid",
        XType::Xany32 => "Xany32",
        XType::Xany64 => "Xany64",
        XType::XstructPtr(_) => "Xptr",
    })
}

fn xtype_to_clight_type_json(xtype: &XType) -> Value {
    match xtype {
        XType::Xbool => json!({"tag": "Tint", "size": "IBool", "sign": "Unsigned", "attr": null}),
        XType::Xint8signed => json!({"tag": "Tint", "size": "I8", "sign": "Signed", "attr": null}),
        XType::Xint8unsigned => json!({"tag": "Tint", "size": "I8", "sign": "Unsigned", "attr": null}),
        XType::Xint16signed => json!({"tag": "Tint", "size": "I16", "sign": "Signed", "attr": null}),
        XType::Xint16unsigned => json!({"tag": "Tint", "size": "I16", "sign": "Unsigned", "attr": null}),
        XType::Xint | XType::Xany32 => json!({"tag": "Tint", "size": "I32", "sign": "Signed", "attr": null}),
        XType::Xintunsigned => json!({"tag": "Tint", "size": "I32", "sign": "Unsigned", "attr": null}),
        XType::Xlong | XType::Xany64 => json!({"tag": "Tlong", "sign": "Signed", "attr": null}),
        XType::Xlongunsigned => json!({"tag": "Tlong", "sign": "Unsigned", "attr": null}),
        XType::Xfloat => json!({"tag": "Tfloat", "size": "F64", "attr": null}),
        XType::Xsingle => json!({"tag": "Tfloat", "size": "F32", "attr": null}),
        XType::Xptr | XType::Xcharptr | XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr => {
            json!({"tag": "Tpointer", "inner": {"tag": "Tvoid"}, "attr": null})
        }
        XType::XstructPtr(id) => json!({
            "tag": "Tpointer",
            "inner": {"tag": "Tstruct", "id": *id, "attr": null},
            "attr": null,
        }),
        XType::Xvoid => json!({"tag": "Tvoid"}),
    }
}

fn xtype_string_to_clight_type(s: &str) -> Value {
    match s {
        "int_IBool" => json!({"tag": "Tint", "size": "IBool", "sign": "Unsigned", "attr": null}),
        "int_I8" => json!({"tag": "Tint", "size": "I8", "sign": "Signed", "attr": null}),
        "int_I8_unsigned" => json!({"tag": "Tint", "size": "I8", "sign": "Unsigned", "attr": null}),
        "int_I16" => json!({"tag": "Tint", "size": "I16", "sign": "Signed", "attr": null}),
        "int_I16_unsigned" => json!({"tag": "Tint", "size": "I16", "sign": "Unsigned", "attr": null}),
        "int_I32" => json!({"tag": "Tint", "size": "I32", "sign": "Signed", "attr": null}),
        "int_I32_unsigned" => json!({"tag": "Tint", "size": "I32", "sign": "Unsigned", "attr": null}),
        "int_I64" => json!({"tag": "Tlong", "sign": "Signed", "attr": null}),
        "int_I64_unsigned" => json!({"tag": "Tlong", "sign": "Unsigned", "attr": null}),
        "float_F64" => json!({"tag": "Tfloat", "size": "F64", "attr": null}),
        "float_F32" => json!({"tag": "Tfloat", "size": "F32", "attr": null}),
        "ptr_I64" | "ptr_char" | "ptr_int" | "ptr_double" | "ptr_float" => {
            json!({"tag": "Tpointer", "inner": {"tag": "Tvoid"}, "attr": null})
        }
        "void" => json!({"tag": "Tvoid"}),
        s if s.starts_with("ptr_struct_") => {
            let id_str = s.trim_start_matches("ptr_struct_");
            let id = usize::from_str_radix(id_str, 16).unwrap_or(0);
            json!({
                "tag": "Tpointer",
                "inner": {"tag": "Tstruct", "id": id, "attr": null},
                "attr": null,
            })
        }
        _ => json!({"tag": "Tlong", "sign": "Unsigned", "attr": null}),
    }
}

fn serialize_external_function(ef: &ExternalFunction) -> Value {
    match ef {
        ExternalFunction::EFExternal(name, sig) => json!({
            "tag": "EF_external",
            "name": name.as_ref(),
            "sig": serialize_signature(sig),
        }),
        ExternalFunction::EFBuiltin(name, sig) => json!({
            "tag": "EF_builtin",
            "name": name.as_ref(),
            "sig": serialize_signature(sig),
        }),
        ExternalFunction::EFRuntime(name, sig) => json!({
            "tag": "EF_runtime",
            "name": name.as_ref(),
            "sig": serialize_signature(sig),
        }),
        ExternalFunction::EFVLoad(chunk) => json!({
            "tag": "EF_vload",
            "chunk": serialize_chunk(chunk),
        }),
        ExternalFunction::EFVStore(chunk) => json!({
            "tag": "EF_vstore",
            "chunk": serialize_chunk(chunk),
        }),
        ExternalFunction::EFMalloc => json!({"tag": "EF_malloc"}),
        ExternalFunction::EFFree => json!({"tag": "EF_free"}),
        ExternalFunction::EFMemcpy(sz, al) => json!({
            "tag": "EF_memcpy",
            "size": *sz,
            "align": *al,
        }),
        _ => json!({"tag": "EF_unknown"}),
    }
}

fn serialize_signature(sig: &Signature) -> Value {
    json!({
        "args": sig.sig_args.iter().map(serialize_xtype).collect::<Vec<_>>(),
        "res": serialize_xtype(&sig.sig_res),
        "cc": serialize_callconv(&sig.sig_cc),
    })
}

fn serialize_chunk(chunk: &MemoryChunk) -> &'static str {
    match chunk {
        MemoryChunk::MBool => "Mbool",
        MemoryChunk::MInt8Signed => "Mint8signed",
        MemoryChunk::MInt8Unsigned => "Mint8unsigned",
        MemoryChunk::MInt16Signed => "Mint16signed",
        MemoryChunk::MInt16Unsigned => "Mint16unsigned",
        MemoryChunk::MInt32 => "Mint32",
        MemoryChunk::MInt64 => "Mint64",
        MemoryChunk::MFloat32 => "Mfloat32",
        MemoryChunk::MFloat64 => "Mfloat64",
        MemoryChunk::MAny32 => "Many32",
        MemoryChunk::MAny64 => "Many64",
        MemoryChunk::Unknown => "Many64",
    }
}

/// Convert a FieldType (from struct recovery) to a Clight JSON type.
fn serialize_ctype_from_field(ty: &crate::decompile::passes::c_pass::types::CType) -> Value {
    use crate::decompile::passes::c_pass::types::{CType, FloatSize, IntSize, Signedness};
    match ty {
        CType::Void => json!({"tag": "Tvoid"}),
        CType::Bool => json!({"tag": "Tint", "size": "IBool", "sign": "Unsigned", "attr": null}),
        CType::Int(size, sign) => {
            let s = match size {
                IntSize::Char => "I8",
                IntSize::Short => "I16",
                IntSize::Int => "I32",
                IntSize::Long | IntSize::LongLong => return json!({
                    "tag": "Tlong",
                    "sign": match sign { Signedness::Signed => "Signed", Signedness::Unsigned => "Unsigned" },
                    "attr": null,
                }),
            };
            json!({
                "tag": "Tint",
                "size": s,
                "sign": match sign { Signedness::Signed => "Signed", Signedness::Unsigned => "Unsigned" },
                "attr": null,
            })
        }
        CType::Float(size) => json!({
            "tag": "Tfloat",
            "size": match size { FloatSize::Float => "F32", FloatSize::Double | FloatSize::LongDouble => "F64" },
            "attr": null,
        }),
        CType::Pointer(inner, _) => json!({
            "tag": "Tpointer",
            "inner": serialize_ctype_from_field(inner),
            "attr": null,
        }),
        CType::Array(elem, size) => json!({
            "tag": "Tarray",
            "elem": serialize_ctype_from_field(elem),
            "size": size.unwrap_or(0),
            "attr": null,
        }),
        CType::Struct(name) => json!({
            "tag": "Tstruct",
            "name": name,
            "attr": null,
        }),
        CType::Union(name) => json!({
            "tag": "Tunion",
            "name": name,
            "attr": null,
        }),
        CType::Function(ret, params, variadic) => json!({
            "tag": "Tfunction",
            "return": serialize_ctype_from_field(ret),
            "params": params.iter().map(serialize_ctype_from_field).collect::<Vec<_>>(),
            "cc": if *variadic { json!({"varargs": 0}) } else { json!("cc_default") },
        }),
        CType::Enum(name) => json!({"tag": "Tint", "size": "I32", "sign": "Signed", "attr": null, "enum": name}),
        CType::TypedefName(name) => json!({"tag": "Tint", "size": "I32", "sign": "Signed", "attr": null, "typedef": name}),
        CType::Qualified(inner, _) => serialize_ctype_from_field(inner),
    }
}

/// Collect names of functions called via Scall/EvarSymbol in a statement tree.
fn collect_called_functions(stmt: &ClightStmt, names: &mut std::collections::HashSet<String>) {
    match stmt {
        ClightStmt::Scall(_, func_expr, _) => {
            collect_called_expr(func_expr, names);
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts { collect_called_functions(s, names); }
        }
        ClightStmt::Sifthenelse(_, s1, s2) => {
            collect_called_functions(s1, names);
            collect_called_functions(s2, names);
        }
        ClightStmt::Sloop(s1, s2) => {
            collect_called_functions(s1, names);
            collect_called_functions(s2, names);
        }
        ClightStmt::Slabel(_, s) => collect_called_functions(s, names),
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases { collect_called_functions(s, names); }
        }
        _ => {}
    }
}

fn collect_called_expr(expr: &ClightExpr, names: &mut std::collections::HashSet<String>) {
    match expr {
        ClightExpr::EvarSymbol(name, _) => { names.insert(name.clone()); }
        ClightExpr::Evar(id, _) => { names.insert(format!("{}", id)); }
        _ => {}
    }
}

fn resolve_name(id: usize, id_to_name: &HashMap<usize, String>) -> String {
    id_to_name
        .get(&id)
        .cloned()
        .unwrap_or_else(|| format!("_{}", id))
}
