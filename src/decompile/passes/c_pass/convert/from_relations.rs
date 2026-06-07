

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::{
    AssignOp, BinaryOp, CBlockItem, CExpr, CStmt, CType, ExprTransform, FloatLiteral,
    FloatLiteralSuffix, FuncDef, FuncParam, IntLiteral, IntLiteralBase,
    IntLiteralSuffix, Label, SourceLoc, StorageClass, StmtTransform, StringLiteral,
    TypeQualifiers, UnaryOp, VarDecl,
};
use crate::decompile::passes::c_pass::TranslationUnit;
use crate::decompile::passes::clight_select::query::GlobalData;
use crate::decompile::passes::clight_select::select::SelectedFunction;
use crate::x86::types as clight;
use crate::x86::types::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use log::debug;
use std::sync::Arc;

// GCC hot/cold splitting emits `<base>_cold` companions with trivial abort/unreachable bodies; drop only when name ends in `_cold` AND body matches that trivial pattern (empty body is kept, not silently deleted).
fn has_cold_suffix(name: &str) -> bool {
    name.len() > 5 && name.ends_with("_cold")
}

fn is_trivial_cold_body(body: &CStmt) -> bool {
    // Unwrap a single-statement Block/Sequence wrapper, then require exactly one trivial call.
    match body {
        CStmt::Block(items) => {
            let stmts: Vec<&CStmt> = items.iter().filter_map(|item| match item {
                CBlockItem::Stmt(s) => Some(s),
                CBlockItem::Decl(_) => None,
            }).collect();
            stmts.len() == 1 && is_trivial_cold_call(stmts[0])
        }
        CStmt::Sequence(stmts) => {
            stmts.len() == 1 && is_trivial_cold_call(&stmts[0])
        }
        other => is_trivial_cold_call(other),
    }
}

fn is_trivial_cold_call(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Expr(CExpr::Call(func, args)) => {
            if !args.is_empty() {
                return false;
            }
            if let CExpr::Var(name) = func.as_ref() {
                name == "abort" || name == "__builtin_unreachable"
            } else {
                false
            }
        }
        _ => false,
    }
}

fn convert_clight_type(ty: &crate::x86::types::ClightType) -> CType {
    use crate::x86::types::*;
    match ty {
        crate::x86::types::ClightType::Tvoid => CType::Void,
        crate::x86::types::ClightType::Tint(size, sign, _attr) => {
            let c_size = match size {
                ClightIntSize::I8 => crate::decompile::passes::c_pass::types::IntSize::Char,
                ClightIntSize::I16 => crate::decompile::passes::c_pass::types::IntSize::Short,
                ClightIntSize::I32 | ClightIntSize::IBool => crate::decompile::passes::c_pass::types::IntSize::Int,
            };
            let c_sign = match sign {
                ClightSignedness::Signed => crate::decompile::passes::c_pass::types::Signedness::Signed,
                ClightSignedness::Unsigned => crate::decompile::passes::c_pass::types::Signedness::Unsigned,
            };
            CType::Int(c_size, c_sign)
        }
        crate::x86::types::ClightType::Tlong(sign, _attr) => {
            let c_sign = match sign {
                ClightSignedness::Signed => crate::decompile::passes::c_pass::types::Signedness::Signed,
                ClightSignedness::Unsigned => crate::decompile::passes::c_pass::types::Signedness::Unsigned,
            };
            CType::Int(crate::decompile::passes::c_pass::types::IntSize::Long, c_sign)
        }
        crate::x86::types::ClightType::Tfloat(size, _attr) => {
            let c_size = match size {
                ClightFloatSize::F32 => crate::decompile::passes::c_pass::types::FloatSize::Float,
                ClightFloatSize::F64 => crate::decompile::passes::c_pass::types::FloatSize::Double,
            };
            CType::Float(c_size)
        }
        crate::x86::types::ClightType::Tpointer(inner, attr) => {
            let qualifiers = TypeQualifiers {
                is_volatile: attr.attr_volatile,
                ..TypeQualifiers::none()
            };
            CType::Pointer(Box::new(convert_clight_type(inner)), qualifiers)
        }
        crate::x86::types::ClightType::Tarray(inner, size, _attr) => {
            CType::Array(Box::new(convert_clight_type(inner)), Some(*size as usize))
        }
        crate::x86::types::ClightType::Tfunction(params, ret, _cc) => {
            let c_params: Vec<CType> = params.iter().map(convert_clight_type).collect();
            CType::Function(Box::new(convert_clight_type(ret)), c_params, false)
        }
        crate::x86::types::ClightType::Tstruct(id, _attr) => {
            CType::Struct(format!("struct_{:x}", id))
        }
        crate::x86::types::ClightType::Tunion(id, _attr) => CType::Union(format!("union_{}", id)),
    }
}

fn clight_expr_to_ctype(expr: &clight::ClightExpr) -> CType {
    let clight_ty = match expr {
        clight::ClightExpr::EconstInt(_, ty)
        | clight::ClightExpr::EconstFloat(_, ty)
        | clight::ClightExpr::EconstSingle(_, ty)
        | clight::ClightExpr::EconstLong(_, ty)
        | clight::ClightExpr::Evar(_, ty)
        | clight::ClightExpr::EvarSymbol(_, ty)
        | clight::ClightExpr::Etempvar(_, ty)
        | clight::ClightExpr::Ederef(_, ty)
        | clight::ClightExpr::Eaddrof(_, ty)
        | clight::ClightExpr::Eunop(_, _, ty)
        | clight::ClightExpr::Ebinop(_, _, _, ty)
        | clight::ClightExpr::Ecast(_, ty)
        | clight::ClightExpr::Efield(_, _, ty)
        | clight::ClightExpr::Esizeof(_, ty)
        | clight::ClightExpr::Ealignof(_, ty)
        | clight::ClightExpr::Econdition(_, _, _, ty) => ty,
    };
    convert_clight_type(clight_ty)
}

// Well-known variadic libc/coreutils functions whose recovered prototypes carry only the fixed leading parameters, so calls passing the variadic tail fail to type-check unless the prototype is declared variadic (mirrors the printf/scanf families handled by narrow_varargs_args, plus common variadic libc entry points).
fn is_known_variadic_fn(name: &str) -> bool {
    matches!(
        name,
        "printf" | "fprintf" | "sprintf" | "snprintf" | "dprintf"
            | "scanf" | "fscanf" | "sscanf"
            | "__printf_chk" | "__fprintf_chk" | "__sprintf_chk" | "__snprintf_chk"
            | "__isoc99_scanf" | "__isoc99_fscanf" | "__isoc99_sscanf"
            | "error" | "error_at_line"
            | "open" | "openat" | "fcntl" | "ioctl"
            | "syslog" | "asprintf" | "execl" | "execlp" | "execle"
    )
}

fn convert_xtype(xt: &XType) -> CType {
    match xt {
        XType::Xvoid => CType::Void,
        XType::Xint8signed => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Char,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xint8unsigned => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Char,
            crate::decompile::passes::c_pass::types::Signedness::Unsigned,
        ),
        XType::Xint16signed => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Short,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xint16unsigned => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Short,
            crate::decompile::passes::c_pass::types::Signedness::Unsigned,
        ),
        XType::Xint => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Int,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xintunsigned => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Int,
            crate::decompile::passes::c_pass::types::Signedness::Unsigned,
        ),
        XType::Xlong => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Long,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xlongunsigned => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Long,
            crate::decompile::passes::c_pass::types::Signedness::Unsigned,
        ),
        XType::Xptr => CType::Pointer(Box::new(CType::Void), TypeQualifiers::none()),
        XType::Xcharptr => CType::Pointer(
            Box::new(CType::Int(
                crate::decompile::passes::c_pass::types::IntSize::Char,
                crate::decompile::passes::c_pass::types::Signedness::Signed,
            )),
            TypeQualifiers::none(),
        ),
        XType::Xcharptrptr => CType::Pointer(
            Box::new(CType::Pointer(
                Box::new(CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Char,
                    crate::decompile::passes::c_pass::types::Signedness::Signed,
                )),
                TypeQualifiers::none(),
            )),
            TypeQualifiers::none(),
        ),
        XType::Xintptr => CType::Pointer(
            Box::new(CType::Int(
                crate::decompile::passes::c_pass::types::IntSize::Int,
                crate::decompile::passes::c_pass::types::Signedness::Signed,
            )),
            TypeQualifiers::none(),
        ),
        XType::Xfloatptr => CType::Pointer(
            Box::new(CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Double)),
            TypeQualifiers::none(),
        ),
        XType::Xsingleptr => CType::Pointer(
            Box::new(CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Float)),
            TypeQualifiers::none(),
        ),
        XType::Xfuncptr => CType::Pointer(
            Box::new(CType::Function(
                Box::new(CType::Void),
                Vec::new(),
                false,
            )),
            TypeQualifiers::none(),
        ),
        XType::Xfloat => CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Double),
        XType::Xsingle => CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Float),
        XType::Xany32 => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Int,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xany64 => CType::Int(
            crate::decompile::passes::c_pass::types::IntSize::Long,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xbool => CType::Bool,
        XType::XstructPtr(id) => CType::Pointer(
            Box::new(CType::Struct(format!("struct_{:x}", id))),
            TypeQualifiers::none(),
        ),
    }
}

pub fn build_cast_from_relations(
    db: &DecompileDB,
    selected_functions: &[SelectedFunction],
    globals: &[GlobalData],
    id_to_name: &HashMap<usize, String>,
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
) -> TranslationUnit {
    let mut ctx = ConversionContext::new(id_to_name.clone());
    for global in globals {
        if global.is_string {
            ctx.string_globals.insert(global.id);
        }
    }
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        ctx.string_label_to_content.insert(label.clone(), content.clone());
    }
    
    {
        let mut addr_name_map: HashMap<u64, String> = HashMap::new();
        for (addr, name, _entry_node) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            addr_name_map.insert(*addr as u64, sanitize_c_symbol_name(name));
        }
        for func in selected_functions {
            addr_name_map.insert(func.address as u64, sanitize_c_symbol_name(&func.name));
        }
        let mut sorted: Vec<(u64, String)> = addr_name_map.into_iter().collect();
        sorted.sort_by_key(|(addr, _)| *addr);
        ctx.func_addrs_sorted = sorted;
    }

    let mut stmt_map: HashMap<crate::x86::types::Node, CStmt> = HashMap::new();
    for func in selected_functions {
        // func.statements is a HashMap; iterating it directly leaks non-deterministic order into convert_stmt -> record_var_type (which is first-wins), so a variable's recorded C type flips between runs. Walk nodes in sorted order.
        let mut nodes: Vec<crate::x86::types::Node> = func.statements.keys().copied().collect();
        nodes.sort();
        for node in nodes {
            let clight_stmt = &func.statements[&node];
            let converted = convert_stmt(clight_stmt, &mut ctx);
            stmt_map.insert(node, converted);
        }
    }

    build_translation_unit_from_stmt_map_with_types(
        db,
        selected_functions,
        globals,
        id_to_name,
        &stmt_map,
        edges,
        &ctx.var_types,
        &HashMap::new(),
    )
}


pub fn build_translation_unit_from_stmt_map_with_types(
    db: &DecompileDB,
    selected_functions: &[SelectedFunction],
    globals: &[GlobalData],
    id_to_name: &HashMap<usize, String>,
    stmt_map: &HashMap<crate::x86::types::Node, CStmt>,
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
    var_types: &HashMap<String, CType>,
    optimized_node_to_func: &HashMap<crate::x86::types::Node, crate::x86::types::Address>,
) -> TranslationUnit {
    let mut tu = TranslationUnit::new();
    let mut func_var_types = var_types.clone();

    let dwarf_param_names: HashMap<(Address, usize), String> = db
        .rel_iter::<(Address, usize, Symbol)>("dwarf_func_param_name")
        .map(|&(addr, idx, name)| ((addr, idx), name.to_string()))
        .collect();

    let mut global_names: HashSet<String> = globals
        .iter()
        .map(|g| sanitize_c_symbol_name(&g.name))
        .collect();
    for func in selected_functions {
        global_names.insert(sanitize_c_symbol_name(&func.name));
    }
    for name in id_to_name.values() {
        global_names.insert(sanitize_c_symbol_name(name));
    }

    let known_global_types: HashMap<String, CType> = db.rel_iter::<(Symbol, XType)>("known_global_type")
        .map(|(name, xtype)| (sanitize_c_symbol_name(name), convert_xtype(xtype)))
        .collect();

    // Extern return types from abi_pass for variable type inference at call sites
    let extern_return_types: HashMap<String, CType> = db
        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        .map(|(name, _, ret_type, _)| (sanitize_c_symbol_name(name), convert_xtype(ret_type)))
        .filter(|(_, ty)| !matches!(ty, CType::Void))
        .collect();

    // Build global load chunk map: prefer integer over float (SSE bulk copies produce spurious floats).
    let global_chunks: HashMap<usize, MemoryChunk> = {
        let mut chunks: HashMap<usize, Vec<MemoryChunk>> = HashMap::new();
        for (id, chunk) in db.rel_iter::<(Ident, MemoryChunk)>("global_load_chunk") {
            chunks.entry(*id).or_default().push(*chunk);
        }
        chunks.into_iter().map(|(id, mut chunk_list)| {
            // Filter out generic MAny/Unknown when specific chunks exist
            let has_specific = chunk_list.iter().any(|c|
                !matches!(c, MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown));
            if has_specific {
                chunk_list.retain(|c|
                    !matches!(c, MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown));
            }
            // Filter out float chunks when integer chunks exist (SSE bulk copies produce MFloat64)
            let has_int = chunk_list.iter().any(|c|
                matches!(c, MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned
                    | MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned
                    | MemoryChunk::MInt32 | MemoryChunk::MInt64));
            if has_int {
                chunk_list.retain(|c|
                    !matches!(c, MemoryChunk::MFloat32 | MemoryChunk::MFloat64));
            }
            // Among remaining, prefer the largest integer type
            let best = chunk_list.iter().max_by_key(|c| match c {
                MemoryChunk::MBool => 0,
                MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
                MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
                MemoryChunk::MInt32 => 3,
                MemoryChunk::MFloat32 => 4,
                MemoryChunk::MFloat64 => 5,
                MemoryChunk::MInt64 => 6,
                MemoryChunk::MAny32 => 7,
                MemoryChunk::MAny64 => 8,
                MemoryChunk::Unknown => 9,
            }).copied().unwrap_or(MemoryChunk::Unknown);
            (id, best)
        }).collect()
    };

    // Build global pointer sets from rtl_pass analysis
    let global_ptr_ids: HashSet<usize> = db.rel_iter::<(Ident,)>("emit_global_is_ptr")
        .map(|(id,)| *id)
        .collect();
    let global_char_ptr_ids: HashSet<usize> = db.rel_iter::<(Ident,)>("emit_global_is_char_ptr")
        .map(|(id,)| *id)
        .collect();

    for global in globals {
        if global.is_string || global.scalar_value.is_some() {
            continue;
        }
        let sanitized_name = sanitize_c_symbol_name(&global.name);
        let (ty, init) = if let Some(known_ty) = known_global_types.get(&sanitized_name) {
            (known_ty.clone(), None)
        } else if global_char_ptr_ids.contains(&global.id) {
            (CType::Pointer(
                Box::new(CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Char,
                    crate::decompile::passes::c_pass::types::Signedness::Signed,
                )),
                TypeQualifiers::none(),
            ), None)
        } else if global.is_pointer || global_ptr_ids.contains(&global.id) {
            (CType::ptr(CType::Void), None)
        } else if let Some(chunk) = global_chunks.get(&global.id) {
            let chunk_ty = match chunk {
                MemoryChunk::MBool | MemoryChunk::MInt32 | MemoryChunk::MAny32 => CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Int,
                    crate::decompile::passes::c_pass::types::Signedness::Signed,
                ),
                MemoryChunk::MInt8Signed => CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Char,
                    crate::decompile::passes::c_pass::types::Signedness::Signed,
                ),
                MemoryChunk::MInt8Unsigned => CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Char,
                    crate::decompile::passes::c_pass::types::Signedness::Unsigned,
                ),
                MemoryChunk::MInt16Signed => CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Short,
                    crate::decompile::passes::c_pass::types::Signedness::Signed,
                ),
                MemoryChunk::MInt16Unsigned => CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Short,
                    crate::decompile::passes::c_pass::types::Signedness::Unsigned,
                ),
                MemoryChunk::MFloat32 => CType::Float(
                    crate::decompile::passes::c_pass::types::FloatSize::Float,
                ),
                MemoryChunk::MFloat64 => CType::Float(
                    crate::decompile::passes::c_pass::types::FloatSize::Double,
                ),
                _ => CType::long(),
            };
            (chunk_ty, None)
        } else {
            (CType::long(), None)
        };

        tu.add_global_var(VarDecl {
            name: sanitized_name,
            ty,
            storage_class: StorageClass::default(),
            qualifiers: TypeQualifiers::none(),
            init,
            loc: SourceLoc::unknown(),
        });
    }

    // instr_in_function is multi-valued (shared PLT/thunk nodes); keep the smallest owning address so the node->function mapping is identical across runs.
    let mut node_to_func: HashMap<crate::x86::types::Node, crate::x86::types::Address> =
        HashMap::new();
    for (node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        node_to_func
            .entry(*node)
            .and_modify(|e| {
                if *func < *e {
                    *e = *func;
                }
            })
            .or_insert(*func);
    }

    let recovered_func_names = recover_func_names_from_assert(db);

    let string_map = crate::decompile::passes::c_pass::helpers::build_string_literal_map(db);

    let known_func_names: HashMap<String, usize> = selected_functions
        .iter()
        .map(|f| (sanitize_c_symbol_name(&f.name), f.param_regs.len()))
        .chain(
            id_to_name
                .values()
                .filter(|name| !is_generated_label(name))
                .map(|name| (sanitize_c_symbol_name(name), usize::MAX)),
        )
        .collect();

    let mut emitted_func_names: HashSet<String> = HashSet::new();
    for func in selected_functions {
        let params: Vec<FuncParam> = func
            .param_regs
            .iter()
            .zip(func.param_types.iter())
            .map(|(reg, pty)| {
                let name = param_name_for_reg(*reg);
                FuncParam::named(name, convert_param_type_from_param(pty))
            })
            .collect();

        let param_name_set: HashSet<String> =
            params.iter().filter_map(|p| p.name.clone()).collect();

        let func_addr = func.address;
        
        let nodes_set: HashSet<_> = stmt_map
            .keys()
            .copied()
            .filter(|n| {
                func.statements.contains_key(n)
                    || node_to_func.get(n) == Some(&func_addr)
                    || optimized_node_to_func.get(n) == Some(&func_addr)
            })
            .collect();

        // sseq bundling drops bundle members but their clight_succ edges still point at them; narrowly remap member->synth edges to the head so synth nodes (e.g. SP-indexed-load assignments) stay reachable via DFS. Restricted to synth targets only: broader remap breaks loop structuring (smoke::for_loop).
        let mut sseq_member_to_head: HashMap<crate::x86::types::Node, crate::x86::types::Node> = HashMap::new();
        for (&head, members) in &func.sseq_groups {
            for &m in members {
                if m != head {
                    sseq_member_to_head.insert(m, head);
                }
            }
        }
        const SYNTH_BIT: u64 = 1u64 << 62;
        let remapped_edges: Vec<(crate::x86::types::Node, crate::x86::types::Node)> = edges.iter()
            .flat_map(|&(s, d)| {
                let mut out: Vec<(crate::x86::types::Node, crate::x86::types::Node)> = vec![(s, d)];
                let dst_is_synth = (d & SYNTH_BIT) != 0;
                let src_is_synth = (s & SYNTH_BIT) != 0;
                // synth-targeted edge from a bundle member: also publish from the head
                if dst_is_synth {
                    if let Some(&head) = sseq_member_to_head.get(&s) {
                        if head != s {
                            out.push((head, d));
                        }
                    }
                }
                // synth-source edge to an external (non-bundle) consumer: keep as-is (synth nodes aren't bundle members, so no remap needed for src).
                let _ = src_is_synth;
                out
            })
            .filter(|(s, d)| s != d)
            .collect();

        let entry_node = func.address as crate::x86::types::Node;
        let nodes = order_nodes_dfs(entry_node, &nodes_set, &remapped_edges);

        let mut body_items = Vec::new();
        let mut body_terminated = false;
        for &node in &nodes {
            if let Some(stmt) = stmt_map.get(&node) {
                if matches!(stmt, CStmt::Empty) {
                    continue;
                }
                if body_terminated {
                    // After unconditional exit, only keep statements with named labels (goto targets).
                    if contains_named_label(stmt) {
                        body_items.push(CBlockItem::Stmt(stmt.clone()));
                        // The labeled section might end with a terminator, so re-check.
                        body_terminated = is_unconditional_exit(stmt);
                    }
                } else {
                    body_items.push(CBlockItem::Stmt(stmt.clone()));
                    if is_unconditional_exit(stmt) {
                        body_terminated = true;
                    }
                }
            }
        }

        let _before_count = body_items.len();
        body_items = simplify_fallthrough_gotos_in_block(body_items);

        for (i, item) in body_items.iter().enumerate() {
            if i + 1 < body_items.len() {
                if let CBlockItem::Stmt(CStmt::If(_, then_s, Some(else_s))) = item {
                    if let CBlockItem::Stmt(next_stmt) = &body_items[i + 1] {
                        if let Some(next_label) = get_first_label_from_stmt(next_stmt) {
                            if let CStmt::Goto(else_target) = &**else_s {
                                if normalize_label(else_target) == normalize_label(&next_label) {
                                    debug!("[EMIT-UNSIMPLIFIED] else goto {} should have been simplified to next label {}",
                                        else_target, next_label);
                                }
                            }
                            if let CStmt::Goto(then_target) = &**then_s {
                                if normalize_label(then_target) == normalize_label(&next_label) {
                                    debug!("[EMIT-UNSIMPLIFIED] then goto {} should have been simplified to next label {}",
                                        then_target, next_label);
                                }
                            }
                        }
                    }
                }
            }
        }

        let expected_stmts = func.statements.len();
        let actual_leaf_count = count_leaf_stmts_in_block(&body_items);
        let is_incomplete = body_items.is_empty()
            || (expected_stmts > 4 && actual_leaf_count * 2 < expected_stmts);
        if is_incomplete {
            let covered_nodes: HashSet<crate::x86::types::Node> = nodes.iter().copied().collect();

            let mut fb_ctx = ConversionContext::new(id_to_name.clone());
            {
                let mut addr_name_map: HashMap<u64, String> = HashMap::new();
                for (addr, name, _entry_node) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
                    addr_name_map.insert(*addr as u64, sanitize_c_symbol_name(name));
                }
                for f in selected_functions {
                    addr_name_map.insert(f.address as u64, sanitize_c_symbol_name(&f.name));
                }
                let mut sorted: Vec<(u64, String)> = addr_name_map.into_iter().collect();
                sorted.sort_by_key(|(addr, _)| *addr);
                fb_ctx.func_addrs_sorted = sorted;
            }
            let mut fb_nodes: Vec<_> = func.statements.keys().copied()
                .filter(|n| !covered_nodes.contains(n))
                .collect();
            fb_nodes.sort();
            for node in fb_nodes {
                if let Some(cl_stmt) = func.statements.get(&node) {
                    let cstmt = convert_stmt(cl_stmt, &mut fb_ctx);
                    let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                        crate::decompile::passes::c_pass::helpers::inline_string_literals(e, &string_map)
                    });
                    let cstmt = strip_trivial_casts(&cstmt);
                    if !matches!(cstmt, CStmt::Empty) {
                        body_items.push(CBlockItem::Stmt(cstmt));
                    }
                }
            }
            for (name, ty) in fb_ctx.var_types {
                func_var_types.entry(name).or_insert(ty);
            }
        }

        rewrite_tailcall_gotos(&mut body_items, &known_func_names, &func.name);

        ensure_goto_label_consistency(&mut body_items);

        deduplicate_labels(&mut body_items);

        strip_dead_labels_in_block(&mut body_items);

        let body = if body_items.is_empty() {
            continue;
        } else if body_items.len() == 1 {
            match body_items.remove(0) {
                CBlockItem::Stmt(s) => s,
                other => CStmt::Block(vec![other]),
            }
        } else {
            CStmt::Block(body_items)
        };

        let mut body = crate::decompile::passes::c_pass::helpers::flatten_blocks_and_cleanup(&body);
        body = eliminate_dead_code(&body);

        simplify_xor_self_in_stmt(&mut body);
        strip_dead_expr_stmts(&mut body);
        body = strip_trivial_casts(&body);
        body = forward_return_value(&body);

        let is_reconciled_void = db.rel_iter::<(Address,)>("emit_function_void").any(|&(addr,)| addr == func.address);

        // Return type from signature_pass via emit_function_return_type_xtype
        let return_type = if is_reconciled_void {
            CType::Void
        } else if let Some((_, xtype)) = db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype").find(|(a, _)| *a == func.address) {
            convert_xtype(xtype)
        } else {
            convert_clight_type(&func.return_type)
        };

        if is_reconciled_void {
            strip_return_values_in_stmt(&mut body);
        }
        if !matches!(return_type, CType::Void) {
            fix_bare_returns_in_stmt(&mut body);
        }

        if is_dead_expr_stmt(&body) {
            continue;
        }

        let mut local_var_types = func_var_types.clone();

        // Seed with clang-refined types from clight_select (validated by clang compilation, takes precedence over re-inference).
        for (reg, candidates) in &func.var_type_candidates {
            let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
            if let Some(type_str) = candidates.get(idx).or_else(|| func.var_types.get(reg)) {
                let var_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
                let ctype = crate::decompile::passes::c_pass::helpers::xtype_string_to_ctype(type_str);
                local_var_types.insert(var_name, ctype);
            }
        }

        infer_var_types_from_usage(&body, &mut local_var_types, &extern_return_types);

        let bool_vars = detect_bool_variables(&body);

        let params: Vec<FuncParam> = params.into_iter().map(|mut p| {
            if let Some(name) = &p.name {
                if p.ty == CType::long() {
                    if let Some(inferred_ty) = local_var_types.get(name) {
                        p.ty = inferred_ty.clone();
                    } else if bool_vars.contains(name.as_str()) {
                        p.ty = CType::int();
                    }
                }
            }
            p
        }).collect();

        // Compilability: now that var/param C types are final, cast to long the pointer operands of any arithmetic C forbids (ptr*int, ptr+ptr, ...); runs before VarRenamer so type map keys still match the variable names used in `body`.
        let body = {
            let mut arith_types = local_var_types.clone();
            for p in &params {
                if let Some(name) = &p.name {
                    arith_types.insert(name.clone(), p.ty.clone());
                }
            }
            repair_arith_stmt(&body, &arith_types)
        };

        let mut local_names = HashSet::new();
        collect_var_names_from_stmt(&body, &mut local_names);
        local_names.retain(|n| !param_name_set.contains(n) && !global_names.contains(n));

        let mut local_vars: Vec<VarDecl> = local_names
            .into_iter()
            .map(|name| {
                let ty = local_var_types.get(&name).cloned().unwrap_or_else(CType::int);
                VarDecl {
                    name,
                    ty,
                    storage_class: StorageClass::default(),
                    qualifiers: TypeQualifiers::none(),
                    init: None,
                    loc: SourceLoc::unknown(),
                }
            })
            .collect();
        local_vars.sort_by(|a, b| a.name.cmp(&b.name));

        let mut renamer = VarRenamer::new();
        for (i, p) in params.iter().enumerate() {
            if let Some(name) = &p.name {
                let dwarf_name = dwarf_param_names.get(&(func_addr, i)).map(|s| s.as_str());
                renamer.seed_param(name, i, dwarf_name);
            }
        }
        // Reserve every pass-through (non-compacted) name first so counter-based compaction of synthetic regs cannot collide with a literal short var_N.
        for v in &local_vars {
            renamer.reserve(&v.name);
        }
        for v in &local_vars {
            renamer.ensure_mapping(&v.name);
        }
        let body = StmtTransform::transform_stmt(&mut renamer, body);
        let params: Vec<FuncParam> = params.iter().map(|p| {
            let new_name = p.name.as_ref().map(|n| renamer.rename(n));
            FuncParam::new(new_name, p.ty.clone())
        }).collect();
        let local_vars: Vec<VarDecl> = local_vars.into_iter().map(|mut v| {
            v.name = renamer.rename(&v.name);
            v
        }).collect();

        // Use-before-def guard: a local read but never the plain-variable assignment target, address-taken, or inc/dec'd in the final body has no producer and "comes from nowhere" (a residual use-before-def upstream recovery could not resolve), so zero-initialize its declaration to avoid reading an undefined value. Defensive last resort; the real fixes are upstream (reaching-def / return-value recovery).
        let mut local_origin_names: HashSet<String> = HashSet::new();
        for p in &params {
            if let Some(n) = &p.name { local_origin_names.insert(n.clone()); }
        }
        collect_var_origins_stmt(&body, &mut local_origin_names);
        let local_vars: Vec<VarDecl> = local_vars
            .into_iter()
            .map(|mut v| {
                if v.init.is_none() && !local_origin_names.contains(&v.name) {
                    v.init = zero_initializer_for_var(&v.ty);
                }
                v
            })
            .collect();

        let func_name = if func.name.starts_with("FUN_") {
            recovered_func_names.get(&func.address).cloned().unwrap_or_else(|| func.name.clone())
        } else {
            func.name.clone()
        };
        let func_name = sanitize_c_symbol_name(&func_name);

        if !emitted_func_names.insert(func_name.clone()) {
            continue;
        }

        if has_cold_suffix(&func_name) && is_trivial_cold_body(&body) {
            continue;
        }

        let func_def = FuncDef {
            name: func_name,
            return_type,
            params,
            is_variadic: false,
            storage_class: StorageClass::default(),
            body,
            local_vars,
            loc: SourceLoc::unknown(),
        };

        if std::env::var("DET_FP").is_ok() {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let body_str = crate::decompile::passes::c_pass::print::print_stmt(&func_def.body);
            let mut lv: Vec<String> = func_def.local_vars.iter().map(|v| format!("{:?}", v)).collect();
            lv.sort();
            let mut h = DefaultHasher::new();
            body_str.hash(&mut h);
            lv.join(",").hash(&mut h);
            eprintln!("[FP-E] {:016x} {} {:016x}", func_addr, func_def.name, h.finish());
        }
        tu.add_function(func_def);
    }

    // A function whose declaration the compiler already provides (header prototype or builtin); our own decl only yields "conflicting types". Name/prefix lists live in header_functions.json (loaded into the DB), so this is data, not hardcoded.
    let is_compiler_provided = |n: &str| {
        db.header_declared_functions.contains(n)
            || db.header_declared_prefixes.iter().any(|p| n.starts_with(p))
    };

    // resolved_extern_signature comes from Ascent (set-semantics, non-deterministic order) and may carry multiple rows for the same function name (one per call-site signature). Group by sanitized name, pick a single signature deterministically, then emit in sorted name order so the C file is byte-stable across runs.
    let mut extern_by_name: BTreeMap<String, Vec<(usize, XType, Arc<Vec<XType>>)>> = BTreeMap::new();
    for (name, param_count, ret_type, param_types) in db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature") {
        let sanitized = sanitize_c_symbol_name(name);
        extern_by_name
            .entry(sanitized)
            .or_default()
            .push((*param_count, *ret_type, param_types.clone()));
    }
    for (sanitized_name, mut sigs) in extern_by_name {
        if emitted_func_names.contains(&sanitized_name) || is_compiler_provided(&sanitized_name) {
            continue;
        }
        // Deterministic pick: prefer the row whose XType vector compares smallest.
        sigs.sort_by(|a, b| a.2.cmp(&b.2).then_with(|| a.1.cmp(&b.1)).then_with(|| a.0.cmp(&b.0)));
        let (_param_count, ret_type, param_types) = sigs.into_iter().next().unwrap();
        let ret_ctype = convert_xtype(&ret_type);
        let params: Vec<FuncParam> = param_types
            .iter()
            .enumerate()
            .map(|(i, t)| FuncParam::named(format!("arg{}", i), convert_xtype(t)))
            .collect();

        let variadic = is_known_variadic_fn(&sanitized_name);
        let mut decl = crate::decompile::passes::c_pass::types::FuncDecl::new(sanitized_name, ret_ctype, params);
        decl.is_variadic = variadic;
        tu.add_func_decl(decl);
    }

    // Per-callee argument types from observed call sites in the emitted bodies, used below to give called-but-not-emitted functions a prototype matching their calls instead of a bare (void).
    let mut call_sigs: HashMap<String, Vec<CType>> = HashMap::new();
    for decl in tu.decls.iter() {
        if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDef(fdef) = decl {
            collect_call_sigs_in_stmt(&fdef.body, &mut call_sigs);
        }
    }

    let resolved_extern_names: HashSet<String> = db
        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
        .map(|(n, _, _, _)| sanitize_c_symbol_name(n))
        .collect();
    let mut unknown_extern_names: Vec<String> = db
        .rel_iter::<(Symbol,)>("unknown_extern")
        .map(|(n,)| sanitize_c_symbol_name(n))
        .collect();
    unknown_extern_names.sort();
    unknown_extern_names.dedup();
    for sanitized_name in unknown_extern_names {
        if emitted_func_names.contains(&sanitized_name) || is_compiler_provided(&sanitized_name) {
            continue;
        }
        if resolved_extern_names.contains(&sanitized_name) {
            continue;
        }

        // Unknown-signature extern: emit a K&R `int name();` (unspecified, unchecked args) so calls with any argument count compile, instead of guessing a fixed arity from one call site that breaks every call that disagrees.
        let decl = crate::decompile::passes::c_pass::types::FuncDecl::new_unspecified(
            sanitized_name,
            CType::Int(crate::decompile::passes::c_pass::types::IntSize::Int, crate::decompile::passes::c_pass::types::Signedness::Signed),
        );
        tu.add_func_decl(decl);
    }

    // Emit forward declarations for all called but undeclared/undefined functions to eliminate "undeclared function" clang errors.
    {
        let mut called_funcs: HashSet<String> = HashSet::new();
        for decl in tu.decls.iter() {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDef(fdef) = decl {
                collect_called_names_in_stmt(&fdef.body, &mut called_funcs);
            }
        }
        let declared: HashSet<String> = tu.symbols.keys().cloned().collect();
        // Collect forward declarations and insert them before function definitions so they're visible at the point of use.
        let mut forward_decls = Vec::new();
        let mut sorted_called_funcs: Vec<&String> = called_funcs.iter().collect();
        sorted_called_funcs.sort();
        for name in sorted_called_funcs {
            let is_label = name.starts_with("L_")
                || (name.starts_with('L') && name.len() > 1 && name[1..].chars().all(|c| c.is_ascii_hexdigit()));
            if !declared.contains(name) && !is_label && !is_compiler_provided(name)
                && !emitted_func_names.contains(name) {
                // Called-but-undeclared external of unknown signature: emit a K&R `int name();` (unspecified, unchecked args). Guarded to externals (not emitted internal funcs) to avoid the documented internal-forward-decl regression.
                let decl = crate::decompile::passes::c_pass::types::FuncDecl::new_unspecified(
                    name.clone(),
                    CType::Int(crate::decompile::passes::c_pass::types::IntSize::Int, crate::decompile::passes::c_pass::types::Signedness::Signed),
                );
                forward_decls.push(crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(decl));
            }
        }
        for decl in forward_decls {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(fd) = decl {
                tu.add_func_decl(fd);
            }
        }
    }

    // Forward declarations for internal (defined) functions, so a call preceding the definition doesn't get an implicit `int name()` that conflicts with it; uses each definition's reconciled signature and is pushed directly (not via add_func_decl) to preserve the symbol->definition mapping (the printer orders FuncDecl before FuncDef).
    {
        let mut internal_decls = Vec::new();
        for decl in tu.decls.iter() {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDef(fdef) = decl {
                if fdef.name == "main" {
                    continue;
                }
                let mut fd = crate::decompile::passes::c_pass::types::FuncDecl::new(
                    fdef.name.clone(),
                    fdef.return_type.clone(),
                    fdef.params.clone(),
                );
                fd.is_variadic = fdef.is_variadic;
                internal_decls.push(fd);
            }
        }
        for fd in internal_decls {
            tu.decls.push(crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(fd));
        }
    }

    // Normalize call-site argument counts to each callee's declared fixed arity so calls agree with their (now forward-declared) prototypes/definitions; only fixed-arity callees are collected, variadic and unspecified-prototype (K&R) callees are left as-is.
    {
        use crate::decompile::passes::c_pass::types::TopLevelDecl;
        let mut arity_counts: HashMap<String, usize> = HashMap::new();
        for decl in tu.decls.iter() {
            match decl {
                TopLevelDecl::FuncDef(f) if !f.is_variadic => {
                    arity_counts.insert(f.name.clone(), f.params.len());
                }
                TopLevelDecl::FuncDecl(d) if !d.is_variadic && !d.unspecified_params => {
                    arity_counts.entry(d.name.clone()).or_insert(d.params.len());
                }
                _ => {}
            }
        }
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                f.body = normalize_call_arity_stmt(&f.body, &arity_counts);
            }
        }
    }

    // Compilability: insert explicit (T) casts at int<->pointer assignment / argument / return mismatches (hard errors on modern clang/gcc even under -w); runs after arity normalization so padded arguments are coerced too, using each function's final params/locals/return type and the program's callee signatures.
    {
        use crate::decompile::passes::c_pass::types::TopLevelDecl;
        let mut callee_params: CalleeParams = HashMap::new();
        let mut callee_ret: HashMap<String, CType> = HashMap::new();
        let mut global_types: HashMap<String, CType> = HashMap::new();
        for decl in tu.decls.iter() {
            match decl {
                TopLevelDecl::FuncDef(f) => {
                    callee_params.insert(
                        f.name.clone(),
                        (f.params.iter().map(|p| p.ty.clone()).collect(), f.is_variadic, false),
                    );
                    callee_ret.insert(f.name.clone(), f.return_type.clone());
                }
                TopLevelDecl::FuncDecl(d) => {
                    callee_params.entry(d.name.clone()).or_insert_with(|| {
                        (d.params.iter().map(|p| p.ty.clone()).collect(), d.is_variadic, d.unspecified_params)
                    });
                    callee_ret.entry(d.name.clone()).or_insert_with(|| d.return_type.clone());
                }
                TopLevelDecl::VarDecl(v) => {
                    global_types.insert(v.name.clone(), v.ty.clone());
                }
                _ => {}
            }
        }
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                let mut types = global_types.clone();
                for p in &f.params {
                    if let Some(n) = &p.name {
                        types.insert(n.clone(), p.ty.clone());
                    }
                }
                for v in &f.local_vars {
                    types.insert(v.name.clone(), v.ty.clone());
                }
                let ret = f.return_type.clone();
                f.body = insert_casts_stmt(&f.body, &types, &callee_params, &callee_ret, &ret);
            }
        }
    }

    // Compilability: declare any referenced-but-undeclared global-scope identifier (rodata data labels like `L_1a2b3` taken by address, named globals like `error_one_per_line`) as a tentative `long` so it stops being an "undeclared identifier"; compiler-synthesized locals (var_*, p<N>, tmp*) are excluded, since an undeclared one of those is a local-scope recovery gap to fix upstream, not a global.
    {
        use crate::decompile::passes::c_pass::types::TopLevelDecl;
        let mut declared: HashSet<String> = HashSet::new();
        let mut locals: HashSet<String> = HashSet::new();
        for decl in tu.decls.iter() {
            match decl {
                TopLevelDecl::FuncDef(f) => {
                    declared.insert(f.name.clone());
                    for p in &f.params {
                        if let Some(n) = &p.name {
                            locals.insert(n.clone());
                        }
                    }
                    for v in &f.local_vars {
                        locals.insert(v.name.clone());
                    }
                }
                TopLevelDecl::FuncDecl(d) => {
                    declared.insert(d.name.clone());
                }
                TopLevelDecl::VarDecl(v) => {
                    declared.insert(v.name.clone());
                }
                _ => {}
            }
        }
        let mut referenced: HashSet<String> = HashSet::new();
        for decl in tu.decls.iter() {
            if let TopLevelDecl::FuncDef(f) = decl {
                collect_var_names_from_stmt(&f.body, &mut referenced);
            }
        }
        let mut undeclared: Vec<String> = referenced
            .into_iter()
            .filter(|n| !declared.contains(n) && !locals.contains(n) && is_global_like_name(n))
            .collect();
        undeclared.sort();
        undeclared.dedup();
        for name in undeclared {
            tu.decls.push(TopLevelDecl::VarDecl(VarDecl {
                name,
                ty: CType::long(),
                storage_class: StorageClass::default(),
                qualifiers: TypeQualifiers::none(),
                init: None,
                loc: SourceLoc::unknown(),
            }));
        }
    }

    tu
}

fn param_name_for_reg(reg: RTLReg) -> String {
    let ident = ident_from_reg(reg);
    format!("var_{}", ident)
}

pub(crate) fn convert_param_type_from_param(param: &ParamType) -> CType {
    match param {
        ParamType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::ptr(CType::Struct(struct_name))
        }
        ParamType::Pointer => CType::ptr(CType::Void),
        ParamType::Typed(xtype) => convert_xtype(xtype),
        ParamType::Integer | ParamType::Unknown => CType::int(),
    }
}

// Collect locals with an origin in the body for the use-before-def guard: the plain-variable LHS of an assignment, an address-taken variable (&v -- a callee may fill it), or an inc/dec target; a referenced local with none of these "comes from nowhere". Mirrors the use-before-def metric's notion of "written" (assign / ++,-- / address-taken).
fn collect_var_origins_expr(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Assign(_, lhs, rhs) => {
            if let CExpr::Var(n) = lhs.as_ref() { out.insert(n.clone()); }
            collect_var_origins_expr(lhs, out);
            collect_var_origins_expr(rhs, out);
        }
        CExpr::Unary(op, inner) => {
            if matches!(op, UnaryOp::AddrOf | UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec) {
                if let CExpr::Var(n) = inner.as_ref() { out.insert(n.clone()); }
            }
            collect_var_origins_expr(inner, out);
        }
        CExpr::Binary(_, l, r) | CExpr::Index(l, r) => {
            collect_var_origins_expr(l, out);
            collect_var_origins_expr(r, out);
        }
        CExpr::Ternary(c, t, e) => {
            collect_var_origins_expr(c, out);
            collect_var_origins_expr(t, out);
            collect_var_origins_expr(e, out);
        }
        CExpr::Call(f, args) => {
            collect_var_origins_expr(f, out);
            for a in args { collect_var_origins_expr(a, out); }
        }
        CExpr::Cast(_, inner) | CExpr::Paren(inner) | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) | CExpr::SizeofExpr(inner) => {
            collect_var_origins_expr(inner, out);
        }
        CExpr::StmtExpr(stmts, fin) => {
            for s in stmts { collect_var_origins_stmt(s, out); }
            collect_var_origins_expr(fin, out);
        }
        _ => {}
    }
}

fn collect_var_origins_stmt(stmt: &CStmt, out: &mut HashSet<String>) {
    use crate::decompile::passes::c_pass::types::ForInit;
    match stmt {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => collect_var_origins_expr(e, out),
        CStmt::If(c, t, e) => {
            collect_var_origins_expr(c, out);
            collect_var_origins_stmt(t, out);
            if let Some(s) = e { collect_var_origins_stmt(s, out); }
        }
        CStmt::Switch(e, body) => {
            collect_var_origins_expr(e, out);
            collect_var_origins_stmt(body, out);
        }
        CStmt::While(c, body) | CStmt::DoWhile(body, c) => {
            collect_var_origins_expr(c, out);
            collect_var_origins_stmt(body, out);
        }
        CStmt::For(init, cond, update, body) => {
            match init {
                Some(ForInit::Expr(e)) => collect_var_origins_expr(e, out),
                Some(ForInit::Decl(decls)) => { for d in decls { out.insert(d.name.clone()); } }
                None => {}
            }
            if let Some(c) = cond { collect_var_origins_expr(c, out); }
            if let Some(u) = update { collect_var_origins_expr(u, out); }
            collect_var_origins_stmt(body, out);
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_var_origins_stmt(s, out),
                    CBlockItem::Decl(decls) => { for d in decls { out.insert(d.name.clone()); } }
                }
            }
        }
        CStmt::Sequence(stmts) => { for s in stmts { collect_var_origins_stmt(s, out); } }
        CStmt::Labeled(_, inner) => collect_var_origins_stmt(inner, out),
        _ => {}
    }
}

// Zero initializer for a "variable from nowhere": scalars/pointers get `= 0`, aggregates get `= {0}` (both valid C); function/void-typed declarations are left untouched.
fn zero_initializer_for_var(ty: &CType) -> Option<crate::decompile::passes::c_pass::types::Initializer> {
    use crate::decompile::passes::c_pass::types::{InitItem, Initializer};
    match ty {
        CType::Void | CType::Function(..) => None,
        CType::Struct(_) | CType::Union(_) | CType::Array(..) => Some(Initializer::List(vec![InitItem {
            designator: None,
            init: Initializer::Expr(CExpr::int(0)),
        }])),
        _ => Some(Initializer::Expr(CExpr::int(0))),
    }
}

fn collect_var_names_from_stmt(stmt: &CStmt, vars: &mut HashSet<String>) {
    match stmt {
        CStmt::Empty | CStmt::Continue | CStmt::Break | CStmt::Goto(_) => {}
        CStmt::Expr(e) | CStmt::Return(Some(e)) => collect_var_names_from_expr(e, vars),
        CStmt::Return(None) => {}
        CStmt::If(cond, then_s, else_s) => {
            collect_var_names_from_expr(cond, vars);
            collect_var_names_from_stmt(then_s, vars);
            if let Some(e) = else_s {
                collect_var_names_from_stmt(e, vars);
            }
        }
        CStmt::Switch(expr, body) => {
            collect_var_names_from_expr(expr, vars);
            collect_var_names_from_stmt(body, vars);
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_var_names_from_stmt(body, vars);
            collect_var_names_from_expr(cond, vars);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    crate::decompile::passes::c_pass::types::ForInit::Expr(e) => {
                        collect_var_names_from_expr(e, vars)
                    }
                    crate::decompile::passes::c_pass::types::ForInit::Decl(decls) => {
                        for d in decls {
                            vars.insert(d.name.clone());
                        }
                    }
                }
            }
            if let Some(cond) = cond {
                collect_var_names_from_expr(cond, vars);
            }
            if let Some(update) = update {
                collect_var_names_from_expr(update, vars);
            }
            collect_var_names_from_stmt(body, vars);
        }
        CStmt::Labeled(_, inner) => collect_var_names_from_stmt(inner, vars),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_var_names_from_stmt(s, vars),
                    CBlockItem::Decl(decls) => {
                        for d in decls {
                            vars.insert(d.name.clone());
                        }
                    }
                }
            }
        }
        CStmt::Decl(decls) => {
            for d in decls {
                vars.insert(d.name.clone());
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_var_names_from_stmt(s, vars);
            }
        }
    }
}

fn infer_var_types_from_usage(
    stmt: &CStmt,
    var_types: &mut HashMap<String, CType>,
    extern_return_types: &HashMap<String, CType>,
) {
    match stmt {
        CStmt::Expr(e) => infer_types_from_expr(e, var_types, extern_return_types),
        CStmt::Return(Some(e)) => infer_types_from_expr(e, var_types, extern_return_types),
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    infer_var_types_from_usage(s, var_types, extern_return_types);
                }
            }
        }
        CStmt::If(cond, then_s, else_s) => {
            infer_types_from_expr(cond, var_types, extern_return_types);
            infer_var_types_from_usage(then_s, var_types, extern_return_types);
            if let Some(e) = else_s {
                infer_var_types_from_usage(e, var_types, extern_return_types);
            }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            infer_types_from_expr(cond, var_types, extern_return_types);
            infer_var_types_from_usage(body, var_types, extern_return_types);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(fi) = init {
                if let crate::decompile::passes::c_pass::types::ForInit::Expr(e) = fi {
                    infer_types_from_expr(e, var_types, extern_return_types);
                }
            }
            if let Some(e) = cond { infer_types_from_expr(e, var_types, extern_return_types); }
            if let Some(e) = update { infer_types_from_expr(e, var_types, extern_return_types); }
            infer_var_types_from_usage(body, var_types, extern_return_types);
        }
        CStmt::Switch(e, body) => {
            infer_types_from_expr(e, var_types, extern_return_types);
            infer_var_types_from_usage(body, var_types, extern_return_types);
        }
        CStmt::Labeled(_, inner) => infer_var_types_from_usage(inner, var_types, extern_return_types),
        CStmt::Sequence(stmts) => {
            for s in stmts { infer_var_types_from_usage(s, var_types, extern_return_types); }
        }
        _ => {}
    }
}

fn insert_or_refine(var_types: &mut HashMap<String, CType>, name: String, new_ty: CType) {
    match var_types.get(&name) {
        None => { var_types.insert(name, new_ty); }
        Some(existing) => {
            if *existing == CType::ptr(CType::Void) && new_ty != CType::ptr(CType::Void) && new_ty.is_pointer() {
                var_types.insert(name, new_ty);
            }
            else if (*existing == CType::int() || *existing == CType::long()) && new_ty.is_pointer() {
                var_types.insert(name, new_ty);
            }
            else if *existing == CType::long() && !new_ty.is_pointer() && new_ty != CType::long() {
                var_types.insert(name, new_ty);
            }
            else if existing.is_generic_long_ptr() && new_ty.is_pointer() && !new_ty.is_generic_long_ptr() {
                var_types.insert(name, new_ty);
            }
        }
    }
}

fn extract_var_name(expr: &CExpr) -> Option<&str> {
    match expr {
        CExpr::Var(name) => Some(name.as_str()),
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => extract_var_name(inner),
        _ => None,
    }
}

fn infer_types_from_expr(
    expr: &CExpr,
    var_types: &mut HashMap<String, CType>,
    extern_return_types: &HashMap<String, CType>,
) {
    match expr {
        CExpr::Unary(UnaryOp::Deref, inner) => {
            if let CExpr::Cast(ty, cast_inner) = inner.as_ref() {
                if let Some(name) = extract_var_name(cast_inner) {
                    if ty.is_pointer() {
                        insert_or_refine(var_types, name.to_string(), ty.clone());
                    }
                }
            }
            else if let CExpr::Paren(paren_inner) = inner.as_ref() {
                if let CExpr::Binary(BinaryOp::Add, lhs, _) | CExpr::Binary(BinaryOp::Sub, lhs, _) = paren_inner.as_ref() {
                    if let CExpr::Cast(ty, cast_inner) = lhs.as_ref() {
                        if let Some(name) = extract_var_name(cast_inner) {
                            if ty.is_pointer() {
                                insert_or_refine(var_types, name.to_string(), ty.clone());
                            }
                        }
                    }
                }
            }
            else if let CExpr::Var(name) = inner.as_ref() {
                var_types.entry(name.clone()).or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(inner, var_types, extern_return_types);
        }
        CExpr::Unary(UnaryOp::Not, inner) => {
            if let Some(name) = extract_var_name(inner) {
                var_types.entry(name.to_string()).or_insert(CType::Bool);
            }
            infer_types_from_expr(inner, var_types, extern_return_types);
        }
        CExpr::Assign(_, lhs, rhs) => {
            if let CExpr::Var(name) = lhs.as_ref() {
                if let CExpr::Cast(ty, _) = rhs.as_ref() {
                    if ty.is_pointer() {
                        insert_or_refine(var_types, name.clone(), ty.clone());
                    }
                }
                if matches!(rhs.as_ref(), CExpr::StringLit(_)) {
                    insert_or_refine(var_types, name.clone(), CType::ptr(CType::char_signed()));
                }
                if let CExpr::Call(callee, _) = rhs.as_ref() {
                    if let CExpr::Var(func_name) = callee.as_ref() {
                        if let Some(ret_ty) = extern_return_types.get(func_name.as_str()) {
                            var_types.entry(name.clone()).or_insert(ret_ty.clone());
                        }
                    }
                }
            }
            infer_types_from_expr(lhs, var_types, extern_return_types);
            infer_types_from_expr(rhs, var_types, extern_return_types);
        }
        CExpr::Call(func, args) => {
            if let CExpr::Var(func_name) = func.as_ref() {
                infer_call_arg_types(func_name, args, var_types);
            }
            infer_types_from_expr(func, var_types, extern_return_types);
            for arg in args { infer_types_from_expr(arg, var_types, extern_return_types); }
        }
        CExpr::MemberPtr(inner, _) => {
            if let CExpr::Var(name) = inner.as_ref() {
                var_types.entry(name.clone()).or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(inner, var_types, extern_return_types);
        }
        CExpr::Index(base, index) => {
            if let CExpr::Var(name) = base.as_ref() {
                var_types.entry(name.clone()).or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(base, var_types, extern_return_types);
            infer_types_from_expr(index, var_types, extern_return_types);
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner) | CExpr::Member(inner, _) => {
            infer_types_from_expr(inner, var_types, extern_return_types);
        }
        CExpr::Binary(_, lhs, rhs) => {
            infer_types_from_expr(lhs, var_types, extern_return_types);
            infer_types_from_expr(rhs, var_types, extern_return_types);
        }
        CExpr::Ternary(c, t, e) => {
            infer_types_from_expr(c, var_types, extern_return_types);
            infer_types_from_expr(t, var_types, extern_return_types);
            infer_types_from_expr(e, var_types, extern_return_types);
        }
        _ => {}
    }
}

fn infer_call_arg_types(func_name: &str, args: &[CExpr], var_types: &mut HashMap<String, CType>) {
    let char_ptr = || CType::ptr(CType::char_signed());
    let void_ptr = || CType::ptr(CType::Void);
    let str_first: &[&str] = &[
        "strlen", "strcmp", "strncmp", "strcpy", "strdup", "strndup",
        "strcat", "strncat", "strchr", "strrchr", "strstr", "strtol", "strtoul",
        "strtoll", "strtoull", "strtod", "atoi", "atol", "atoll",
        "fputs", "puts", "printf", "sprintf", "snprintf",
        "__sprintf_chk", "__snprintf_chk", "__fprintf_chk", "__printf_chk",
        "dcgettext", "gettext", "ngettext", "dgettext",
        "setlocale", "getenv", "putenv",
        "opendir", "stat", "lstat", "access", "unlink", "rmdir", "mkdir",
        "fopen", "freopen", "remove", "rename",
        "error", "error_at_line",
    ];
    if str_first.contains(&func_name) {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
    }
    let str_second: &[&str] = &[
        "strcmp", "strncmp", "strcpy", "strncpy", "strcat", "strncat", "strstr",
        "fprintf", "sprintf", "snprintf",
        "fopen", "freopen", "rename",
        "__sprintf_chk", "__snprintf_chk",
    ];
    if str_second.contains(&func_name) {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
    }
    if func_name == "fprintf" {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
    }
    if func_name == "snprintf" || func_name == "__snprintf_chk" {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
    }
    if matches!(func_name, "memset" | "memcpy" | "memmove" | "memcmp") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), void_ptr());
        }
        if matches!(func_name, "memcpy" | "memmove" | "memcmp") {
            if let Some(name) = args.get(1).and_then(extract_var_name) {
                insert_or_refine(var_types, name.to_string(), void_ptr());
            }
        }
    }
    if matches!(func_name, "memset" | "memcpy" | "memmove" | "memcmp") {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::ulong());
        }
    }
    if func_name == "error" || func_name == "error_at_line" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "getopt_long" || func_name == "getopt" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::ptr(CType::ptr(CType::char_signed())));
        }
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
    }
    if matches!(func_name, "exit" | "_exit" | "_Exit") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if matches!(func_name, "fwrite" | "fread") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), void_ptr());
        }
    }
    if func_name == "fgets" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), char_ptr());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "setlocale" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "open" {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if matches!(func_name, "close" | "read" | "write" | "dup" | "dup2" | "fcntl" | "ioctl" | "isatty") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
    if matches!(func_name, "strtol" | "strtoul" | "strtoll" | "strtoull" | "strtod") {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(var_types, name.to_string(), CType::int());
        }
    }
}

fn detect_bool_variables(stmt: &CStmt) -> HashSet<&str> {
    let mut bool_uses: HashMap<&str, (usize, usize)> = HashMap::new();
    collect_bool_evidence(stmt, &mut bool_uses, false);
    bool_uses.into_iter()
        .filter(|(_, (bool_count, non_bool_count))| *bool_count > 0 && *non_bool_count == 0)
        .map(|(name, _)| name)
        .collect()
}

fn collect_bool_evidence<'a>(stmt: &'a CStmt, evidence: &mut HashMap<&'a str, (usize, usize)>, _in_bool_ctx: bool) {
    match stmt {
        CStmt::If(cond, then_s, else_s) => {
            collect_bool_evidence_expr(cond, evidence, true);
            collect_bool_evidence(then_s, evidence, false);
            if let Some(e) = else_s { collect_bool_evidence(e, evidence, false); }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_bool_evidence_expr(cond, evidence, true);
            collect_bool_evidence(body, evidence, false);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(fi) = init {
                if let crate::decompile::passes::c_pass::types::ForInit::Expr(e) = fi {
                    collect_bool_evidence_expr(e, evidence, false);
                }
            }
            if let Some(e) = cond { collect_bool_evidence_expr(e, evidence, true); }
            if let Some(e) = update { collect_bool_evidence_expr(e, evidence, false); }
            collect_bool_evidence(body, evidence, false);
        }
        CStmt::Expr(e) => collect_bool_evidence_expr(e, evidence, false),
        CStmt::Return(Some(e)) => collect_bool_evidence_expr(e, evidence, false),
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_bool_evidence(s, evidence, false);
                }
            }
        }
        CStmt::Switch(e, body) => {
            collect_bool_evidence_expr(e, evidence, false);
            collect_bool_evidence(body, evidence, false);
        }
        CStmt::Labeled(_, inner) => collect_bool_evidence(inner, evidence, false),
        CStmt::Sequence(stmts) => {
            for s in stmts { collect_bool_evidence(s, evidence, false); }
        }
        _ => {}
    }
}

fn collect_bool_evidence_expr<'a>(expr: &'a CExpr, evidence: &mut HashMap<&'a str, (usize, usize)>, in_bool_ctx: bool) {
    match expr {
        CExpr::Var(name) => {
            let entry = evidence.entry(name.as_str()).or_insert((0, 0));
            if in_bool_ctx {
                entry.0 += 1;
            } else {
                entry.1 += 1;
            }
        }
        CExpr::Unary(UnaryOp::Not, inner) => {
            collect_bool_evidence_expr(inner, evidence, true);
        }
        CExpr::Binary(op, lhs, rhs) if matches!(op, BinaryOp::Eq | BinaryOp::Ne) => {
            let lhs_is_bool_const = matches!(rhs.as_ref(), CExpr::IntLit(lit) if lit.value == 0 || lit.value == 1);
            let rhs_is_bool_const = matches!(lhs.as_ref(), CExpr::IntLit(lit) if lit.value == 0 || lit.value == 1);
            collect_bool_evidence_expr(lhs, evidence, lhs_is_bool_const || in_bool_ctx);
            collect_bool_evidence_expr(rhs, evidence, rhs_is_bool_const || in_bool_ctx);
        }
        CExpr::Binary(BinaryOp::And | BinaryOp::Or, lhs, rhs) => {
            collect_bool_evidence_expr(lhs, evidence, true);
            collect_bool_evidence_expr(rhs, evidence, true);
        }
        CExpr::Assign(_, lhs, rhs) => {
            let rhs_is_bool = matches!(rhs.as_ref(), CExpr::IntLit(lit) if lit.value == 0 || lit.value == 1)
                || matches!(rhs.as_ref(), CExpr::Binary(op, _, _) if matches!(op,
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le |
                    BinaryOp::Gt | BinaryOp::Ge | BinaryOp::And | BinaryOp::Or))
                || matches!(rhs.as_ref(), CExpr::Unary(UnaryOp::Not, _));
            collect_bool_evidence_expr(lhs, evidence, rhs_is_bool);
            collect_bool_evidence_expr(rhs, evidence, false);
        }
        CExpr::Binary(_, lhs, rhs) | CExpr::Index(lhs, rhs) => {
            collect_bool_evidence_expr(lhs, evidence, false);
            collect_bool_evidence_expr(rhs, evidence, false);
        }
        CExpr::Ternary(c, t, e) => {
            collect_bool_evidence_expr(c, evidence, true);
            collect_bool_evidence_expr(t, evidence, in_bool_ctx);
            collect_bool_evidence_expr(e, evidence, in_bool_ctx);
        }
        CExpr::Call(func, args) => {
            collect_bool_evidence_expr(func, evidence, false);
            for arg in args { collect_bool_evidence_expr(arg, evidence, false); }
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner) | CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_bool_evidence_expr(inner, evidence, false);
        }
        _ => {}
    }
}

fn strip_trivial_casts(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(strip_trivial_casts_expr(e)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(strip_trivial_casts(s)),
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            strip_trivial_casts_expr(cond),
            Box::new(strip_trivial_casts(then_s)),
            else_s.as_ref().map(|e| Box::new(strip_trivial_casts(e))),
        ),
        CStmt::While(cond, body) => CStmt::While(
            strip_trivial_casts_expr(cond),
            Box::new(strip_trivial_casts(body)),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(strip_trivial_casts(body)),
            strip_trivial_casts_expr(cond),
        ),
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.as_ref().map(strip_trivial_casts_expr),
            update.as_ref().map(strip_trivial_casts_expr),
            Box::new(strip_trivial_casts(body)),
        ),
        CStmt::Return(Some(e)) => CStmt::Return(Some(strip_trivial_casts_expr(e))),
        CStmt::Switch(e, body) => CStmt::Switch(
            strip_trivial_casts_expr(e),
            Box::new(strip_trivial_casts(body)),
        ),
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(lbl.clone(), Box::new(strip_trivial_casts(inner))),
        CStmt::Sequence(stmts) => CStmt::Sequence(stmts.iter().map(strip_trivial_casts).collect()),
        other => other.clone(),
    }
}

fn strip_trivial_casts_expr(expr: &CExpr) -> CExpr {
    fn unwrap_parens(expr: &CExpr) -> &CExpr {
        match expr {
            CExpr::Paren(inner) => unwrap_parens(inner),
            other => other,
        }
    }

    match expr {
        CExpr::Cast(ty, inner) => {
            let inner_stripped = strip_trivial_casts_expr(inner);

            if is_long_type(ty) {
                let unwrapped_inner = unwrap_parens(&inner_stripped);
                match unwrapped_inner {
                    CExpr::Var(_) => return inner_stripped,
                    CExpr::IntLit(_) => return inner_stripped,
                    CExpr::StringLit(_) => return inner_stripped,
                    CExpr::Cast(inner_ty, _) if is_long_type(inner_ty) => return inner_stripped,
                    // Strip (long) wrapping pointer-typed expressions from coerce_ptr_to_long in clight_pass to avoid int/ptr conversion errors.
                    CExpr::Cast(inner_ty, _) if inner_ty.is_pointer() => return inner_stripped,
                    _ => {}
                }
            }
            if ty.is_pointer() {
                let unwrapped = unwrap_parens(&inner_stripped);
                if let CExpr::IntLit(lit) = unwrapped {
                    if lit.value != 0 {
                        return inner_stripped;
                    }
                    // Keep (void*)0 as null pointer constant
                }
            }
            CExpr::Cast(ty.clone(), Box::new(inner_stripped))
        }
        CExpr::Assign(op, lhs, rhs) => CExpr::Assign(
            *op,
            Box::new(strip_trivial_casts_expr(lhs)),
            Box::new(strip_trivial_casts_expr(rhs)),
        ),
        CExpr::Binary(op, lhs, rhs) => CExpr::Binary(
            *op,
            Box::new(strip_trivial_casts_expr(lhs)),
            Box::new(strip_trivial_casts_expr(rhs)),
        ),
        CExpr::Unary(op, inner) => CExpr::Unary(*op, Box::new(strip_trivial_casts_expr(inner))),
        CExpr::Call(func, args) => CExpr::Call(
            Box::new(strip_trivial_casts_expr(func)),
            args.iter().map(strip_trivial_casts_expr).collect(),
        ),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(strip_trivial_casts_expr(inner))),
        CExpr::Index(arr, idx) => CExpr::Index(
            Box::new(strip_trivial_casts_expr(arr)),
            Box::new(strip_trivial_casts_expr(idx)),
        ),
        CExpr::Member(inner, field) => CExpr::Member(Box::new(strip_trivial_casts_expr(inner)), field.clone()),
        CExpr::MemberPtr(inner, field) => CExpr::MemberPtr(Box::new(strip_trivial_casts_expr(inner)), field.clone()),
        CExpr::Ternary(cond, then_e, else_e) => CExpr::Ternary(
            Box::new(strip_trivial_casts_expr(cond)),
            Box::new(strip_trivial_casts_expr(then_e)),
            Box::new(strip_trivial_casts_expr(else_e)),
        ),
        other => other.clone(),
    }
}

fn fix_bare_returns_in_stmt(stmt: &mut CStmt) {
    match stmt {
        CStmt::Return(None) => {
            *stmt = CStmt::Return(Some(CExpr::int(0)));
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    fix_bare_returns_in_stmt(s);
                }
            }
        }
        CStmt::If(_, then_s, else_s) => {
            fix_bare_returns_in_stmt(then_s);
            if let Some(e) = else_s {
                fix_bare_returns_in_stmt(e);
            }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) => fix_bare_returns_in_stmt(body),
        CStmt::For(_, _, _, body) => fix_bare_returns_in_stmt(body),
        CStmt::Switch(_, body) => fix_bare_returns_in_stmt(body),
        CStmt::Labeled(_, inner) => fix_bare_returns_in_stmt(inner),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                fix_bare_returns_in_stmt(s);
            }
        }
        _ => {}
    }
}

fn strip_return_values_in_stmt(stmt: &mut CStmt) {
    match stmt {
        CStmt::Return(val @ Some(_)) => {
            *val = None;
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    strip_return_values_in_stmt(s);
                }
            }
        }
        CStmt::If(_, then_s, else_s) => {
            strip_return_values_in_stmt(then_s);
            if let Some(e) = else_s {
                strip_return_values_in_stmt(e);
            }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) => strip_return_values_in_stmt(body),
        CStmt::For(_, _, _, body) => strip_return_values_in_stmt(body),
        CStmt::Switch(_, body) => strip_return_values_in_stmt(body),
        CStmt::Labeled(_, inner) => strip_return_values_in_stmt(inner),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                strip_return_values_in_stmt(s);
            }
        }
        _ => {}
    }
}

pub(crate) fn sanitize_c_ident(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for (i, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else if i > 0 {
            out.push('_');
        }
    }
    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

pub(crate) fn sanitize_c_symbol_name(name: &str) -> String {
    const RESERVED_GLOBALS: &[&str] = &[
        "stdin",
        "stdout",
        "stderr",
        "optind",
        "optarg",
        "opterr",
        "optopt",
        "errno",
        "environ",
        "program_invocation_name",
        "program_invocation_short_name",
    ];

    let base_name = name.split('@').next().unwrap_or(name);
    if RESERVED_GLOBALS.contains(&base_name) {
        let mut out = sanitize_c_ident(base_name);
        out.push_str("_sym");
        return out;
    }

    let mut out = sanitize_c_ident(name);
    if RESERVED_GLOBALS.contains(&out.as_str()) {
        out.push_str("_sym");
    }
    out
}

struct VarRenamer {
    map: HashMap<String, String>,
    counter: usize,
    used_names: HashSet<String>,
}

impl VarRenamer {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            counter: 0,
            used_names: HashSet::new(),
        }
    }

    fn seed_param(&mut self, name: &str, index: usize, dwarf_name: Option<&str>) {
        if self.map.contains_key(name) {
            return;
        }
        let short = if let Some(dname) = dwarf_name {
            let sanitized = sanitize_c_ident(dname);
            if self.used_names.contains(&sanitized) {
                format!("p{}", index)
            } else {
                sanitized
            }
        } else {
            format!("p{}", index)
        };
        self.used_names.insert(short.clone());
        self.map.insert(name.to_string(), short);
    }

    // ensure_mapping compacts a name only when it is a synthetic-reg name var_<5+ digit decimal> (fresh_xtl_reg sets bit 63, producing ~19-digit values); everything else (short var_N for real machine regs, params, globals) passes through rename() unchanged.
    fn is_renameable(name: &str) -> bool {
        match name.strip_prefix("var_") {
            Some(suffix) => suffix.len() > 4 && suffix.chars().all(|c| c.is_ascii_digit()),
            None => false,
        }
    }

    // Reserve a pass-through name so counter-based compaction never collides with it: short var_N names (e.g. var_0 from RTLReg 0) keep their literal spelling, so a compacted synthetic reg must not also be assigned that spelling.
    fn reserve(&mut self, name: &str) {
        if !Self::is_renameable(name) {
            self.used_names.insert(name.to_string());
        }
    }

    fn ensure_mapping(&mut self, name: &str) {
        if self.map.contains_key(name) {
            return;
        }
        if Self::is_renameable(name) {
            // Skip counter values already taken by a reserved pass-through name or a previously compacted reg, so two distinct slots never share one name.
            let short = loop {
                let candidate = format!("var_{:x}", self.counter);
                self.counter += 1;
                if !self.used_names.contains(&candidate) {
                    break candidate;
                }
            };
            self.used_names.insert(short.clone());
            self.map.insert(name.to_string(), short);
        }
    }

    fn rename(&self, name: &str) -> String {
        self.map.get(name).cloned().unwrap_or_else(|| name.to_string())
    }
}

impl ExprTransform for VarRenamer {
    fn transform_expr(&mut self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::Var(name) => {
                self.ensure_mapping(&name);
                CExpr::Var(self.rename(&name))
            }
            other => self.walk_expr(other),
        }
    }
}

impl StmtTransform for VarRenamer {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Decl(decls) => CStmt::Decl(
                decls
                    .into_iter()
                    .map(|mut d| {
                        self.ensure_mapping(&d.name);
                        d.name = self.rename(&d.name);
                        d.init = d.init.map(|i| self.transform_initializer(i));
                        d
                    })
                    .collect(),
            ),
            other => self.walk_stmt(other),
        }
    }
}

fn is_long_type(ty: &CType) -> bool {
    use crate::decompile::passes::c_pass::types::{IntSize, Signedness};
    matches!(
        ty,
        CType::Int(IntSize::Long, Signedness::Signed)
            | CType::Int(IntSize::Long, Signedness::Unsigned)
            | CType::Int(IntSize::LongLong, Signedness::Signed)
            | CType::Int(IntSize::LongLong, Signedness::Unsigned)
    )
}

fn collect_var_names_from_expr(expr: &CExpr, vars: &mut HashSet<String>) {
    match expr {
        CExpr::Var(name) => {
            vars.insert(name.clone());
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner) => collect_var_names_from_expr(inner, vars),
        CExpr::MemberPtr(inner, _) | CExpr::Member(inner, _) => {
            collect_var_names_from_expr(inner, vars)
        }
        CExpr::Binary(_, lhs, rhs) | CExpr::Assign(_, lhs, rhs) | CExpr::Index(lhs, rhs) => {
            collect_var_names_from_expr(lhs, vars);
            collect_var_names_from_expr(rhs, vars);
        }
        CExpr::Ternary(c, t, e) => {
            collect_var_names_from_expr(c, vars);
            collect_var_names_from_expr(t, vars);
            collect_var_names_from_expr(e, vars);
        }
        CExpr::Call(func, args) => {
            // Skip direct callee names (functions, not local variables) but recurse into non-trivial callee expressions.
            match func.as_ref() {
                CExpr::Var(_) => {}
                CExpr::Cast(_, inner) if matches!(inner.as_ref(), CExpr::Var(_)) => {}
                _ => collect_var_names_from_expr(func, vars),
            }
            for a in args {
                collect_var_names_from_expr(a, vars);
            }
        }
        CExpr::CompoundLit(_, inits) => {
            for init in inits {
                collect_var_names_from_initializer(init, vars);
            }
        }
        CExpr::Generic(sel, arms) => {
            collect_var_names_from_expr(sel, vars);
            for (_, arm_expr) in arms {
                collect_var_names_from_expr(arm_expr, vars);
            }
        }
        CExpr::StmtExpr(stmts, tail) => {
            for s in stmts {
                collect_var_names_from_stmt(s, vars);
            }
            collect_var_names_from_expr(tail, vars);
        }
        CExpr::SizeofType(_)
        | CExpr::AlignofType(_)
        | CExpr::IntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_) => {}
    }
}

fn collect_var_names_from_initializer(
    init: &crate::decompile::passes::c_pass::types::Initializer,
    vars: &mut HashSet<String>,
) {
    match init {
        crate::decompile::passes::c_pass::types::Initializer::Expr(e) => collect_var_names_from_expr(e, vars),
        crate::decompile::passes::c_pass::types::Initializer::List(items) => {
            for item in items {
                collect_var_names_from_initializer(&item.init, vars);
            }
        }
        crate::decompile::passes::c_pass::types::Initializer::String(_) => {}
    }
}

pub struct ConversionContext {
    pub id_to_name: HashMap<usize, String>,
    #[allow(dead_code)]
    pub global_names: HashSet<String>,
    pub string_globals: HashSet<usize>,
    #[allow(dead_code)]
    name_counter: usize,
    temp_names: HashMap<usize, String>,
    pub var_types: HashMap<String, CType>,
    pub string_label_to_content: HashMap<String, String>,
    pub suppress_string_literals: bool,
    pub func_addrs_sorted: Vec<(u64, String)>,
}

impl ConversionContext {
    pub fn new(id_to_name: HashMap<usize, String>) -> Self {
        let global_names = id_to_name.values().cloned().collect();
        Self {
            id_to_name,
            global_names,
            string_globals: HashSet::new(),
            name_counter: 0,
            temp_names: HashMap::new(),
            var_types: HashMap::new(),
            string_label_to_content: HashMap::new(),
            suppress_string_literals: false,
            func_addrs_sorted: Vec::new(),
        }
    }

    pub fn record_var_type(&mut self, var_name: &str, ty: CType) {
        self.var_types.entry(var_name.to_string()).or_insert(ty);
    }

    pub fn temp_name(&mut self, id: usize) -> String {
        if let Some(name) = self.temp_names.get(&id) {
            return name.clone();
        }
        let name = format!("var_{}", id);
        self.temp_names.insert(id, name.clone());
        name
    }

    pub fn var_name(&self, id: usize) -> String {
        self.id_to_name
            .get(&id)
            .map(|name| sanitize_c_symbol_name(name))
            .unwrap_or_else(|| format!("var_{}", id))
    }

    pub fn label_name(&self, id: usize) -> String {
        let raw = self
            .id_to_name
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("L{}", id));

        if raw.chars().all(|c| c.is_ascii_digit()) {
            format!("L{}", raw)
        } else {
            sanitize_c_ident(&raw)
        }
    }

    pub fn resolve_l_label(&self, name: &str) -> String {
        let hex_str = if name.starts_with("L_") {
            &name[2..]
        } else {
            return name.to_string();
        };
        if hex_str.is_empty() || !hex_str.chars().all(|c| c.is_ascii_hexdigit()) {
            return sanitize_c_ident(name);
        }
        let addr = match u64::from_str_radix(hex_str, 16) {
            Ok(a) => a,
            Err(_) => return sanitize_c_ident(name),
        };
        match self.func_addrs_sorted.binary_search_by_key(&addr, |(a, _)| *a) {
            Ok(idx) => {
                sanitize_c_symbol_name(&self.func_addrs_sorted[idx].1)
            }
            Err(idx) => {
                if idx > 0 {
                    sanitize_c_symbol_name(&self.func_addrs_sorted[idx - 1].1)
                } else {
                    sanitize_c_ident(name)
                }
            }
        }
    }
}


fn convert_unary_op(op: &clight::ClightUnaryOp) -> UnaryOp {
    match op {
        clight::ClightUnaryOp::Onotbool => UnaryOp::Not,
        clight::ClightUnaryOp::Onotint => UnaryOp::BitNot,
        clight::ClightUnaryOp::Oneg => UnaryOp::Neg,
        clight::ClightUnaryOp::Oabsfloat => UnaryOp::Plus,
    }
}

fn cexpr_is_pointer(e: &CExpr, types: &HashMap<String, CType>) -> bool {
    match e {
        CExpr::Cast(ty, _) => ty.is_pointer(),
        CExpr::Var(name) => types.get(name).map_or(false, |t| t.is_pointer()),
        CExpr::Paren(inner) => cexpr_is_pointer(inner, types),
        CExpr::Unary(UnaryOp::AddrOf, _) => true,
        // ptr +/- int yields a pointer; comparisons/other ops do not.
        CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, l, r) => {
            cexpr_is_pointer(l, types) || cexpr_is_pointer(r, types)
        }
        _ => false,
    }
}

// Machine address arithmetic is computed in integer registers, but type recovery can type those operands as pointers, and C rejects `ptr*int`, `ptr&int`, `ptr+ptr`, mixed `ptr-ptr`, etc. Cast the offending pointer operands to `long` so the arithmetic is valid integer arithmetic; the result is converted back by the surrounding cast (if any). Genuine `ptr+int` / `ptr-int` are left intact.
fn repair_pointer_arith(
    op: BinaryOp,
    lhs: CExpr,
    lhs_ptr: bool,
    rhs: CExpr,
    rhs_ptr: bool,
) -> (CExpr, CExpr) {
    let to_long = |e: CExpr| CExpr::Cast(CType::long(), Box::new(e));
    match op {
        BinaryOp::Mul
        | BinaryOp::Div
        | BinaryOp::Mod
        | BinaryOp::BitAnd
        | BinaryOp::BitOr
        | BinaryOp::BitXor
        | BinaryOp::Shl
        | BinaryOp::Shr => (
            if lhs_ptr { to_long(lhs) } else { lhs },
            if rhs_ptr { to_long(rhs) } else { rhs },
        ),
        // ptr + ptr is invalid; ptr - ptr we normalize to an integer (byte) difference.
        BinaryOp::Add | BinaryOp::Sub if lhs_ptr && rhs_ptr => (to_long(lhs), to_long(rhs)),
        // int - ptr is invalid C (a pointer may only be subtracted from a pointer); cast the pointer operand to long so it becomes integer subtraction (ptr - int and ptr + int are kept).
        BinaryOp::Sub if rhs_ptr && !lhs_ptr => (lhs, to_long(rhs)),
        _ => (lhs, rhs),
    }
}

// Walk an expression bottom-up, repairing invalid pointer arithmetic at every Binary node.
fn repair_arith_expr(e: &CExpr, types: &HashMap<String, CType>) -> CExpr {
    match e {
        CExpr::Binary(op, l, r) => {
            let l = repair_arith_expr(l, types);
            let r = repair_arith_expr(r, types);
            let lp = cexpr_is_pointer(&l, types);
            let rp = cexpr_is_pointer(&r, types);
            let (l, r) = repair_pointer_arith(*op, l, lp, r, rp);
            CExpr::Binary(*op, Box::new(l), Box::new(r))
        }
        CExpr::Unary(op, inner) => {
            let inner = repair_arith_expr(inner, types);
            // `-ptr` and `~ptr` are invalid C; cast the pointer operand to long (Deref/AddrOf/Not are valid on pointers and left alone).
            let inner = if matches!(op, UnaryOp::Neg | UnaryOp::BitNot) && cexpr_is_pointer(&inner, types) {
                CExpr::Cast(CType::long(), Box::new(inner))
            } else {
                inner
            };
            CExpr::Unary(*op, Box::new(inner))
        }
        CExpr::Assign(op, l, r) => CExpr::Assign(
            *op,
            Box::new(repair_arith_expr(l, types)),
            Box::new(repair_arith_expr(r, types)),
        ),
        CExpr::Ternary(c, t, f) => CExpr::Ternary(
            Box::new(repair_arith_expr(c, types)),
            Box::new(repair_arith_expr(t, types)),
            Box::new(repair_arith_expr(f, types)),
        ),
        CExpr::Call(f, args) => CExpr::Call(
            Box::new(repair_arith_expr(f, types)),
            args.iter().map(|a| repair_arith_expr(a, types)).collect(),
        ),
        CExpr::Cast(ty, inner) => CExpr::Cast(ty.clone(), Box::new(repair_arith_expr(inner, types))),
        CExpr::Member(inner, fld) => {
            // `e.field` where e is a pointer must be `e->field`; type recovery sometimes declares the base as a pointer while emitting a value member access ("X is a pointer; use ->").
            let inner = repair_arith_expr(inner, types);
            if cexpr_is_pointer(&inner, types) {
                CExpr::MemberPtr(Box::new(inner), fld.clone())
            } else {
                CExpr::Member(Box::new(inner), fld.clone())
            }
        }
        CExpr::MemberPtr(inner, fld) => CExpr::MemberPtr(Box::new(repair_arith_expr(inner, types)), fld.clone()),
        CExpr::Index(a, i) => CExpr::Index(
            Box::new(repair_arith_expr(a, types)),
            Box::new(repair_arith_expr(i, types)),
        ),
        CExpr::SizeofExpr(inner) => CExpr::SizeofExpr(Box::new(repair_arith_expr(inner, types))),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(repair_arith_expr(inner, types))),
        CExpr::StmtExpr(stmts, inner) => CExpr::StmtExpr(
            stmts.iter().map(|s| repair_arith_stmt(s, types)).collect(),
            Box::new(repair_arith_expr(inner, types)),
        ),
        other => other.clone(),
    }
}

// Walk a statement tree, applying repair_arith_expr to every contained expression.
fn repair_arith_stmt(stmt: &CStmt, types: &HashMap<String, CType>) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(repair_arith_expr(e, types)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(repair_arith_stmt(s, types)),
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            repair_arith_expr(cond, types),
            Box::new(repair_arith_stmt(then_s, types)),
            else_s.as_ref().map(|e| Box::new(repair_arith_stmt(e, types))),
        ),
        CStmt::While(cond, body) => CStmt::While(
            repair_arith_expr(cond, types),
            Box::new(repair_arith_stmt(body, types)),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(repair_arith_stmt(body, types)),
            repair_arith_expr(cond, types),
        ),
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.as_ref().map(|c| repair_arith_expr(c, types)),
            update.as_ref().map(|u| repair_arith_expr(u, types)),
            Box::new(repair_arith_stmt(body, types)),
        ),
        CStmt::Return(Some(e)) => CStmt::Return(Some(repair_arith_expr(e, types))),
        CStmt::Switch(e, body) => {
            // `switch (ptr)` is invalid C (switch quantity not an integer); cast to long.
            let e = repair_arith_expr(e, types);
            let e = if cexpr_is_pointer(&e, types) {
                CExpr::Cast(CType::long(), Box::new(e))
            } else {
                e
            };
            CStmt::Switch(e, Box::new(repair_arith_stmt(body, types)))
        }
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(lbl.clone(), Box::new(repair_arith_stmt(inner, types))),
        CStmt::Sequence(stmts) => CStmt::Sequence(stmts.iter().map(|s| repair_arith_stmt(s, types)).collect()),
        other => other.clone(),
    }
}

// Pad/truncate each call's argument list to the callee's declared fixed-arity parameter count so calls agree with the prototype/definition (forward declarations make this checked), padding with 0 (a valid integer / null-pointer constant); `counts` holds only fixed-arity callees, so variadic and unspecified-prototype (K&R) calls are left untouched.
fn normalize_call_arity_expr(e: &CExpr, counts: &HashMap<String, usize>) -> CExpr {
    match e {
        CExpr::Call(func, args) => {
            let nf = normalize_call_arity_expr(func, counts);
            let mut nargs: Vec<CExpr> = args.iter().map(|a| normalize_call_arity_expr(a, counts)).collect();
            if let CExpr::Var(name) = &nf {
                if let Some(&pc) = counts.get(name) {
                    if nargs.len() > pc {
                        nargs.truncate(pc);
                    } else {
                        while nargs.len() < pc {
                            nargs.push(CExpr::int(0));
                        }
                    }
                }
            }
            CExpr::Call(Box::new(nf), nargs)
        }
        CExpr::Unary(op, i) => CExpr::Unary(*op, Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::Binary(op, l, r) => CExpr::Binary(*op, Box::new(normalize_call_arity_expr(l, counts)), Box::new(normalize_call_arity_expr(r, counts))),
        CExpr::Assign(op, l, r) => CExpr::Assign(*op, Box::new(normalize_call_arity_expr(l, counts)), Box::new(normalize_call_arity_expr(r, counts))),
        CExpr::Ternary(c, t, f) => CExpr::Ternary(Box::new(normalize_call_arity_expr(c, counts)), Box::new(normalize_call_arity_expr(t, counts)), Box::new(normalize_call_arity_expr(f, counts))),
        CExpr::Cast(ty, i) => CExpr::Cast(ty.clone(), Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::Member(i, f) => CExpr::Member(Box::new(normalize_call_arity_expr(i, counts)), f.clone()),
        CExpr::MemberPtr(i, f) => CExpr::MemberPtr(Box::new(normalize_call_arity_expr(i, counts)), f.clone()),
        CExpr::Index(a, i) => CExpr::Index(Box::new(normalize_call_arity_expr(a, counts)), Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::SizeofExpr(i) => CExpr::SizeofExpr(Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::Paren(i) => CExpr::Paren(Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::StmtExpr(stmts, i) => CExpr::StmtExpr(
            stmts.iter().map(|s| normalize_call_arity_stmt(s, counts)).collect(),
            Box::new(normalize_call_arity_expr(i, counts)),
        ),
        other => other.clone(),
    }
}

fn normalize_call_arity_stmt(stmt: &CStmt, counts: &HashMap<String, usize>) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(normalize_call_arity_expr(e, counts)),
        CStmt::Block(items) => CStmt::Block(items.iter().map(|item| match item {
            CBlockItem::Stmt(s) => CBlockItem::Stmt(normalize_call_arity_stmt(s, counts)),
            other => other.clone(),
        }).collect()),
        CStmt::If(c, t, e) => CStmt::If(
            normalize_call_arity_expr(c, counts),
            Box::new(normalize_call_arity_stmt(t, counts)),
            e.as_ref().map(|x| Box::new(normalize_call_arity_stmt(x, counts))),
        ),
        CStmt::While(c, b) => CStmt::While(normalize_call_arity_expr(c, counts), Box::new(normalize_call_arity_stmt(b, counts))),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(Box::new(normalize_call_arity_stmt(b, counts)), normalize_call_arity_expr(c, counts)),
        CStmt::For(init, c, u, b) => CStmt::For(
            init.clone(),
            c.as_ref().map(|x| normalize_call_arity_expr(x, counts)),
            u.as_ref().map(|x| normalize_call_arity_expr(x, counts)),
            Box::new(normalize_call_arity_stmt(b, counts)),
        ),
        CStmt::Return(Some(e)) => CStmt::Return(Some(normalize_call_arity_expr(e, counts))),
        CStmt::Switch(e, b) => CStmt::Switch(normalize_call_arity_expr(e, counts), Box::new(normalize_call_arity_stmt(b, counts))),
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(lbl.clone(), Box::new(normalize_call_arity_stmt(inner, counts))),
        CStmt::Sequence(stmts) => CStmt::Sequence(stmts.iter().map(|s| normalize_call_arity_stmt(s, counts)).collect()),
        other => other.clone(),
    }
}

// Compilability: insert explicit (T) casts at int<->pointer mismatches, which modern clang (>=15) and gcc (>=14) reject as HARD errors even under `-w`; only the pointer-vs-integer pair is coerced (an explicit cast between scalars is always legal), while float<->pointer (itself illegal, the upstream selector's job) and unknown-class operands (casting risks making a legal conversion illegal) are left alone.

#[derive(PartialEq, Eq, Clone, Copy)]
enum ScalarClass {
    Ptr,
    Int,
    Float,
    Other,
}

fn ctype_scalar_class(t: &CType) -> ScalarClass {
    match t {
        CType::Pointer(..) | CType::Array(..) => ScalarClass::Ptr,
        CType::Int(..) | CType::Bool | CType::Enum(..) => ScalarClass::Int,
        CType::Float(..) => ScalarClass::Float,
        _ => ScalarClass::Other,
    }
}

// Best-effort static class of an expression's value; Other == unknown (left untouched).
fn cexpr_scalar_class(
    e: &CExpr,
    types: &HashMap<String, CType>,
    callee_ret: &HashMap<String, CType>,
) -> ScalarClass {
    match e {
        CExpr::Cast(ty, _) => ctype_scalar_class(ty),
        CExpr::Var(name) => types.get(name).map(ctype_scalar_class).unwrap_or(ScalarClass::Other),
        CExpr::Paren(inner) => cexpr_scalar_class(inner, types, callee_ret),
        CExpr::IntLit(_) => ScalarClass::Int,
        CExpr::FloatLit(_) => ScalarClass::Float,
        CExpr::StringLit(_) => ScalarClass::Ptr,
        CExpr::Unary(UnaryOp::AddrOf, _) => ScalarClass::Ptr,
        CExpr::Unary(UnaryOp::Neg | UnaryOp::BitNot | UnaryOp::Not | UnaryOp::Plus, _) => ScalarClass::Int,
        CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, l, r) => {
            if cexpr_scalar_class(l, types, callee_ret) == ScalarClass::Ptr
                || cexpr_scalar_class(r, types, callee_ret) == ScalarClass::Ptr
            {
                ScalarClass::Ptr
            } else {
                ScalarClass::Int
            }
        }
        CExpr::Binary(..) => ScalarClass::Int,
        CExpr::Call(f, _) => match f.as_ref() {
            CExpr::Var(n) => callee_ret.get(n).map(ctype_scalar_class).unwrap_or(ScalarClass::Other),
            _ => ScalarClass::Other,
        },
        _ => ScalarClass::Other,
    }
}

// Wrap `e` in a cast to `target` only at a genuine pointer<->integer mismatch (the hard-error pair).
fn coerce_scalar(
    target: &CType,
    e: CExpr,
    types: &HashMap<String, CType>,
    callee_ret: &HashMap<String, CType>,
) -> CExpr {
    let mismatch = matches!(
        (ctype_scalar_class(target), cexpr_scalar_class(&e, types, callee_ret)),
        (ScalarClass::Ptr, ScalarClass::Int) | (ScalarClass::Int, ScalarClass::Ptr)
    );
    if !mismatch {
        return e;
    }
    // 0 is a valid null-pointer constant and a valid integer; it never needs a cast.
    if let CExpr::IntLit(l) = &e {
        if l.value == 0 {
            return e;
        }
    }
    CExpr::Cast(target.clone(), Box::new(e))
}

// Type of an lvalue, for casting an assignment's RHS to it; handles a plain variable and a deref of a pointer variable, other lvalue forms (field, index) return None and are left untouched.
fn lvalue_ctype(e: &CExpr, types: &HashMap<String, CType>) -> Option<CType> {
    match e {
        CExpr::Var(n) => types.get(n).cloned(),
        CExpr::Paren(inner) => lvalue_ctype(inner, types),
        CExpr::Unary(UnaryOp::Deref, inner) => match lvalue_ctype(inner, types) {
            Some(CType::Pointer(t, _)) => Some(*t),
            _ => None,
        },
        _ => None,
    }
}

// name -> (param types, is_variadic, is_unspecified_K&R)
type CalleeParams = HashMap<String, (Vec<CType>, bool, bool)>;

fn insert_casts_expr(
    e: &CExpr,
    types: &HashMap<String, CType>,
    callee_params: &CalleeParams,
    callee_ret: &HashMap<String, CType>,
) -> CExpr {
    match e {
        CExpr::Call(f, args) => {
            let nf = insert_casts_expr(f, types, callee_params, callee_ret);
            let mut nargs: Vec<CExpr> = args
                .iter()
                .map(|a| insert_casts_expr(a, types, callee_params, callee_ret))
                .collect();
            if let CExpr::Var(fname) = &nf {
                if let Some((ptypes, _variadic, unspecified)) = callee_params.get(fname) {
                    // K&R `f()` is unchecked; for variadics, ptypes covers only the fixed leading parameters, so `ptypes.get(i)` naturally leaves the variadic tail untouched.
                    if !unspecified {
                        for (i, a) in nargs.iter_mut().enumerate() {
                            if let Some(pt) = ptypes.get(i) {
                                let arg = std::mem::replace(a, CExpr::int(0));
                                *a = coerce_scalar(pt, arg, types, callee_ret);
                            }
                        }
                    }
                }
            }
            CExpr::Call(Box::new(nf), nargs)
        }
        CExpr::Assign(op, lhs, rhs) => {
            let nlhs = insert_casts_expr(lhs, types, callee_params, callee_ret);
            let nrhs = insert_casts_expr(rhs, types, callee_params, callee_ret);
            if *op == AssignOp::Assign {
                if let Some(lty) = lvalue_ctype(&nlhs, types) {
                    let nrhs = coerce_scalar(&lty, nrhs, types, callee_ret);
                    return CExpr::Assign(*op, Box::new(nlhs), Box::new(nrhs));
                }
            }
            CExpr::Assign(*op, Box::new(nlhs), Box::new(nrhs))
        }
        CExpr::Unary(op, i) => CExpr::Unary(*op, Box::new(insert_casts_expr(i, types, callee_params, callee_ret))),
        CExpr::Binary(op, l, r) => CExpr::Binary(
            *op,
            Box::new(insert_casts_expr(l, types, callee_params, callee_ret)),
            Box::new(insert_casts_expr(r, types, callee_params, callee_ret)),
        ),
        CExpr::Ternary(c, t, f) => CExpr::Ternary(
            Box::new(insert_casts_expr(c, types, callee_params, callee_ret)),
            Box::new(insert_casts_expr(t, types, callee_params, callee_ret)),
            Box::new(insert_casts_expr(f, types, callee_params, callee_ret)),
        ),
        CExpr::Cast(ty, i) => CExpr::Cast(ty.clone(), Box::new(insert_casts_expr(i, types, callee_params, callee_ret))),
        CExpr::Member(i, fld) => CExpr::Member(Box::new(insert_casts_expr(i, types, callee_params, callee_ret)), fld.clone()),
        CExpr::MemberPtr(i, fld) => CExpr::MemberPtr(Box::new(insert_casts_expr(i, types, callee_params, callee_ret)), fld.clone()),
        CExpr::Index(a, i) => CExpr::Index(
            Box::new(insert_casts_expr(a, types, callee_params, callee_ret)),
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
        ),
        CExpr::SizeofExpr(i) => CExpr::SizeofExpr(Box::new(insert_casts_expr(i, types, callee_params, callee_ret))),
        CExpr::Paren(i) => CExpr::Paren(Box::new(insert_casts_expr(i, types, callee_params, callee_ret))),
        CExpr::StmtExpr(stmts, i) => CExpr::StmtExpr(
            stmts.iter().map(|s| insert_casts_stmt(s, types, callee_params, callee_ret, &CType::Void)).collect(),
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
        ),
        other => other.clone(),
    }
}

fn insert_casts_stmt(
    stmt: &CStmt,
    types: &HashMap<String, CType>,
    callee_params: &CalleeParams,
    callee_ret: &HashMap<String, CType>,
    ret_type: &CType,
) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(insert_casts_expr(e, types, callee_params, callee_ret)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(insert_casts_stmt(s, types, callee_params, callee_ret, ret_type)),
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::If(c, t, e) => CStmt::If(
            insert_casts_expr(c, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(t, types, callee_params, callee_ret, ret_type)),
            e.as_ref().map(|x| Box::new(insert_casts_stmt(x, types, callee_params, callee_ret, ret_type))),
        ),
        CStmt::While(c, b) => CStmt::While(
            insert_casts_expr(c, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(b, types, callee_params, callee_ret, ret_type)),
        ),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(
            Box::new(insert_casts_stmt(b, types, callee_params, callee_ret, ret_type)),
            insert_casts_expr(c, types, callee_params, callee_ret),
        ),
        CStmt::For(init, c, u, b) => CStmt::For(
            init.clone(),
            c.as_ref().map(|x| insert_casts_expr(x, types, callee_params, callee_ret)),
            u.as_ref().map(|x| insert_casts_expr(x, types, callee_params, callee_ret)),
            Box::new(insert_casts_stmt(b, types, callee_params, callee_ret, ret_type)),
        ),
        CStmt::Switch(e, b) => CStmt::Switch(
            insert_casts_expr(e, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(b, types, callee_params, callee_ret, ret_type)),
        ),
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(lbl.clone(), Box::new(insert_casts_stmt(inner, types, callee_params, callee_ret, ret_type))),
        CStmt::Sequence(ss) => CStmt::Sequence(ss.iter().map(|s| insert_casts_stmt(s, types, callee_params, callee_ret, ret_type)).collect()),
        CStmt::Return(Some(e)) => {
            let ne = insert_casts_expr(e, types, callee_params, callee_ret);
            let ne = if matches!(ret_type, CType::Void) { ne } else { coerce_scalar(ret_type, ne, types, callee_ret) };
            CStmt::Return(Some(ne))
        }
        other => other.clone(),
    }
}

// Whether a referenced-but-undeclared identifier should be declared as a file-scope object; excludes compiler-synthesized local/param/temporary names (var_*, p<N>, tmp*), whose absence is a local-scope recovery gap, not a missing global, and masking it with a file-scope object would hide the real bug.
fn is_global_like_name(n: &str) -> bool {
    if n.is_empty() {
        return false;
    }
    if n.starts_with("var_") || n.starts_with("tmp") {
        return false;
    }
    if n.starts_with('p') && n.len() >= 2 && n[1..].chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    true
}

fn convert_binary_op(op: &clight::ClightBinaryOp) -> BinaryOp {
    match op {
        clight::ClightBinaryOp::Oadd => BinaryOp::Add,
        clight::ClightBinaryOp::Osub => BinaryOp::Sub,
        clight::ClightBinaryOp::Omul => BinaryOp::Mul,
        clight::ClightBinaryOp::Odiv => BinaryOp::Div,
        clight::ClightBinaryOp::Omod => BinaryOp::Mod,
        clight::ClightBinaryOp::Oand => BinaryOp::BitAnd,
        clight::ClightBinaryOp::Oor => BinaryOp::BitOr,
        clight::ClightBinaryOp::Oxor => BinaryOp::BitXor,
        clight::ClightBinaryOp::Oshl => BinaryOp::Shl,
        clight::ClightBinaryOp::Oshr => BinaryOp::Shr,
        clight::ClightBinaryOp::Oeq => BinaryOp::Eq,
        clight::ClightBinaryOp::One => BinaryOp::Ne,
        clight::ClightBinaryOp::Olt => BinaryOp::Lt,
        clight::ClightBinaryOp::Ogt => BinaryOp::Gt,
        clight::ClightBinaryOp::Ole => BinaryOp::Le,
        clight::ClightBinaryOp::Oge => BinaryOp::Ge,
    }
}

pub fn convert_expr(expr: &clight::ClightExpr, ctx: &mut ConversionContext) -> CExpr {
    match expr {
        clight::ClightExpr::EconstInt(val, _ty) => {
            CExpr::IntLit(IntLiteral {
                value: *val as i128,
                suffix: IntLiteralSuffix::None,
                base: IntLiteralBase::Decimal,
            })
        }
        clight::ClightExpr::EconstLong(val, _ty) => {
            CExpr::IntLit(IntLiteral {
                value: *val as i128,
                suffix: IntLiteralSuffix::L,
                base: IntLiteralBase::Decimal,
            })
        }
        clight::ClightExpr::EconstFloat(val, _ty) => CExpr::FloatLit(FloatLiteral {
            value: val.0,
            suffix: FloatLiteralSuffix::None,
        }),
        clight::ClightExpr::EconstSingle(val, _ty) => CExpr::FloatLit(FloatLiteral {
            value: val.0 as f64,
            suffix: FloatLiteralSuffix::F,
        }),
        clight::ClightExpr::Evar(id, _ty) => {
            let raw_name = ctx
                .id_to_name
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("var_{}", id));
            if !ctx.suppress_string_literals {
                if let Some(content) = ctx.string_label_to_content.get(&raw_name) {
                    return CExpr::StringLit(StringLiteral {
                        value: content.trim_end_matches('\0').to_string(),
                        is_wide: false,
                    });
                }
            }
            CExpr::Var(ctx.var_name(*id))
        }
        clight::ClightExpr::EvarSymbol(name, _ty) => {
            if !ctx.suppress_string_literals {
                if let Some(content) = ctx.string_label_to_content.get(name) {
                    return CExpr::StringLit(StringLiteral {
                        value: content.trim_end_matches('\0').to_string(),
                        is_wide: false,
                    });
                }
            }
            CExpr::Var(sanitize_c_symbol_name(name))
        }
        clight::ClightExpr::Etempvar(id, _ty) => CExpr::Var(ctx.temp_name(*id)),
        clight::ClightExpr::Ederef(inner, _ty) => {
            CExpr::Unary(UnaryOp::Deref, Box::new(convert_expr(inner, ctx)))
        }
        clight::ClightExpr::Eaddrof(inner, _ty) => {
            match inner.as_ref() {
                clight::ClightExpr::EvarSymbol(name, _) => {
                    if let Some(content) = ctx.string_label_to_content.get(name) {
                        return CExpr::StringLit(StringLiteral {
                            value: content.trim_end_matches('\0').to_string(),
                            is_wide: false,
                        });
                    }
                }
                clight::ClightExpr::Evar(id, _) => {
                    let raw_name = ctx
                        .id_to_name
                        .get(id)
                        .cloned()
                        .unwrap_or_else(|| format!("var_{}", id));
                    if let Some(content) = ctx.string_label_to_content.get(&raw_name) {
                        return CExpr::StringLit(StringLiteral {
                            value: content.trim_end_matches('\0').to_string(),
                            is_wide: false,
                        });
                    }
                }
                _ => {}
            }
            CExpr::Unary(UnaryOp::AddrOf, Box::new(convert_expr(inner, ctx)))
        }
        clight::ClightExpr::Eunop(op, inner, _ty) => {
            if matches!(op, clight::ClightUnaryOp::Oabsfloat) {
                CExpr::Call(
                    Box::new(CExpr::Var("__builtin_fabs".to_string())),
                    vec![convert_expr(inner, ctx)],
                )
            } else {
                CExpr::Unary(convert_unary_op(op), Box::new(convert_expr(inner, ctx)))
            }
        }
        clight::ClightExpr::Ebinop(op, lhs, rhs, _ty) => {
            let is_comparison = matches!(
                op,
                clight::ClightBinaryOp::Oeq
                    | clight::ClightBinaryOp::One
                    | clight::ClightBinaryOp::Olt
                    | clight::ClightBinaryOp::Ogt
                    | clight::ClightBinaryOp::Ole
                    | clight::ClightBinaryOp::Oge
            );
            let prev_suppress = ctx.suppress_string_literals;
            if is_comparison {
                ctx.suppress_string_literals = true;
            }
            let lhs_expr = convert_expr(lhs, ctx);
            let rhs_expr = convert_expr(rhs, ctx);
            ctx.suppress_string_literals = prev_suppress;
            CExpr::Binary(convert_binary_op(op), Box::new(lhs_expr), Box::new(rhs_expr))
        }
        clight::ClightExpr::Ecast(inner, ty) => {
            CExpr::Cast(convert_clight_type(ty), Box::new(convert_expr(inner, ctx)))
        }
        clight::ClightExpr::Efield(inner, field_id, field_ty) => {
            let inner_expr = convert_expr(inner, ctx);
            let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_id);
            let inner_ct = clight_expr_to_ctype(inner);

            match &inner_expr {
                CExpr::Unary(UnaryOp::Deref, ptr_expr) => {
                    // The field access is well-typed in clight (base derefs to a struct/union), but the emitted C declaration of the base pointer can disagree (type recovery may type it as int*/void*); cast the base to the struct pointer so `->` type-checks.
                    match inner_ct {
                        ct @ (CType::Struct(_) | CType::Union(_)) => {
                            let sptr = CType::Pointer(Box::new(ct), TypeQualifiers::none());
                            CExpr::MemberPtr(
                                Box::new(CExpr::Cast(sptr, ptr_expr.clone())),
                                field_name,
                            )
                        }
                        // The base derefs to a non-aggregate (no struct/union identity recovered for it), so `->ofs_N` would be a member access through a void/scalar pointer and cannot compile. The field ident encodes the byte offset N (see field_ident_to_name); lower to a typed byte-offset deref `*(FieldTy *)((char *)base + N)`, matching Ghidra's `*(int *)(param + 0x10)` form. FieldTy comes from the Efield's own type, which is always a concrete scalar/pointer here.
                        _ => {
                            let offset = *field_id as i64;
                            let field_ctype = convert_clight_type(field_ty);
                            let char_ptr = CType::Pointer(
                                Box::new(CType::char_signed()),
                                TypeQualifiers::none(),
                            );
                            let byte_addr = CExpr::Binary(
                                BinaryOp::Add,
                                Box::new(CExpr::Cast(char_ptr, ptr_expr.clone())),
                                Box::new(CExpr::int(offset)),
                            );
                            let field_ptr = CType::Pointer(
                                Box::new(field_ctype),
                                TypeQualifiers::none(),
                            );
                            CExpr::Unary(
                                UnaryOp::Deref,
                                Box::new(CExpr::Cast(field_ptr, Box::new(byte_addr))),
                            )
                        }
                    }
                }
                _ => CExpr::Member(Box::new(inner_expr), field_name),
            }
        }
        clight::ClightExpr::Esizeof(ty, _result_ty) => CExpr::SizeofType(convert_clight_type(ty)),
        clight::ClightExpr::Ealignof(ty, _result_ty) => CExpr::AlignofType(convert_clight_type(ty)),
        clight::ClightExpr::Econdition(cond, true_val, false_val, _ty) => CExpr::Ternary(
            Box::new(convert_expr(cond, ctx)),
            Box::new(convert_expr(true_val, ctx)),
            Box::new(convert_expr(false_val, ctx)),
        ),
    }
}


/// For known varargs functions (printf, fprintf, etc.), narrow the argument list by counting format specifiers in the format string.
fn narrow_varargs_args(func_expr: &CExpr, mut args: Vec<CExpr>) -> Vec<CExpr> {
    let func_name = match func_expr {
        CExpr::Var(name) => name.as_str(),
        _ => return args,
    };

    // (function_name, format_string_position)
    let fmt_pos = match func_name {
        "printf" | "scanf" => Some(0),
        "fprintf" | "fscanf" | "sprintf" | "sscanf" | "dprintf" => Some(1),
        "snprintf" => Some(2),
        "__printf_chk" => Some(1),
        "__fprintf_chk" => Some(2),
        "__sprintf_chk" | "__snprintf_chk" => Some(3),
        _ => None,
    };

    let fmt_idx = match fmt_pos {
        Some(i) if i < args.len() => i,
        _ => return args,
    };

    // Count format specifiers (%d, %s, %x, etc.) in the format string
    let specifier_count = match &args[fmt_idx] {
        CExpr::StringLit(sl) => {
            let mut count = 0;
            let mut chars = sl.value.chars().peekable();
            while let Some(ch) = chars.next() {
                if ch == '%' {
                    match chars.peek() {
                        Some('%') => { chars.next(); } // %% is literal
                        Some(_) => count += 1,
                        None => {}
                    }
                }
            }
            count
        }
        _ => return args, // can't parse, keep all
    };

    let keep = fmt_idx + 1 + specifier_count;
    if keep >= args.len() {
        return args;
    }

    // Refuse to truncate when any trailing arg has side effects to avoid changing semantics.
    let trailing_has_effects = args[keep..].iter().any(|a| a.has_side_effects());
    if trailing_has_effects {
        log::warn!(
            "narrow_varargs_args: refusing to truncate {}() args from {} to {} -- trailing arg has side effects",
            func_name,
            args.len(),
            keep,
        );
        return args;
    }

    args.truncate(keep);
    args
}

/// Narrow varargs in all Call expressions within a CStmt (call after string inlining).
pub fn narrow_varargs_in_stmt(stmt: &CStmt) -> CStmt {
    use crate::decompile::passes::c_pass::helpers::map_stmt_exprs;
    map_stmt_exprs(stmt, &|expr| {
        if let CExpr::Call(func, args) = expr {
            let args = narrow_varargs_args(func, args.to_vec());
            Some(CExpr::Call(func.clone(), args))
        } else {
            None
        }
    })
}

/// Eliminate dead code after unconditional exits, preserving labeled goto targets.
fn eliminate_dead_code(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Block(items) => {
            let pruned = prune_block_items(items);
            match pruned.len() {
                0 => CStmt::Empty,
                _ => CStmt::Block(pruned),
            }
        }
        CStmt::Sequence(stmts) => {
            let items: Vec<CBlockItem> = stmts.iter().map(|s| CBlockItem::Stmt(s.clone())).collect();
            let pruned = prune_block_items(&items);
            let stmts: Vec<CStmt> = pruned.into_iter().filter_map(|item| match item {
                CBlockItem::Stmt(s) => Some(s),
                _ => None,
            }).collect();
            match stmts.len() {
                0 => CStmt::Empty,
                1 => stmts.into_iter().next().unwrap(),
                _ => CStmt::Sequence(stmts),
            }
        }
        CStmt::If(cond, then_s, else_s) => {
            CStmt::If(
                cond.clone(),
                Box::new(eliminate_dead_code(then_s)),
                else_s.as_ref().map(|e| Box::new(eliminate_dead_code(e))),
            )
        }
        CStmt::While(cond, body) => {
            CStmt::While(cond.clone(), Box::new(eliminate_dead_code(body)))
        }
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(eliminate_dead_code(body)), cond.clone())
        }
        CStmt::For(init, cond, update, body) => {
            CStmt::For(init.clone(), cond.clone(), update.clone(), Box::new(eliminate_dead_code(body)))
        }
        CStmt::Switch(expr, body) => {
            // Don't prune inside switch bodies (all case/default labels are reachable via dispatch); only recurse into individual case bodies, not the sequential structure.
            CStmt::Switch(expr.clone(), Box::new(eliminate_dead_code_in_switch(body)))
        }
        CStmt::Labeled(label, inner) => {
            CStmt::Labeled(label.clone(), Box::new(eliminate_dead_code(inner)))
        }
        other => other.clone(),
    }
}

/// Recurse into switch body items without pruning between them (all cases are dispatch targets).
fn eliminate_dead_code_in_switch(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Block(items) => {
            let cleaned: Vec<CBlockItem> = items.iter().map(|item| match item {
                CBlockItem::Stmt(s) => CBlockItem::Stmt(eliminate_dead_code(s)),
                other => other.clone(),
            }).collect();
            CStmt::Block(cleaned)
        }
        CStmt::Sequence(stmts) => {
            CStmt::Sequence(stmts.iter().map(|s| eliminate_dead_code(s)).collect())
        }
        other => eliminate_dead_code(other),
    }
}

/// Prune block items after unconditional exits, preserving named labels (goto targets).
fn prune_block_items(items: &[CBlockItem]) -> Vec<CBlockItem> {
    let mut result = Vec::new();
    let mut terminated = false;
    for item in items {
        match item {
            CBlockItem::Stmt(s) => {
                // First, recursively eliminate dead code within the statement
                let cleaned = eliminate_dead_code(s);
                if matches!(cleaned, CStmt::Empty) {
                    continue;
                }
                if terminated {
                    // Preserve labeled stmts and loop/switch constructs after terminators.
                    if contains_named_label(&cleaned) || is_control_flow_construct(&cleaned) {
                        let exits = is_unconditional_exit(&cleaned);
                        result.push(CBlockItem::Stmt(cleaned));
                        terminated = exits;
                    }
                } else {
                    let exits = is_unconditional_exit(&cleaned);
                    result.push(CBlockItem::Stmt(cleaned));
                    if exits {
                        terminated = true;
                    }
                }
            }
            CBlockItem::Decl(decls) => {
                // Always keep declarations (they don't produce dead code)
                result.push(CBlockItem::Decl(decls.clone()));
            }
        }
    }
    result
}

/// True if stmt is a loop/switch that should survive DCE after a terminator.
fn is_control_flow_construct(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::While(_, _) | CStmt::DoWhile(_, _) | CStmt::For(_, _, _, _)
        | CStmt::Switch(_, _) => true,
        CStmt::Labeled(_, inner) => is_control_flow_construct(inner),
        _ => false,
    }
}

/// Returns true if stmt unconditionally exits (return/goto/break/continue).
fn is_unconditional_exit(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) | CStmt::Goto(_) | CStmt::Break | CStmt::Continue => true,
        // Labeled stmt exit status depends on inner stmt (subsequent code still dead if inner exits).
        CStmt::Labeled(_, inner) => is_unconditional_exit(inner),
        CStmt::Block(items) => {
            // A block exits if its last statement exits
            items.iter().rev().find_map(|item| match item {
                CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty) => Some(is_unconditional_exit(s)),
                _ => None,
            }).unwrap_or(false)
        }
        CStmt::Sequence(stmts) => {
            stmts.iter().rev().find_map(|s| {
                if !matches!(s, CStmt::Empty) { Some(is_unconditional_exit(s)) } else { None }
            }).unwrap_or(false)
        }
        CStmt::If(_, then_s, Some(else_s)) => {
            is_unconditional_exit(then_s) && is_unconditional_exit(else_s)
        }
        _ => false,
    }
}

/// Returns true if a CStmt contains a Named label (goto target), ignoring case/default labels (used to check switch bodies without false positives from case labels).
fn contains_goto_target(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Labeled(Label::Named(_), _) => true,
        CStmt::Labeled(_, inner) => contains_goto_target(inner),
        CStmt::Block(items) => items.iter().any(|item| match item {
            CBlockItem::Stmt(s) => contains_goto_target(s),
            _ => false,
        }),
        CStmt::Sequence(stmts) => stmts.iter().any(contains_goto_target),
        CStmt::If(_, then_s, else_s) => {
            contains_goto_target(then_s)
                || else_s.as_ref().map_or(false, |e| contains_goto_target(e))
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) => {
            contains_goto_target(body)
        }
        CStmt::Switch(_, body) => contains_goto_target(body),
        _ => false,
    }
}

/// Returns true if a CStmt contains any reachable label (named goto targets, case/default).
fn contains_named_label(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Labeled(Label::Named(_), _) => true,
        CStmt::Labeled(Label::Case(_), _) | CStmt::Labeled(Label::Default, _) => true,
        CStmt::Labeled(_, inner) => contains_named_label(inner),
        CStmt::Block(items) => items.iter().any(|item| match item {
            CBlockItem::Stmt(s) => contains_named_label(s),
            _ => false,
        }),
        CStmt::Sequence(stmts) => stmts.iter().any(contains_named_label),
        CStmt::If(_, then_s, else_s) => {
            contains_named_label(then_s)
                || else_s.as_ref().map_or(false, |e| contains_named_label(e))
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) => {
            contains_named_label(body)
        }
        // Dead switch only preserved if it contains a Named goto target (case labels aren't external).
        CStmt::Switch(_, body) => contains_goto_target(body),
        _ => false,
    }
}

pub fn convert_stmt(stmt: &clight::ClightStmt, ctx: &mut ConversionContext) -> CStmt {
    match stmt {
        clight::ClightStmt::Sskip => CStmt::Empty,

        clight::ClightStmt::Sassign(lhs, rhs) => {
            let lhs_expr = convert_expr(lhs, ctx);
            let rhs_expr = convert_expr(rhs, ctx);
            CStmt::Expr(CExpr::Assign(
                AssignOp::Assign,
                Box::new(lhs_expr),
                Box::new(rhs_expr),
            ))
        }

        clight::ClightStmt::Sset(id, expr) => {
            let var_name = ctx.temp_name(*id);
            let var_type = clight_expr_to_ctype(expr);
            ctx.record_var_type(&var_name, var_type);
            let rhs_expr = convert_expr(expr, ctx);
            CStmt::Expr(CExpr::Assign(
                AssignOp::Assign,
                Box::new(CExpr::Var(var_name.clone())),
                Box::new(rhs_expr),
            ))
        }

        clight::ClightStmt::Scall(dst, func, args) => {
            let func_expr = convert_expr(func, ctx);
            let func_expr = if let CExpr::Var(ref name) = func_expr {
                let resolved = ctx.resolve_l_label(name);
                if resolved != *name {
                    CExpr::Var(resolved)
                } else {
                    func_expr
                }
            } else {
                func_expr
            };
            let arg_exprs: Vec<CExpr> = args.iter().map(|a| convert_expr(a, ctx)).collect();
            let call_expr = CExpr::Call(Box::new(func_expr), arg_exprs);

            if let Some(id) = dst {
                let var_name = ctx.temp_name(*id);
                CStmt::Expr(CExpr::Assign(
                    AssignOp::Assign,
                    Box::new(CExpr::Var(var_name)),
                    Box::new(call_expr),
                ))
            } else {
                CStmt::Expr(call_expr)
            }
        }

        clight::ClightStmt::Sbuiltin(dst, ef, _tys, args) => {
            let func_name = external_func_name(ef);
            let arg_exprs: Vec<CExpr> = args.iter().map(|a| convert_expr(a, ctx)).collect();
            let call_expr = CExpr::Call(Box::new(CExpr::Var(func_name)), arg_exprs);

            if let Some(id) = dst {
                let var_name = ctx.temp_name(*id);
                CStmt::Expr(CExpr::Assign(
                    AssignOp::Assign,
                    Box::new(CExpr::Var(var_name)),
                    Box::new(call_expr),
                ))
            } else {
                CStmt::Expr(call_expr)
            }
        }

        clight::ClightStmt::Ssequence(stmts) => {
            let mut converted: Vec<CBlockItem> = Vec::new();
            let mut terminated = false;
            for s in stmts {
                let c = convert_stmt(s, ctx);
                if terminated {
                    // After unconditional exit, keep named-label stmts (goto targets) and loop/switch constructs (bodies may host code reachable via gotos/cases).
                    if contains_named_label(&c) || is_control_flow_construct(&c) {
                        let exits = is_unconditional_exit(&c);
                        converted.push(CBlockItem::Stmt(c));
                        // A preserved label can restart reachability for following fallthrough code.
                        terminated = exits;
                    }
                } else {
                    let exits = is_unconditional_exit(&c);
                    converted.push(CBlockItem::Stmt(c));
                    if exits {
                        terminated = true;
                    }
                }
            }
            if converted.len() == 1 {
                match converted.into_iter().next().unwrap() {
                    CBlockItem::Stmt(s) => s,
                    _ => unreachable!(),
                }
            } else {
                CStmt::Block(converted)
            }
        }

        clight::ClightStmt::Sifthenelse(cond, then_stmt, else_stmt) => {
            let cond_expr = convert_expr(cond, ctx);
            let then_s = convert_stmt(then_stmt, ctx);
            let else_s = convert_stmt(else_stmt, ctx);

            let else_opt = if matches!(else_s, CStmt::Empty) {
                None
            } else {
                Some(Box::new(else_s))
            };

            CStmt::If(cond_expr, Box::new(then_s), else_opt)
        }

        clight::ClightStmt::Sloop(body, cont) => {
            let body_stmt = convert_stmt(body, ctx);
            let cont_stmt = convert_stmt(cont, ctx);
            let has_update = !matches!(cont_stmt, CStmt::Empty);
            let update = if has_update { extract_loop_update(&cont_stmt) } else { None };

            if let Some((cond, rest_body, is_pre)) = extract_loop_condition(&body_stmt) {
                if is_pre {
                    if has_update {
                        CStmt::For(None, Some(cond), update, Box::new(rest_body))
                    } else {
                        CStmt::While(cond, Box::new(rest_body))
                    }
                } else if has_update {
                    // Post-condition with update becomes for(;1;update) loop
                    CStmt::For(None, Some(CExpr::int(1)), update, Box::new(body_stmt))
                } else {
                    CStmt::DoWhile(Box::new(rest_body), cond)
                }
            } else if has_update {
                CStmt::For(None, Some(CExpr::int(1)), update, Box::new(body_stmt))
            } else {
                CStmt::While(CExpr::int(1), Box::new(body_stmt))
            }
        }

        clight::ClightStmt::Sbreak => CStmt::Break,
        clight::ClightStmt::Scontinue => CStmt::Continue,

        clight::ClightStmt::Sreturn(None) => CStmt::Return(None),
        clight::ClightStmt::Sreturn(Some(expr)) => CStmt::Return(Some(convert_expr(expr, ctx))),

        clight::ClightStmt::Sswitch(expr, cases) => {
            if let Some(range_if) = try_switch_to_range_if(expr, cases, ctx) {
                range_if
            } else {
                let switch_expr = convert_expr(expr, ctx);
                let body = convert_switch_cases(cases, ctx);
                CStmt::Switch(switch_expr, Box::new(body))
            }
        }

        clight::ClightStmt::Slabel(label_id, inner) => {
            let label_name = ctx.label_name(*label_id);
            let inner_stmt = convert_stmt(inner, ctx);
            CStmt::Labeled(Label::Named(label_name), Box::new(inner_stmt))
        }

        clight::ClightStmt::Sgoto(label_id) => {
            let label_name = ctx.label_name(*label_id);
            CStmt::Goto(label_name)
        }
    }
}

fn extract_loop_condition(body: &CStmt) -> Option<(CExpr, CStmt, bool)> {
    if let Some(cond) = extract_condition_break(body) {
        return Some((cond, CStmt::Empty, true));
    }

    let stmts: Vec<&CStmt> = match body {
        CStmt::Sequence(stmts) if stmts.len() >= 2 => stmts.iter().collect(),
        CStmt::Block(items) if items.len() >= 1 => {
            items.iter().filter_map(|item| match item {
                CBlockItem::Stmt(s) => Some(s),
                _ => None,
            }).collect()
        }
        _ => return None,
    };

    if stmts.is_empty() {
        return None;
    }

    if stmts.len() == 1 {
        if let Some(cond) = extract_condition_break(stmts[0]) {
            return Some((cond, CStmt::Empty, true));
        }
        return None;
    }

    if let Some(cond) = extract_condition_break(stmts[0]) {
        let rest: Vec<CStmt> = stmts[1..].iter().map(|s| (*s).clone()).collect();
        let rest_stmt = if rest.len() == 1 {
            rest.into_iter().next().unwrap()
        } else {
            CStmt::Sequence(rest)
        };
        return Some((cond, rest_stmt, true));
    }

    if let Some(cond) = extract_condition_break(stmts.last().unwrap()) {
        let rest: Vec<CStmt> = stmts[..stmts.len() - 1].iter().map(|s| (*s).clone()).collect();
        let rest_stmt = if rest.len() == 1 {
            rest.into_iter().next().unwrap()
        } else {
            CStmt::Sequence(rest)
        };
        return Some((cond, rest_stmt, false));
    }

    None
}

fn extract_condition_break(stmt: &CStmt) -> Option<CExpr> {
    match stmt {
        CStmt::If(cond, then_br, Some(else_br))
            if matches!(**then_br, CStmt::Empty) && matches!(**else_br, CStmt::Break) =>
        {
            Some(cond.clone())
        }
        CStmt::If(cond, then_br, None) if matches!(**then_br, CStmt::Break) => {
            Some(negate_cond(cond))
        }
        CStmt::If(cond, then_br, Some(else_br))
            if matches!(**then_br, CStmt::Break) && matches!(**else_br, CStmt::Empty) =>
        {
            Some(negate_cond(cond))
        }
        _ => None,
    }
}

fn negate_cond(cond: &CExpr) -> CExpr {
    match cond {
        CExpr::Unary(UnaryOp::Not, inner) => *inner.clone(),
        CExpr::Binary(BinaryOp::Eq, a, b) => CExpr::Binary(BinaryOp::Ne, a.clone(), b.clone()),
        CExpr::Binary(BinaryOp::Ne, a, b) => CExpr::Binary(BinaryOp::Eq, a.clone(), b.clone()),
        CExpr::Binary(BinaryOp::Lt, a, b) => CExpr::Binary(BinaryOp::Ge, a.clone(), b.clone()),
        CExpr::Binary(BinaryOp::Le, a, b) => CExpr::Binary(BinaryOp::Gt, a.clone(), b.clone()),
        CExpr::Binary(BinaryOp::Gt, a, b) => CExpr::Binary(BinaryOp::Le, a.clone(), b.clone()),
        CExpr::Binary(BinaryOp::Ge, a, b) => CExpr::Binary(BinaryOp::Lt, a.clone(), b.clone()),
        _ => CExpr::Unary(UnaryOp::Not, Box::new(cond.clone())),
    }
}

fn extract_loop_update(stmt: &CStmt) -> Option<CExpr> {
    match stmt {
        CStmt::Expr(e) => Some(e.clone()),
        CStmt::Block(items) if items.len() == 1 => match &items[0] {
            CBlockItem::Stmt(s) => extract_loop_update(s),
            _ => None,
        },
        CStmt::Block(items) => {
            let exprs: Vec<CExpr> = items
                .iter()
                .filter_map(|item| match item {
                    CBlockItem::Stmt(s) => extract_loop_update(s),
                    _ => None,
                })
                .collect();
            if exprs.len() == items.len() && !exprs.is_empty() {
                Some(
                    exprs
                        .into_iter()
                        .reduce(|acc, e| CExpr::Binary(BinaryOp::Comma, Box::new(acc), Box::new(e)))
                        .unwrap(),
                )
            } else {
                None
            }
        }
        _ => None,
    }
}

fn convert_switch_cases(
    cases: &clight::ClightLabeledStatements,
    ctx: &mut ConversionContext,
) -> CStmt {
    // Convert each (label, body) pair first.
    let converted: Vec<(Label, CStmt)> = cases
        .iter()
        .map(|(label, stmt)| {
            let label = match label {
                Some(val) => Label::Case(CExpr::int(*val)),
                None => Label::Default,
            };
            (label, convert_stmt(stmt, ctx))
        })
        .collect();

    // Collapse maximal runs of consecutive cases that share an identical, non-fall-through body
    // into one stacked-label arm (`case a: case b: <body>`), the way switch arms are written by
    // hand. A chain lowered from a jump table or comparison ladder produces one `case k: goto L;`
    // per value, so distinct values reaching the same target would otherwise emit one goto each.
    // Only bodies ending in an unconditional control transfer are merged, so stacking them cannot
    // change C fall-through accumulation semantics. Labels are nested (Labeled wrapping Labeled)
    // rather than emitted as separate empty-bodied block items, so later block-level cleanup
    // passes treat each arm as a single unit and cannot drop an intermediate label.
    let mut block_items = Vec::new();
    let mut i = 0;
    while i < converted.len() {
        let mut j = i + 1;
        if switch_body_exits(&converted[i].1) {
            while j < converted.len() && converted[j].1 == converted[i].1 {
                j += 1;
            }
        }
        let mut arm = converted[j - 1].1.clone();
        for (label, _) in converted[i..j].iter().rev() {
            arm = CStmt::Labeled(label.clone(), Box::new(arm));
        }
        block_items.push(CBlockItem::Stmt(arm));
        i = j;
    }

    CStmt::Block(block_items)
}

/// True if `stmt` ends in an unconditional control transfer, so control never falls off its end.
/// Stacking consecutive same-bodied switch cases under shared labels is sound only when the shared
/// body cannot fall through into the following case.
fn switch_body_exits(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Goto(_) | CStmt::Break | CStmt::Continue | CStmt::Return(_) => true,
        CStmt::Labeled(_, inner) => switch_body_exits(inner),
        CStmt::Sequence(stmts) => stmts.last().map_or(false, switch_body_exits),
        CStmt::Block(items) => items
            .iter()
            .rev()
            .find_map(|item| match item {
                CBlockItem::Stmt(s) => Some(s),
                _ => None,
            })
            .map_or(false, switch_body_exits),
        _ => false,
    }
}

/// Number of disjoint value ranges above which a single-target switch is left as a switch rather
/// than expanded into an `||` chain of range tests (keeps a genuinely sparse set readable as a switch).
const MAX_RANGE_IF_RUNS: usize = 8;

/// A switch whose explicit cases all branch to one identical, non-fall-through body is semantically a
/// membership test: `switch(e){case lo: ... case hi: goto L;}` == `if (e>=lo && e<=hi) goto L;`. Jump
/// tables and equality-comparison ladders lower to exactly this shape -- one `case k: goto L;` per
/// value -- which a human writes as a range / `ctype`-style `if`. Recover that form when it is
/// provably equivalent and return None (leaving the switch intact) otherwise.
///
/// Equivalence conditions, all required:
/// - the scrutinee is duplicable (no memory read), since it is evaluated once per range test;
/// - every explicit case shares one body that cannot fall through (so arm order is irrelevant and
///   unmatched values still fall past the `if`, matching switch semantics with no `default`);
/// - an optional `default` body (also non-fall-through) becomes the trailing `else`;
/// - all case values are non-negative, so the `>=`/`<=` range tests agree with the switch's integer
///   match regardless of the scrutinee's signedness (equality on the exact case constants is always
///   sound; only the relational range form is signedness-sensitive). Each emitted range covers a
///   maximal run of contiguous case labels, so every integer it admits is a real case value.
fn try_switch_to_range_if(
    expr: &clight::ClightExpr,
    cases: &clight::ClightLabeledStatements,
    ctx: &mut ConversionContext,
) -> Option<CStmt> {
    if cases.is_empty() || !clight_scrutinee_dupable(expr) {
        return None;
    }

    let mut values: Vec<i64> = Vec::new();
    let mut arm_body: Option<&clight::ClightStmt> = None;
    let mut default_body: Option<&clight::ClightStmt> = None;
    for (label, body) in cases {
        match label {
            Some(v) => {
                match arm_body {
                    None => arm_body = Some(body),
                    Some(b) if b == body => {}
                    // A second distinct target means a real multi-way dispatch; keep the switch.
                    Some(_) => return None,
                }
                values.push(*v);
            }
            None => {
                if default_body.is_some() {
                    return None;
                }
                default_body = Some(body);
            }
        }
    }

    let arm_body = arm_body?;
    if !clight_stmt_exits(arm_body) {
        return None;
    }
    if matches!(default_body, Some(d) if !clight_stmt_exits(d)) {
        return None;
    }

    values.sort_unstable();
    values.dedup();
    if values.first().map_or(true, |&v| v < 0) {
        return None;
    }

    // Collapse the sorted values into maximal runs of contiguous integers.
    let mut runs: Vec<(i64, i64)> = Vec::new();
    for &v in &values {
        match runs.last_mut() {
            Some(run) if v == run.1 + 1 => run.1 = v,
            _ => runs.push((v, v)),
        }
    }
    if runs.len() > MAX_RANGE_IF_RUNS {
        return None;
    }

    let scrutinee = convert_expr(expr, ctx);
    let mut condition: Option<CExpr> = None;
    for (lo, hi) in runs {
        let part = if lo == hi {
            CExpr::Binary(BinaryOp::Eq, Box::new(scrutinee.clone()), Box::new(CExpr::int(lo)))
        } else {
            // Wrap each `e>=lo && e<=hi` group in parens so a multi-range condition reads as
            // `(e>=lo && e<=hi) || (e>=lo2 && e<=hi2)` rather than relying on C's &&-over-|| precedence.
            CExpr::Paren(Box::new(CExpr::Binary(
                BinaryOp::And,
                Box::new(CExpr::Binary(BinaryOp::Ge, Box::new(scrutinee.clone()), Box::new(CExpr::int(lo)))),
                Box::new(CExpr::Binary(BinaryOp::Le, Box::new(scrutinee.clone()), Box::new(CExpr::int(hi)))),
            )))
        };
        condition = Some(match condition {
            None => part,
            Some(c) => CExpr::Binary(BinaryOp::Or, Box::new(c), Box::new(part)),
        });
    }

    let then_branch = convert_stmt(arm_body, ctx);
    let else_branch = default_body.map(|d| Box::new(convert_stmt(d, ctx)));
    Some(CStmt::If(condition?, Box::new(then_branch), else_branch))
}

/// True if `expr` can be evaluated more than once without changing program behavior: a constant or
/// variable read, or arithmetic over such. Excludes memory reads (`Efield`, address-of) so a range
/// `if` never duplicates a load that could alias or be volatile. The Clight expression language has
/// no call or assignment forms, so these are the only impurity concerns.
fn clight_scrutinee_dupable(expr: &clight::ClightExpr) -> bool {
    match expr {
        clight::ClightExpr::EconstInt(_, _)
        | clight::ClightExpr::EconstLong(_, _)
        | clight::ClightExpr::EconstFloat(_, _)
        | clight::ClightExpr::EconstSingle(_, _)
        | clight::ClightExpr::Evar(_, _)
        | clight::ClightExpr::EvarSymbol(_, _)
        | clight::ClightExpr::Etempvar(_, _) => true,
        clight::ClightExpr::Ecast(inner, _) | clight::ClightExpr::Eunop(_, inner, _) => {
            clight_scrutinee_dupable(inner)
        }
        clight::ClightExpr::Ebinop(_, lhs, rhs, _) => {
            clight_scrutinee_dupable(lhs) && clight_scrutinee_dupable(rhs)
        }
        _ => false,
    }
}

/// True if a Clight statement ends in an unconditional control transfer (mirrors `switch_body_exits`
/// at the Clight level, before conversion to the C AST).
fn clight_stmt_exits(stmt: &clight::ClightStmt) -> bool {
    match stmt {
        clight::ClightStmt::Sgoto(_)
        | clight::ClightStmt::Sbreak
        | clight::ClightStmt::Scontinue
        | clight::ClightStmt::Sreturn(_) => true,
        clight::ClightStmt::Slabel(_, inner) => clight_stmt_exits(inner),
        clight::ClightStmt::Ssequence(stmts) => stmts.last().map_or(false, clight_stmt_exits),
        _ => false,
    }
}

fn external_func_name(ef: &ExternalFunction) -> String {
    match ef {
        ExternalFunction::EFExternal(n, _)
        | ExternalFunction::EFBuiltin(n, _)
        | ExternalFunction::EFRuntime(n, _)
        | ExternalFunction::EFInlineAsm(n, _, _) => sanitize_c_symbol_name(n),
        ExternalFunction::EFVLoad(_) => "__builtin_vload".into(),
        ExternalFunction::EFVStore(_) => "__builtin_vstore".into(),
        ExternalFunction::EFMalloc => "malloc".into(),
        ExternalFunction::EFFree => "free".into(),
        ExternalFunction::EFMemcpy(_, _) => "memcpy".into(),
        ExternalFunction::EFAnnot(_, n, _) | ExternalFunction::EFAnnotVal(_, n, _) => sanitize_c_symbol_name(n),
        ExternalFunction::EFDebug(_, _, _) => "__builtin_debug".into(),
    }
}

fn order_nodes_dfs(
    entry: crate::x86::types::Node,
    nodes: &HashSet<crate::x86::types::Node>,
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
) -> Vec<crate::x86::types::Node> {
    let mut adjacency: HashMap<crate::x86::types::Node, Vec<crate::x86::types::Node>> = HashMap::new();
    for (src, dst) in edges {
        if nodes.contains(src) && nodes.contains(dst) {
            adjacency.entry(*src).or_default().push(*dst);
        }
    }

    for succs in adjacency.values_mut() {
        succs.sort();
    }

    let mut visited = HashSet::new();
    let mut post_order = Vec::new();
    let mut stack = Vec::new();

    enum Action {
        Visit(crate::x86::types::Node),
        PostVisit(crate::x86::types::Node),
    }

    let start_node = if nodes.contains(&entry) {
        entry
    } else {
        *nodes.iter().min().unwrap_or(&entry)
    };

    if nodes.contains(&start_node) {
        stack.push(Action::Visit(start_node));
    }

    while let Some(action) = stack.pop() {
        match action {
            Action::Visit(u) => {
                if !visited.contains(&u) {
                    visited.insert(u);
                    stack.push(Action::PostVisit(u));
                    if let Some(succs) = adjacency.get(&u) {
                        for &v in succs.iter().rev() {
                            if !visited.contains(&v) {
                                stack.push(Action::Visit(v));
                            }
                        }
                    }
                }
            }
            Action::PostVisit(u) => {
                post_order.push(u);
            }
        }
    }

    let mut result: Vec<_> = post_order.into_iter().rev().collect();

    let result_set: HashSet<_> = result.iter().copied().collect();
    let mut remaining: Vec<_> = nodes.difference(&result_set).copied().collect();
    if !remaining.is_empty() {
        remaining.sort_by_key(|&n| crate::util::exec_order_key(n));
        result.extend(remaining);
    }

    result
}

fn simplify_fallthrough_gotos_in_block(items: Vec<CBlockItem>) -> Vec<CBlockItem> {
    let mut count = 0;
    simplify_fallthrough_gotos_in_block_with_next(items, None, &mut count)
}

fn simplify_fallthrough_gotos_in_block_with_next(
    items: Vec<CBlockItem>,
    outer_next_label: Option<&str>,
    count: &mut usize,
) -> Vec<CBlockItem> {
    if items.is_empty() {
        return items;
    }

    let mut result = Vec::with_capacity(items.len());
    let mut i = 0;

    while i < items.len() {
        let current = &items[i];

        let next_label = if i + 1 < items.len() {
            get_first_label_from_item(&items[i + 1])
        } else {
            outer_next_label.map(|s| s.to_string())
        };

        match current {
            CBlockItem::Stmt(stmt) => {
                let simplified = simplify_stmt_fallthrough(stmt, next_label.as_deref(), count);
                result.push(CBlockItem::Stmt(simplified));
            }
            other => result.push(other.clone()),
        }
        i += 1;
    }

    result
}

fn simplify_stmt_fallthrough(stmt: &CStmt, next_label: Option<&str>, count: &mut usize) -> CStmt {
    match stmt {
        CStmt::Goto(target) => {
            if let Some(next_lbl) = next_label {
                if normalize_label(target) == normalize_label(next_lbl) {
                    *count += 1;
                    return CStmt::Empty;
                }
            }
            stmt.clone()
        }

        CStmt::If(cond, then_s, Some(else_s)) => {
            let simplified_then = simplify_stmt_fallthrough(then_s, next_label, count);
            let simplified_else = simplify_stmt_fallthrough(else_s, next_label, count);

            if let Some(next_lbl) = next_label {
                let else_is_fallthrough = is_goto_to_label(&simplified_else, next_lbl);
                let then_is_fallthrough = is_goto_to_label(&simplified_then, next_lbl);

                if else_is_fallthrough && then_is_fallthrough {
                    *count += 1;
                    return CStmt::Empty;
                }

                if else_is_fallthrough {
                    *count += 1;
                    return CStmt::If(cond.clone(), Box::new(simplified_then), None);
                }

                if then_is_fallthrough {
                    let negated_cond = negate_condition(cond);
                    *count += 1;
                    return CStmt::If(negated_cond, Box::new(simplified_else), None);
                }
            }

            CStmt::If(cond.clone(), Box::new(simplified_then), Some(Box::new(simplified_else)))
        }

        CStmt::If(cond, then_s, None) => {
            let simplified_then = simplify_stmt_fallthrough(then_s, next_label, count);
            CStmt::If(cond.clone(), Box::new(simplified_then), None)
        }

        CStmt::Labeled(label, inner) => {
            let simplified_inner = simplify_stmt_fallthrough(inner, next_label, count);
            CStmt::Labeled(label.clone(), Box::new(simplified_inner))
        }

        CStmt::Block(items) => {
            let simplified = simplify_fallthrough_gotos_in_block_with_next(items.clone(), next_label, count);
            CStmt::Block(simplified)
        }

        CStmt::Sequence(stmts) => {
            if stmts.is_empty() {
                return CStmt::Empty;
            }
            let mut result = Vec::with_capacity(stmts.len());
            for (j, s) in stmts.iter().enumerate() {
                let next = if j + 1 < stmts.len() {
                    get_first_label_from_stmt(&stmts[j + 1])
                } else {
                    next_label.map(|s| s.to_string())
                };
                result.push(simplify_stmt_fallthrough(s, next.as_deref(), count));
            }
            CStmt::Sequence(result)
        }

        other => other.clone(),
    }
}

fn is_goto_to_label(stmt: &CStmt, label: &str) -> bool {
    match stmt {
        CStmt::Goto(target) => {
            let target_norm = normalize_label(target);
            let label_norm = normalize_label(label);
            target_norm == label_norm
        }
        CStmt::Labeled(_, inner) => is_goto_to_label(inner, label),
        CStmt::Block(items) if items.len() == 1 => {
            if let CBlockItem::Stmt(s) = &items[0] {
                is_goto_to_label(s, label)
            } else {
                false
            }
        }
        _ => false,
    }
}

fn normalize_label(label: &str) -> String {
    let s = label.strip_prefix('.').unwrap_or(label);
    let s = s.strip_prefix('L').unwrap_or(s);
    let s = s.strip_prefix('_').unwrap_or(s);
    if s.chars().all(|c| c.is_ascii_hexdigit()) {
        s.to_lowercase()
    } else {
        label.to_lowercase()
    }
}

fn get_first_label_from_item(item: &CBlockItem) -> Option<String> {
    match item {
        CBlockItem::Stmt(stmt) => get_first_label_from_stmt(stmt),
        _ => None,
    }
}

fn get_first_label_from_stmt(stmt: &CStmt) -> Option<String> {
    match stmt {
        CStmt::Labeled(Label::Named(name), _) => Some(name.clone()),
        CStmt::Block(items) if !items.is_empty() => get_first_label_from_item(&items[0]),
        CStmt::Sequence(stmts) if !stmts.is_empty() => get_first_label_from_stmt(&stmts[0]),
        _ => None,
    }
}

fn negate_condition(cond: &CExpr) -> CExpr {
    match cond {
        CExpr::Unary(UnaryOp::Not, inner) => (**inner).clone(),
        CExpr::Binary(BinaryOp::Eq, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Ne, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Ne, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Eq, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Lt, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Ge, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Ge, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Lt, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Gt, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Le, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Le, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Gt, lhs.clone(), rhs.clone())
        }
        other => CExpr::Unary(UnaryOp::Not, Box::new(other.clone())),
    }
}


fn simplify_xor_self_in_expr(expr: &mut CExpr) {
    match expr {
        CExpr::Binary(_, lhs, rhs) => {
            simplify_xor_self_in_expr(lhs);
            simplify_xor_self_in_expr(rhs);
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) => simplify_xor_self_in_expr(inner),
        CExpr::Assign(_, lhs, rhs) => {
            simplify_xor_self_in_expr(lhs);
            simplify_xor_self_in_expr(rhs);
        }
        CExpr::Index(arr, idx) => {
            simplify_xor_self_in_expr(arr);
            simplify_xor_self_in_expr(idx);
        }
        CExpr::Ternary(c, t, e) => {
            simplify_xor_self_in_expr(c);
            simplify_xor_self_in_expr(t);
            simplify_xor_self_in_expr(e);
        }
        CExpr::Call(func, args) => {
            simplify_xor_self_in_expr(func);
            for arg in args {
                simplify_xor_self_in_expr(arg);
            }
        }
        _ => {}
    }
    if let CExpr::Binary(BinaryOp::BitXor, lhs, rhs) = expr {
        if lhs == rhs {
            *expr = CExpr::IntLit(IntLiteral {
                value: 0,
                suffix: IntLiteralSuffix::None,
                base: IntLiteralBase::Decimal,
            });
        }
    }
}

fn simplify_xor_self_in_stmt(stmt: &mut CStmt) {
    match stmt {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => simplify_xor_self_in_expr(e),
        CStmt::If(cond, then_s, else_s) => {
            simplify_xor_self_in_expr(cond);
            simplify_xor_self_in_stmt(then_s);
            if let Some(e) = else_s {
                simplify_xor_self_in_stmt(e);
            }
        }
        CStmt::While(cond, body) => {
            simplify_xor_self_in_expr(cond);
            simplify_xor_self_in_stmt(body);
        }
        CStmt::DoWhile(body, cond) => {
            simplify_xor_self_in_stmt(body);
            simplify_xor_self_in_expr(cond);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(crate::decompile::passes::c_pass::types::ForInit::Expr(e)) = init {
                simplify_xor_self_in_expr(e);
            }
            if let Some(c) = cond {
                simplify_xor_self_in_expr(c);
            }
            if let Some(u) = update {
                simplify_xor_self_in_expr(u);
            }
            simplify_xor_self_in_stmt(body);
        }
        CStmt::Switch(e, body) => {
            simplify_xor_self_in_expr(e);
            simplify_xor_self_in_stmt(body);
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    simplify_xor_self_in_stmt(s);
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                simplify_xor_self_in_stmt(s);
            }
        }
        CStmt::Labeled(_, inner) => simplify_xor_self_in_stmt(inner),
        _ => {}
    }
}


fn strip_dead_expr_stmts(stmt: &mut CStmt) {
    if let CStmt::Expr(e) = &*stmt {
        if !e.has_side_effects() {
            *stmt = CStmt::Empty;
            return;
        }
    }

    match stmt {
        CStmt::Block(items) => {
            for item in items.iter_mut() {
                if let CBlockItem::Stmt(s) = item {
                    strip_dead_expr_stmts(s);
                }
            }
            items.retain(|item| match item {
                CBlockItem::Stmt(s) => !matches!(s, CStmt::Empty),
                _ => true,
            });
        }
        CStmt::Sequence(stmts) => {
            for s in stmts.iter_mut() {
                strip_dead_expr_stmts(s);
            }
            stmts.retain(|s| !matches!(s, CStmt::Empty));
        }
        CStmt::If(_, then_s, else_s) => {
            strip_dead_expr_stmts(then_s);
            if let Some(e) = else_s {
                strip_dead_expr_stmts(e);
            }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) => strip_dead_expr_stmts(body),
        CStmt::For(_, _, _, body) => strip_dead_expr_stmts(body),
        CStmt::Switch(_, body) => strip_dead_expr_stmts(body),
        CStmt::Labeled(_, inner) => strip_dead_expr_stmts(inner),
        _ => {}
    }
}

pub(crate) fn is_dead_expr_stmt(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Empty => true,
        CStmt::Expr(e) => !e.has_side_effects(),
        CStmt::Block(items) => items.iter().all(|item| match item {
            CBlockItem::Stmt(s) => is_dead_expr_stmt(s),
            CBlockItem::Decl(decls) => decls.is_empty(),
        }),
        CStmt::Sequence(stmts) => stmts.iter().all(is_dead_expr_stmt),
        _ => false,
    }
}

fn recover_func_names_from_assert(db: &DecompileDB) -> HashMap<u64, String> {
    use crate::x86::types::ClightStmt;

    let mut result: HashMap<u64, String> = HashMap::new();

    let mut string_addr_to_content: HashMap<usize, String> = HashMap::new();
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        let hex_str = label.trim_start_matches(".L_").trim_start_matches("L_");
        if let Ok(addr) = u64::from_str_radix(hex_str, 16) {
            string_addr_to_content.insert(addr as usize, content.clone());
        }
    }

    let mut assert_fail_addrs: HashSet<u64> = HashSet::new();
    for (addr, name) in db.rel_iter::<(Address, Symbol)>("plt_entry") {
        if *name == "__assert_fail" {
            assert_fail_addrs.insert(*addr);
        }
    }
    let mut assert_fail_idents: HashSet<usize> = HashSet::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        if name.contains("__assert_fail") || name.contains("assert_fail") {
            assert_fail_idents.insert(*id);
            assert_fail_addrs.insert(*id as u64);
        }
    }

    if assert_fail_addrs.is_empty() && assert_fail_idents.is_empty() {
        return result;
    }

    let mut func_stmts: HashMap<u64, Vec<&ClightStmt>> = HashMap::new();
    for (func_addr, _node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        func_stmts.entry(*func_addr).or_default().push(stmt);
    }

    for (func_addr, stmts) in &func_stmts {
        let mut reg_to_addr: HashMap<usize, usize> = HashMap::new();
        for stmt in stmts {
            collect_sset_addr_defs(stmt, &mut reg_to_addr);
        }

        for stmt in stmts {
            if let Some(name) = extract_assert_func_name(
                stmt,
                &assert_fail_addrs,
                &assert_fail_idents,
                &reg_to_addr,
                &string_addr_to_content,
            ) {
                if is_valid_c_identifier(&name) {
                    result.entry(*func_addr).or_insert(name);
                }
            }
        }
    }

    if !result.is_empty() {
        log::info!(
            "Recovered {} function names from __assert_fail calls",
            result.len()
        );
    }
    result
}

fn collect_sset_addr_defs(
    stmt: &crate::x86::types::ClightStmt,
    reg_to_addr: &mut HashMap<usize, usize>,
) {
    use crate::x86::types::ClightStmt;
    match stmt {
        ClightStmt::Sset(reg, expr) => {
            if let Some(addr) = extract_addrof_ident(expr) {
                reg_to_addr.insert(*reg, addr);
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                collect_sset_addr_defs(s, reg_to_addr);
            }
        }
        _ => {}
    }
}

fn extract_addrof_ident(expr: &crate::x86::types::ClightExpr) -> Option<usize> {
    use crate::x86::types::ClightExpr;
    match expr {
        ClightExpr::Eaddrof(inner, _) => match inner.as_ref() {
            ClightExpr::Evar(ident, _) => Some(*ident),
            _ => None,
        },
        ClightExpr::Ecast(inner, _) => extract_addrof_ident(inner),
        _ => None,
    }
}

fn extract_assert_func_name(
    stmt: &crate::x86::types::ClightStmt,
    assert_addrs: &HashSet<u64>,
    assert_idents: &HashSet<usize>,
    reg_to_addr: &HashMap<usize, usize>,
    string_map: &HashMap<usize, String>,
) -> Option<String> {
    use crate::x86::types::*;

    match stmt {
        ClightStmt::Scall(_, callee, args) if args.len() >= 4 => {
            let is_assert = match callee {
                ClightExpr::Evar(ident, _) => {
                    assert_addrs.contains(&(*ident as u64)) || assert_idents.contains(ident)
                }
                ClightExpr::EvarSymbol(name, _) => name.contains("assert_fail"),
                _ => false,
            };
            if !is_assert {
                return None;
            }

            let fourth_arg = &args[3];
            resolve_string_from_expr(fourth_arg, reg_to_addr, string_map)
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                if let Some(name) = extract_assert_func_name(
                    s,
                    assert_addrs,
                    assert_idents,
                    reg_to_addr,
                    string_map,
                ) {
                    return Some(name);
                }
            }
            None
        }
        _ => None,
    }
}

fn resolve_string_from_expr(
    expr: &crate::x86::types::ClightExpr,
    reg_to_addr: &HashMap<usize, usize>,
    string_map: &HashMap<usize, String>,
) -> Option<String> {
    use crate::x86::types::ClightExpr;
    match expr {
        ClightExpr::Eaddrof(inner, _) => {
            if let ClightExpr::Evar(ident, _) = inner.as_ref() {
                return string_map.get(ident).cloned();
            }
            None
        }
        ClightExpr::Etempvar(reg, _) => {
            if let Some(addr) = reg_to_addr.get(reg) {
                return string_map.get(addr).cloned();
            }
            None
        }
        ClightExpr::Ecast(inner, _) => resolve_string_from_expr(inner, reg_to_addr, string_map),
        _ => None,
    }
}

pub(crate) fn is_valid_c_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let first = s.chars().next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }
    s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn strip_dead_labels_in_block(items: &mut Vec<CBlockItem>) {
    use crate::decompile::passes::c_pass::helpers::{collect_goto_targets, collect_all_labels, strip_dead_labels};

    let mut goto_targets: HashSet<String> = HashSet::new();
    let mut all_labels: HashSet<String> = HashSet::new();
    for item in items.iter() {
        if let CBlockItem::Stmt(s) = item {
            for target in collect_goto_targets(s) {
                goto_targets.insert(target);
            }
            for label in collect_all_labels(s) {
                all_labels.insert(label);
            }
        }
    }

    let dead_labels: HashSet<String> = all_labels.difference(&goto_targets).cloned().collect();
    if dead_labels.is_empty() {
        return;
    }

    for item in items.iter_mut() {
        if let CBlockItem::Stmt(s) = item {
            *s = strip_dead_labels(s, &dead_labels);
        }
    }
}

fn count_leaf_stmts_in_block(items: &[CBlockItem]) -> usize {
    items.iter().map(|item| match item {
        CBlockItem::Stmt(s) => count_leaf_stmts(s),
        CBlockItem::Decl(_) => 1,
    }).sum()
}

fn count_leaf_stmts(stmt: &CStmt) -> usize {
    match stmt {
        CStmt::Sequence(stmts) => stmts.iter().map(count_leaf_stmts).sum(),
        CStmt::Block(items) => count_leaf_stmts_in_block(items),
        CStmt::If(_, then_s, else_s) => {
            count_leaf_stmts(then_s) + else_s.as_ref().map_or(0, |e| count_leaf_stmts(e))
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) => {
            count_leaf_stmts(body)
        }
        CStmt::Switch(_, body) => count_leaf_stmts(body),
        CStmt::Labeled(_, inner) => count_leaf_stmts(inner),
        CStmt::Empty => 0,
        _ => 1,
    }
}

fn is_generated_label(name: &str) -> bool {
    if name.chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    if name.starts_with('L') && name[1..].chars().all(|c| c.is_ascii_digit()) {
        return !name[1..].is_empty();
    }
    if name.starts_with("L_") && name[2..].chars().all(|c| c.is_ascii_hexdigit()) {
        return !name[2..].is_empty();
    }
    if name.starts_with("FUN_") && name[4..].chars().all(|c| c.is_ascii_hexdigit()) {
        return !name[4..].is_empty();
    }
    false
}

fn rewrite_tailcall_gotos(body_items: &mut Vec<CBlockItem>, func_names: &HashMap<String, usize>, current_func: &str) {
    for item in body_items.iter_mut() {
        if let CBlockItem::Stmt(stmt) = item {
            rewrite_tailcall_gotos_in_stmt(stmt, func_names, current_func);
        }
    }
}

fn rewrite_tailcall_gotos_in_stmt(stmt: &mut CStmt, func_names: &HashMap<String, usize>, current_func: &str) {
    match stmt {
        CStmt::Goto(target) if func_names.contains_key(target.as_str())
            && target != current_func
            && func_names.get(target.as_str()) == Some(&0) => {
            *stmt = CStmt::Sequence(vec![
                CStmt::Expr(CExpr::call(CExpr::var(target.clone()), vec![])),
                CStmt::Return(None),
            ]);
        }
        CStmt::If(_, then_s, else_s) => {
            rewrite_tailcall_gotos_in_stmt(then_s, func_names, current_func);
            if let Some(e) = else_s {
                rewrite_tailcall_gotos_in_stmt(e, func_names, current_func);
            }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) => {
            rewrite_tailcall_gotos_in_stmt(body, func_names, current_func);
        }
        CStmt::Switch(_, body) => rewrite_tailcall_gotos_in_stmt(body, func_names, current_func),
        CStmt::Sequence(stmts) => {
            for s in stmts.iter_mut() {
                rewrite_tailcall_gotos_in_stmt(s, func_names, current_func);
            }
        }
        CStmt::Block(items) => {
            for item in items.iter_mut() {
                if let CBlockItem::Stmt(s) = item {
                    rewrite_tailcall_gotos_in_stmt(s, func_names, current_func);
                }
            }
        }
        CStmt::Labeled(_, inner) => rewrite_tailcall_gotos_in_stmt(inner, func_names, current_func),
        _ => {}
    }
}

/// Collect all function names called in a statement tree.
fn collect_called_names_in_stmt(stmt: &CStmt, names: &mut HashSet<String>) {
    match stmt {
        CStmt::Expr(expr) => collect_called_names_in_expr(expr, names),
        CStmt::Return(Some(expr)) => collect_called_names_in_expr(expr, names),
        CStmt::If(cond, then_s, else_s) => {
            collect_called_names_in_expr(cond, names);
            collect_called_names_in_stmt(then_s, names);
            if let Some(e) = else_s { collect_called_names_in_stmt(e, names); }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_called_names_in_expr(cond, names);
            collect_called_names_in_stmt(body, names);
        }
        CStmt::For(_, cond, update, body) => {
            if let Some(c) = cond { collect_called_names_in_expr(c, names); }
            if let Some(u) = update { collect_called_names_in_expr(u, names); }
            collect_called_names_in_stmt(body, names);
        }
        CStmt::Switch(expr, body) => {
            collect_called_names_in_expr(expr, names);
            collect_called_names_in_stmt(body, names);
        }
        CStmt::Sequence(stmts) => { for s in stmts { collect_called_names_in_stmt(s, names); } }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item { collect_called_names_in_stmt(s, names); }
            }
        }
        CStmt::Labeled(_, inner) => collect_called_names_in_stmt(inner, names),
        _ => {}
    }
}

fn collect_called_names_in_expr(expr: &CExpr, names: &mut HashSet<String>) {
    match expr {
        CExpr::Call(callee, args) => {
            if let CExpr::Var(name) = callee.as_ref() {
                names.insert(name.clone());
            }
            collect_called_names_in_expr(callee, names);
            for arg in args { collect_called_names_in_expr(arg, names); }
        }
        CExpr::Assign(_, lhs, rhs) => {
            collect_called_names_in_expr(lhs, names);
            collect_called_names_in_expr(rhs, names);
        }
        CExpr::Binary(_, lhs, rhs) => {
            collect_called_names_in_expr(lhs, names);
            collect_called_names_in_expr(rhs, names);
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_called_names_in_expr(inner, names);
        }
        CExpr::Ternary(a, b, c) => {
            collect_called_names_in_expr(a, names);
            collect_called_names_in_expr(b, names);
            collect_called_names_in_expr(c, names);
        }
        _ => {}
    }
}

/// Infer a forward-declaration parameter type from a call-site argument expression, giving a called-but-not-emitted function (e.g. statically-linked gnulib helpers like version_etc, error) a usable prototype derived from how it is actually called instead of the bare `int f(void)` fallback that rejects every argument; casts (the common decompiler form) give the exact type, otherwise fall back to a width accepting both pointers and integers without truncation.
fn infer_arg_ctype(expr: &CExpr) -> CType {
    use crate::decompile::passes::c_pass::types::UnaryOp;
    match expr {
        CExpr::Cast(ty, _) => ty.clone(),
        CExpr::StringLit(_) => CType::ptr(CType::Void),
        CExpr::Unary(UnaryOp::AddrOf, _) => CType::ptr(CType::Void),
        _ => CType::long(),
    }
}

/// Collect, per called function name, the argument types of its highest-arity call site (so a variadic callee gets a prototype covering all observed arguments); mirrors the traversal of collect_called_names_in_stmt.
fn collect_call_sigs_in_stmt(stmt: &CStmt, sigs: &mut HashMap<String, Vec<CType>>) {
    match stmt {
        CStmt::Expr(expr) => collect_call_sigs_in_expr(expr, sigs),
        CStmt::Return(Some(expr)) => collect_call_sigs_in_expr(expr, sigs),
        CStmt::If(cond, then_s, else_s) => {
            collect_call_sigs_in_expr(cond, sigs);
            collect_call_sigs_in_stmt(then_s, sigs);
            if let Some(e) = else_s { collect_call_sigs_in_stmt(e, sigs); }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_call_sigs_in_expr(cond, sigs);
            collect_call_sigs_in_stmt(body, sigs);
        }
        CStmt::For(_, cond, update, body) => {
            if let Some(c) = cond { collect_call_sigs_in_expr(c, sigs); }
            if let Some(u) = update { collect_call_sigs_in_expr(u, sigs); }
            collect_call_sigs_in_stmt(body, sigs);
        }
        CStmt::Switch(expr, body) => {
            collect_call_sigs_in_expr(expr, sigs);
            collect_call_sigs_in_stmt(body, sigs);
        }
        CStmt::Sequence(stmts) => { for s in stmts { collect_call_sigs_in_stmt(s, sigs); } }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item { collect_call_sigs_in_stmt(s, sigs); }
            }
        }
        CStmt::Labeled(_, inner) => collect_call_sigs_in_stmt(inner, sigs),
        _ => {}
    }
}

fn collect_call_sigs_in_expr(expr: &CExpr, sigs: &mut HashMap<String, Vec<CType>>) {
    match expr {
        CExpr::Call(callee, args) => {
            if let CExpr::Var(name) = callee.as_ref() {
                let keep = sigs.get(name).map_or(true, |existing| args.len() > existing.len());
                if keep {
                    sigs.insert(name.clone(), args.iter().map(infer_arg_ctype).collect());
                }
            }
            collect_call_sigs_in_expr(callee, sigs);
            for arg in args { collect_call_sigs_in_expr(arg, sigs); }
        }
        CExpr::Assign(_, lhs, rhs) | CExpr::Binary(_, lhs, rhs) => {
            collect_call_sigs_in_expr(lhs, sigs);
            collect_call_sigs_in_expr(rhs, sigs);
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_call_sigs_in_expr(inner, sigs);
        }
        CExpr::Ternary(a, b, c) => {
            collect_call_sigs_in_expr(a, sigs);
            collect_call_sigs_in_expr(b, sigs);
            collect_call_sigs_in_expr(c, sigs);
        }
        _ => {}
    }
}

/// Rename duplicate labels within a function body so each is unique: first occurrence keeps its name, subsequent get `_2`, `_3`, etc.
fn deduplicate_labels(body_items: &mut Vec<CBlockItem>) {
    // Pass 1: collect all label occurrences in order
    let mut label_counts: HashMap<String, usize> = HashMap::new();
    let mut rename_map: HashMap<(String, usize), String> = HashMap::new();

    for item in body_items.iter() {
        if let CBlockItem::Stmt(stmt) = item {
            count_labels_in_stmt(stmt, &mut label_counts, &mut rename_map);
        }
    }

    // Only proceed if there are duplicates
    if rename_map.is_empty() {
        return;
    }

    // Build a positional rename map: track label occurrences and rename duplicates
    let mut occurrence: HashMap<String, usize> = HashMap::new();
    for item in body_items.iter_mut() {
        if let CBlockItem::Stmt(stmt) = item {
            *stmt = rename_duplicate_labels_in_stmt(stmt, &rename_map, &mut occurrence);
        }
    }
}

fn count_labels_in_stmt(
    stmt: &CStmt,
    counts: &mut HashMap<String, usize>,
    rename_map: &mut HashMap<(String, usize), String>,
) {
    match stmt {
        CStmt::Labeled(Label::Named(name), inner) => {
            let occ = counts.entry(name.clone()).or_insert(0);
            *occ += 1;
            if *occ > 1 {
                rename_map.insert((name.clone(), *occ), format!("{}_{}", name, occ));
            }
            count_labels_in_stmt(inner, counts, rename_map);
        }
        CStmt::If(_, then_s, else_s) => {
            count_labels_in_stmt(then_s, counts, rename_map);
            if let Some(e) = else_s { count_labels_in_stmt(e, counts, rename_map); }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) | CStmt::Switch(_, body) => {
            count_labels_in_stmt(body, counts, rename_map);
        }
        CStmt::Sequence(stmts) => {
            for s in stmts { count_labels_in_stmt(s, counts, rename_map); }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item { count_labels_in_stmt(s, counts, rename_map); }
            }
        }
        _ => {}
    }
}

fn rename_duplicate_labels_in_stmt(
    stmt: &CStmt,
    rename_map: &HashMap<(String, usize), String>,
    occurrence: &mut HashMap<String, usize>,
) -> CStmt {
    match stmt {
        CStmt::Labeled(Label::Named(name), inner) => {
            let occ = occurrence.entry(name.clone()).or_insert(0);
            *occ += 1;
            let new_name = if *occ > 1 {
                rename_map.get(&(name.clone(), *occ))
                    .cloned()
                    .unwrap_or_else(|| name.clone())
            } else {
                name.clone()
            };
            let inner = rename_duplicate_labels_in_stmt(inner, rename_map, occurrence);
            CStmt::Labeled(Label::Named(new_name), Box::new(inner))
        }
        CStmt::Goto(target) => {
            // Gotos to duplicate labels redirect to the first occurrence (only duplicates are renamed)
            CStmt::Goto(target.clone())
        }
        CStmt::If(cond, then_s, else_s) => {
            let then_s = Box::new(rename_duplicate_labels_in_stmt(then_s, rename_map, occurrence));
            let else_s = else_s.as_ref().map(|e| Box::new(rename_duplicate_labels_in_stmt(e, rename_map, occurrence)));
            CStmt::If(cond.clone(), then_s, else_s)
        }
        CStmt::While(cond, body) => CStmt::While(cond.clone(), Box::new(rename_duplicate_labels_in_stmt(body, rename_map, occurrence))),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(Box::new(rename_duplicate_labels_in_stmt(body, rename_map, occurrence)), cond.clone()),
        CStmt::For(i, c, u, body) => CStmt::For(i.clone(), c.clone(), u.clone(), Box::new(rename_duplicate_labels_in_stmt(body, rename_map, occurrence))),
        CStmt::Switch(expr, body) => CStmt::Switch(expr.clone(), Box::new(rename_duplicate_labels_in_stmt(body, rename_map, occurrence))),
        CStmt::Sequence(stmts) => CStmt::Sequence(stmts.iter().map(|s| rename_duplicate_labels_in_stmt(s, rename_map, occurrence)).collect()),
        CStmt::Block(items) => CStmt::Block(items.iter().map(|item| match item {
            CBlockItem::Stmt(s) => CBlockItem::Stmt(rename_duplicate_labels_in_stmt(s, rename_map, occurrence)),
            other => other.clone(),
        }).collect()),
        CStmt::Labeled(label, inner) => CStmt::Labeled(label.clone(), Box::new(rename_duplicate_labels_in_stmt(inner, rename_map, occurrence))),
        _ => stmt.clone(),
    }
}

fn ensure_goto_label_consistency(body_items: &mut Vec<CBlockItem>) {
    let mut goto_targets: HashSet<String> = HashSet::new();
    let mut label_defs: HashSet<String> = HashSet::new();

    for item in body_items.iter() {
        if let CBlockItem::Stmt(stmt) = item {
            for target in crate::decompile::passes::c_pass::helpers::collect_goto_targets(stmt) {
                goto_targets.insert(target);
            }
            for label in crate::decompile::passes::c_pass::helpers::collect_all_labels(stmt) {
                label_defs.insert(label);
            }
        }
    }

    let missing_targets: HashSet<String> = goto_targets.difference(&label_defs).cloned().collect();
    if !missing_targets.is_empty() {
        for item in body_items.iter_mut() {
            if let CBlockItem::Stmt(stmt) = item {
                *stmt = remove_gotos_to_missing_labels(stmt, &missing_targets);
            }
        }
    }
}

fn remove_gotos_to_missing_labels(stmt: &CStmt, missing: &HashSet<String>) -> CStmt {
    match stmt {
        CStmt::Goto(target) if missing.contains(target) => CStmt::Empty,
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            cond.clone(),
            Box::new(remove_gotos_to_missing_labels(then_s, missing)),
            else_s.as_ref().map(|e| Box::new(remove_gotos_to_missing_labels(e, missing))),
        ),
        CStmt::While(cond, body) => CStmt::While(
            cond.clone(),
            Box::new(remove_gotos_to_missing_labels(body, missing)),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(remove_gotos_to_missing_labels(body, missing)),
            cond.clone(),
        ),
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            update.clone(),
            Box::new(remove_gotos_to_missing_labels(body, missing)),
        ),
        CStmt::Switch(expr, body) => CStmt::Switch(
            expr.clone(),
            Box::new(remove_gotos_to_missing_labels(body, missing)),
        ),
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts.iter().map(|s| remove_gotos_to_missing_labels(s, missing)).collect(),
        ),
        CStmt::Block(items) => CStmt::Block(
            items.iter().map(|item| match item {
                CBlockItem::Stmt(s) => CBlockItem::Stmt(remove_gotos_to_missing_labels(s, missing)),
                other => other.clone(),
            }).collect(),
        ),
        CStmt::Labeled(l, inner) => CStmt::Labeled(
            l.clone(),
            Box::new(remove_gotos_to_missing_labels(inner, missing)),
        ),
        other => other.clone(),
    }
}

// Return-value forwarding: when `if (...) { var = val; } else { var = val2; } return var;` transform to `if (...) { return val; } else { return val2; }`
fn forward_return_value(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Block(items) => {
            let new_items = forward_return_in_block_items(items);
            CStmt::Block(new_items)
        }
        CStmt::Sequence(stmts) => {
            let items: Vec<CBlockItem> = stmts.iter().map(|s| CBlockItem::Stmt(s.clone())).collect();
            let new_items = forward_return_in_block_items(&items);
            let new_stmts: Vec<CStmt> = new_items.into_iter().filter_map(|i| match i {
                CBlockItem::Stmt(s) => Some(s),
                _ => None,
            }).collect();
            if new_stmts.len() == 1 {
                new_stmts.into_iter().next().unwrap()
            } else {
                CStmt::Sequence(new_stmts)
            }
        }
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            cond.clone(),
            Box::new(forward_return_value(then_s)),
            else_s.as_ref().map(|s| Box::new(forward_return_value(s))),
        ),
        CStmt::While(cond, body) => CStmt::While(cond.clone(), Box::new(forward_return_value(body))),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(Box::new(forward_return_value(body)), cond.clone()),
        CStmt::For(init, cond, upd, body) => CStmt::For(init.clone(), cond.clone(), upd.clone(), Box::new(forward_return_value(body))),
        CStmt::Labeled(l, inner) => CStmt::Labeled(l.clone(), Box::new(forward_return_value(inner))),
        _ => stmt.clone(),
    }
}

fn forward_return_in_block_items(items: &[CBlockItem]) -> Vec<CBlockItem> {
    let mut result = items.to_vec();
    // Look for: ..., If(cond, then, else), Return(var) where If assigns var in every branch
    let mut i = 0;
    while i + 1 < result.len() {
        let var_match = match (&result[i], &result[i + 1]) {
            (CBlockItem::Stmt(if_stmt @ CStmt::If(_, _, Some(_))),
             CBlockItem::Stmt(CStmt::Return(Some(CExpr::Var(ret_var))))) => {
                if all_branches_assign_last(if_stmt, ret_var) {
                    Some(ret_var.clone())
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(var_name) = var_match {
            if let CBlockItem::Stmt(if_stmt) = &result[i] {
                let transformed = replace_last_assign_with_return(if_stmt, &var_name);
                result[i] = CBlockItem::Stmt(forward_return_value(&transformed));
                result.remove(i + 1);
                continue;
            }
        }
        i += 1;
    }
    for item in &mut result {
        if let CBlockItem::Stmt(s) = item {
            *s = forward_return_value(s);
        }
    }
    result
}

// Check if every branch of the if-else tree assigns to `var` as its last effective statement
fn all_branches_assign_last(stmt: &CStmt, var: &str) -> bool {
    match stmt {
        CStmt::If(_, then_s, Some(else_s)) => {
            last_stmt_assigns(then_s, var) && last_stmt_assigns(else_s, var)
        }
        _ => false,
    }
}

fn last_stmt_assigns(stmt: &CStmt, var: &str) -> bool {
    match stmt {
        CStmt::Expr(CExpr::Assign(AssignOp::Assign, lhs, _)) => {
            matches!(lhs.as_ref(), CExpr::Var(v) if v == var)
        }
        CStmt::If(_, _, Some(_)) => all_branches_assign_last(stmt, var),
        CStmt::Block(items) => {
            items.iter().rev().find_map(|i| match i {
                CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty) => Some(s),
                _ => None,
            }).map_or(false, |s| last_stmt_assigns(s, var))
        }
        CStmt::Sequence(stmts) => {
            stmts.last().map_or(false, |s| last_stmt_assigns(s, var))
        }
        _ => false,
    }
}

// Replace the last `var = val` in each branch with `return val`
fn replace_last_assign_with_return(stmt: &CStmt, var: &str) -> CStmt {
    match stmt {
        CStmt::If(cond, then_s, Some(else_s)) => CStmt::If(
            cond.clone(),
            Box::new(replace_last_assign_with_return(then_s, var)),
            Some(Box::new(replace_last_assign_with_return(else_s, var))),
        ),
        CStmt::Expr(CExpr::Assign(AssignOp::Assign, lhs, rhs)) if matches!(lhs.as_ref(), CExpr::Var(v) if v == var) => {
            CStmt::Return(Some(*rhs.clone()))
        }
        CStmt::Block(items) => {
            let mut new_items = items.clone();
            if let Some(last_stmt_idx) = new_items.iter().rposition(|i| matches!(i, CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty))) {
                if let CBlockItem::Stmt(s) = &new_items[last_stmt_idx] {
                    new_items[last_stmt_idx] = CBlockItem::Stmt(replace_last_assign_with_return(s, var));
                }
            }
            CStmt::Block(new_items)
        }
        CStmt::Sequence(stmts) => {
            let mut new_stmts = stmts.clone();
            if let Some(last) = new_stmts.last_mut() {
                *last = replace_last_assign_with_return(last, var);
            }
            CStmt::Sequence(new_stmts)
        }
        other => other.clone(),
    }
}
