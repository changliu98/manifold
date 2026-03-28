
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::c_pass::helpers::{
    build_string_literal_map, collect_goto_label_targets, convert_param_type_from_param,
    extract_named_label, inline_rodata_constants, inline_string_literals, is_terminal_cstmt,
    param_name_for_reg, xtype_string_to_ctype,
};
use crate::decompile::passes::c_pass::types::{
    CExpr, CStmt, CType, FloatLiteral, FloatLiteralSuffix, IntLiteral, IntLiteralBase, IntLiteralSuffix,
};
use crate::x86::types::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub struct ClightEmitPass;

impl IRPass for ClightEmitPass {
    fn name(&self) -> &'static str {
        "ClightEmit"
    }

    fn run(&self, db: &mut DecompileDB) {
        let binary_path = db
            .binary_path
            .clone()
            .expect("binary_path must be set before ClightEmitPass");

        let selected_functions = match crate::decompile::passes::clight_select::select::select_clight_stmts(db) {
            Ok(funcs) => funcs,
            Err(e) => {
                log::warn!("ClightEmitPass: failed to select statements: {}", e);
                return;
            }
        };

        let mut id_to_name: HashMap<usize, String> = HashMap::new();
        for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            let name_str = name.to_string();
            id_to_name
                .entry(*id)
                .and_modify(|existing| {
                    if name.len() < existing.len() {
                        *existing = name_str.clone();
                    }
                })
                .or_insert_with(|| name_str);
        }
        for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
            let id = *addr as usize;
            id_to_name.entry(id).or_insert_with(|| name.to_string());
        }
        for func in &selected_functions {
            id_to_name
                .entry(func.address as usize)
                .or_insert_with(|| func.name.clone());
        }

        let globals = match crate::decompile::passes::clight_select::query::extract_globals(db, &binary_path) {
            Ok(g) => g,
            Err(e) => {
                log::warn!("ClightEmitPass: failed to extract globals: {}", e);
                return;
            }
        };
        for g in &globals {
            id_to_name.entry(g.id).or_insert_with(|| g.name.clone());
        }

        // Resolve auto-generated L_XXXX labels by merging fragmented func_stacksz ranges back into their containing function.
        {
            let is_generated_label = |n: &str| -> bool {
                n.strip_prefix("L_")
                    .map_or(false, |h| !h.is_empty() && h.chars().all(|c| c.is_ascii_hexdigit()))
            };

            let mut raw: Vec<(u64, u64, String)> = db
                .rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
                .map(|(s, e, n, _)| (*s, *e, n.to_string()))
                .collect();
            raw.sort_by_key(|(s, _, _)| *s);

            // Merge: absorb consecutive L_XXXX entries into the preceding real function
            let mut func_ranges: Vec<(u64, u64, String)> = Vec::new();
            for (start, end, name) in raw {
                if is_generated_label(&name) {
                    // Extend the previous real function's end to cover this fragment
                    if let Some(last) = func_ranges.last_mut() {
                        if start == last.1 {
                            last.1 = end;
                            continue;
                        }
                    }
                }
                func_ranges.push((start, end, name));
            }

            for (_id, name) in id_to_name.iter_mut() {
                if !is_generated_label(name) {
                    continue;
                }
                let addr = match u64::from_str_radix(&name[2..], 16) {
                    Ok(a) => a,
                    Err(_) => continue,
                };
                let idx = match func_ranges.binary_search_by_key(&addr, |(s, _, _)| *s) {
                    Ok(i) => i,
                    Err(i) => i,
                };
                if idx > 0 {
                    let (start, end, func_name) = &func_ranges[idx - 1];
                    if addr >= *start && addr < *end {
                        *name = func_name.clone();
                    }
                }
            }
        }

        {
            let interior_elem_sizes: HashMap<usize, usize> = db
                .rel_iter::<(Ident, usize)>("interior_element_size")
                .map(|(ident, elem_size)| (*ident, *elem_size))
                .collect();
            let array_elem_sizes: HashMap<usize, usize> = db
                .rel_iter::<(Ident, usize, usize)>("is_global_array")
                .map(|(ident, elem_size, _count)| (*ident, *elem_size))
                .collect();
            for (interior_ident, base_name, offset) in db.rel_iter::<(Ident, Symbol, i64)>("emit_address_as_offset") {
                let maybe_base_ident = db
                    .rel_iter::<(Address, usize, Symbol)>("symbol_size")
                    .find(|(_, _, name)| *name == *base_name)
                    .map(|(addr, _, _)| *addr as usize);

                let rewritten_name = if let Some(base_ident) = maybe_base_ident {
                    let elem_size_opt = interior_elem_sizes
                        .get(&base_ident)
                        .or_else(|| array_elem_sizes.get(&base_ident));
                    if let Some(&elem_size) = elem_size_opt {
                        if elem_size > 0 && *offset >= 0 && (*offset as usize) % elem_size == 0 {
                            let index = (*offset as usize) / elem_size;
                            format!("{}[{}]", base_name, index)
                        } else {
                            format!("({} + {})", base_name, offset)
                        }
                    } else if *offset == 0 {
                        base_name.to_string()
                    } else {
                        format!("({} + {})", base_name, offset)
                    }
                } else {
                    format!("({} + {})", base_name, offset)
                };
                id_to_name.insert(*interior_ident, rewritten_name);
            }
        }

        let edges: Vec<(Node, Node)> = db
            .rel_iter::<(Node, Node)>("clight_succ")
            .map(|(src, dst)| (*src, *dst))
            .collect();
        let raw_translation_unit = crate::decompile::passes::c_pass::convert::build_cast_from_relations(
            db,
            &selected_functions,
            &globals,
            &id_to_name,
            &edges,
        );

        let mut string_map = build_string_literal_map(db);
        for g in &globals {
            if g.is_string && !g.content.is_empty() {
                let s = String::from_utf8_lossy(&g.content)
                    .trim_end_matches('\0')
                    .to_string();
                string_map.entry(g.name.clone()).or_insert(s);
            }
        }

        // Build inline constant map from resolved .rodata scalar values
        let rodata_const_map: HashMap<String, CExpr> = globals
            .iter()
            .filter_map(|g| {
                use crate::decompile::passes::clight_select::query::ScalarConstant;
                let expr = match g.scalar_value.as_ref()? {
                    ScalarConstant::Float32(v) => CExpr::FloatLit(FloatLiteral {
                        value: *v as f64,
                        suffix: FloatLiteralSuffix::F,
                    }),
                    ScalarConstant::Float64(v) => CExpr::FloatLit(FloatLiteral {
                        value: *v,
                        suffix: FloatLiteralSuffix::None,
                    }),
                    ScalarConstant::Int32(v) => CExpr::IntLit(IntLiteral {
                        value: *v as i128,
                        suffix: IntLiteralSuffix::None,
                        base: IntLiteralBase::Decimal,
                    }),
                    ScalarConstant::Int64(v) => CExpr::IntLit(IntLiteral {
                        value: *v as i128,
                        suffix: IntLiteralSuffix::L,
                        base: IntLiteralBase::Decimal,
                    }),
                };
                Some((g.name.clone(), expr))
            })
            .collect();
        let struct_layouts = crate::decompile::passes::clight_select::query::extract_struct_layout_map(db);

        let external_funcs: HashSet<u64> =
            db.rel_iter::<(Address,)>("is_external_function").map(|(a,)| *a).collect();

        let internal_functions: Vec<_> = selected_functions
            .iter()
            .filter(|func| {
                !external_funcs.contains(&func.address)
                    && !func.name.starts_with('.')
                    && !db.should_skip_function(func.name.as_str())
            })
            .cloned()
            .collect();

        {
            let internal_addrs: HashSet<u64> =
                internal_functions.iter().map(|f| f.address).collect();
            let node_to_func: HashMap<u64, u64> = db
                .rel_iter::<(Node, Address)>("instr_in_function")
                .map(|(n, f)| (*n, *f))
                .collect();
            let called_addrs: HashSet<u64> = db
                .rel_iter::<(Address, Address)>("direct_call")
                .filter(|(caller, _)| {
                    node_to_func
                        .get(caller)
                        .map_or(false, |f| internal_addrs.contains(f))
                })
                .map(|(_, callee)| *callee)
                .collect();
            for func in &selected_functions {
                if db.should_skip_function(func.name.as_str())
                    && called_addrs.contains(&func.address)
                {
                    let has_sig = db
                        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
                        .any(|(n, ..)| *n == func.name.as_str());
                    if !has_sig {
                        db.rel_push("unknown_extern", (crate::util::leak::<String, str>(func.name.clone()),));
                    }
                }
            }
        }

        let mut ctx = crate::decompile::passes::c_pass::convert::from_relations::ConversionContext::new(
            id_to_name.clone(),
        );

        let mut var_types_for_emission: HashMap<String, CType> = HashMap::new();
        let mut all_statements: Vec<(Node, CStmt)> = Vec::new();
        let mut all_edges: Vec<(Node, Node)> = Vec::new();
        let mut node_to_func_addr: HashMap<Node, u64> = HashMap::new();

        for func in &internal_functions {
            let mut statements = Vec::new();
            let mut func_edges = Vec::new();

            for (reg, pty) in func.param_regs.iter().zip(func.param_types.iter()) {
                let name = param_name_for_reg(*reg);
                let ty = match pty {
                    crate::x86::types::ParamType::StructPointer(_)
                    | crate::x86::types::ParamType::Typed(_) => {
                        convert_param_type_from_param(pty)
                    }
                    _ => {
                        if let Some(type_str) = func.var_types.get(reg) {
                            xtype_string_to_ctype(type_str)
                        } else {
                            convert_param_type_from_param(pty)
                        }
                    }
                };
                var_types_for_emission.entry(name).or_insert(ty);
            }

            for (var_name, type_str) in &func.var_types {
                let ty = xtype_string_to_ctype(type_str);
                let name = format!("var_{}", var_name);
                var_types_for_emission.entry(name).or_insert(ty);
            }

            for (reg, struct_id) in &func.reg_struct_ids {
                let name = format!("var_{}", reg);
                let struct_type_name = format!("struct_{:x}", struct_id);
                let ptr_type = CType::Pointer(
                    Box::new(CType::Struct(struct_type_name)),
                    crate::decompile::passes::c_pass::types::TypeQualifiers::none(),
                );
                var_types_for_emission.insert(name, ptr_type);
            }

            for (node, clight_stmt) in &func.statements {
                let cstmt = crate::decompile::passes::c_pass::convert::from_relations::convert_stmt(
                    clight_stmt,
                    &mut ctx,
                );
                let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                    inline_string_literals(e, &string_map)
                });
                let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                    inline_rodata_constants(e, &rodata_const_map)
                });
                let cstmt = crate::decompile::passes::c_pass::convert::from_relations::narrow_varargs_in_stmt(&cstmt);
                statements.push((*node, cstmt));
            }

            for (node, succs) in &func.successors {
                for succ in succs {
                    func_edges.push((*node, *succ));
                }
            }
            {
                let label_to_node: HashMap<String, Node> = statements
                    .iter()
                    .filter_map(|(n, s)| extract_named_label(s).map(|name| (name, *n)))
                    .collect();
                let node_set: HashSet<Node> =
                    statements.iter().map(|(n, _)| *n).collect();
                let mut extra_edges = Vec::new();
                for (node, stmt) in &statements {
                    let mut targets = Vec::new();
                    collect_goto_label_targets(stmt, &mut targets);
                    for label in &targets {
                        if let Some(&target) = label_to_node.get(label.as_str()) {
                            if node_set.contains(&target) {
                                extra_edges.push((*node, target));
                            }
                        }
                    }
                }
                func_edges.extend(extra_edges);
            }

            {
                let mut sorted_nodes: Vec<Node> =
                    statements.iter().map(|(n, _)| *n).collect();
                sorted_nodes.sort();
                let has_outgoing: HashSet<Node> =
                    func_edges.iter().map(|(f, _)| *f).collect();
                let stmt_map: HashMap<Node, &CStmt> =
                    statements.iter().map(|(n, s)| (*n, s)).collect();
                let mut extra_edges = Vec::new();
                for window in sorted_nodes.windows(2) {
                    let curr = window[0];
                    let next_node = window[1];
                    if has_outgoing.contains(&curr) {
                        continue;
                    }
                    if let Some(stmt) = stmt_map.get(&curr) {
                        if !is_terminal_cstmt(stmt) {
                            extra_edges.push((curr, next_node));
                        }
                    }
                }
                func_edges.extend(extra_edges);
            }

            for (node, _) in &statements {
                node_to_func_addr.insert(*node, func.address);
            }

            // TODO: wire up CsharpminorStmt structuring pass in the pipeline.
            all_statements.extend(statements);
            all_edges.extend(func_edges);
        }

        db.cast_selected_functions = internal_functions;
        db.cast_globals = globals;
        db.cast_id_to_name = id_to_name;
        db.cast_struct_layouts = struct_layouts;
        db.cast_var_types_for_emission = var_types_for_emission.clone();
        db.cast_raw_translation_unit = Some(raw_translation_unit);

        let struct_defs = crate::decompile::passes::clight_select::query::extract_struct_definitions(db);
        let stmt_map: HashMap<Node, CStmt> = all_statements.into_iter().collect();

        log::info!(
            "Building translation unit from {} statements",
            stmt_map.len()
        );

        let mut tu = crate::decompile::passes::c_pass::convert::build_translation_unit_from_stmt_map_with_types(
            db,
            &db.cast_selected_functions,
            &db.cast_globals,
            &db.cast_id_to_name,
            &stmt_map,
            &all_edges,
            &db.cast_var_types_for_emission,
            &node_to_func_addr,
        );

        let mut struct_decls: Vec<crate::decompile::passes::c_pass::types::TopLevelDecl> = struct_defs
            .into_iter()
            .map(|extracted| crate::decompile::passes::c_pass::types::TopLevelDecl::StructDef(extracted.definition))
            .collect();
        struct_decls.append(&mut tu.decls);
        tu.decls = struct_decls;

        db.cast_optimized_translation_unit = Some(tu);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "emit_clight_stmt",
            "emit_function",
            "emit_function_param",
            "emit_function_return_type",
            "emit_next",
            "emit_var_type_candidate",
            "emit_loop_body",
            "emit_switch_chain",
            "emit_struct_fields",
            "emit_ifthenelse_body",
            "ifthenelse_merge_point",
            "primary_exit_node",
            "loop_exit_branch",
            "suppress_step",
            "known_extern_signature",
            "ident_to_symbol",
            "is_external_function",
            "clight_succ",
            "string_data",
            "instr_in_function",
            "emit_address_as_offset",
            "symbol_size",
            "interior_element_size",
            "is_global_array",
            "global_var_ref",
            "global_load_chunk",
            "emit_canonical_struct_id",
            "global_struct_catalog",
            "func_stacksz",
            "symbols",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "cast_selected_functions",
            "cast_globals",
            "cast_id_to_name",
            "cast_struct_layouts",
            "cast_var_types_for_emission",
            "cast_raw_translation_unit",
            "cast_optimized_translation_unit",
        ]
    }
}

