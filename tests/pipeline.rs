use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::LazyLock;

use manifold::decompile::passes::c_pass::types::*;

struct TestOutput {
    text: String,
    tu: TranslationUnit,
}

fn compile(name: &str, compiler: &str, src: &str, opt: &str) -> PathBuf {
    let mut h = DefaultHasher::new();
    (name, compiler, src, opt).hash(&mut h);
    let dir = std::env::temp_dir().join(format!("manifold_{name}_{compiler}_{:016x}", h.finish()));
    std::fs::create_dir_all(&dir).unwrap();

    let c_path = dir.join(format!("{name}.c"));
    std::fs::write(&c_path, src).unwrap();

    let bin = dir.join(name);
    let nopie: &[&str] = if compiler == "gcc" {
        &["-no-pie"]
    } else {
        &["-Wl,-no-pie"]
    };
    let st = Command::new(compiler)
        .args([opt, "-fno-pie", "-fno-stack-protector",
               "-o", bin.to_str().unwrap(), c_path.to_str().unwrap()])
        .args(nopie)
        .status().unwrap_or_else(|e| panic!("{compiler}: {e}"));
    assert!(st.success(), "{compiler} failed for '{name}'");
    bin
}

fn decompile(binary: &Path) -> TestOutput {
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(4).stack_size(64 * 1024 * 1024).build_global();

    let binary = binary.to_path_buf();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut db = manifold::decompile::elevator::DecompileDB::default();
            manifold::decompile::disassembly::load_from_binary(&mut db, &binary);
            manifold::decompile::disassembly::load_preset(&mut db);
            db.run_pipeline(&binary, false, false);
            let tu = db.cast_optimized_translation_unit
                .expect("pipeline must produce translation unit");
            let text = manifold::decompile::passes::c_pass::print_translation_unit(&tu);
            TestOutput { text, tu }
        })
        .unwrap().join().expect("pipeline panicked")
}

// Text-based helpers (kept for backward compatibility and textual checks)

fn body(out: &TestOutput, func: &str) -> String {
    body_from_text(&out.text, func)
}

fn body_from_text(source: &str, func: &str) -> String {
    let pat = format!("{func}(");
    let mut search_from = 0;
    let start = loop {
        let pos = source[search_from..].find(&pat)
            .map(|p| p + search_from)
            .unwrap_or_else(|| panic!("'{func}' not found in output"));
        let line_start = source[..pos].rfind('\n').map(|p| p + 1).unwrap_or(0);
        let prefix = &source[line_start..pos];
        if !prefix.starts_with(' ') && !prefix.starts_with('\t') && prefix.contains(' ') {
            break pos;
        }
        search_from = pos + 1;
    };
    let brace = source[start..].find('{').unwrap() + start;
    let mut depth = 0;
    let mut end = brace;
    for (i, ch) in source[brace..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => { depth -= 1; if depth == 0 { end = brace + i + 1; break; } }
            _ => {}
        }
    }
    source[brace..end].to_string()
}

#[allow(dead_code)]
fn has_loop(s: &str) -> bool {
    s.contains("while") || s.contains("for") || s.contains("do")
}

// AST query helpers

fn func_def<'a>(out: &'a TestOutput, name: &str) -> &'a FuncDef {
    let idx = out.tu.symbols.get(name)
        .unwrap_or_else(|| panic!("function '{}' not found in translation unit", name));
    match &out.tu.decls[*idx] {
        TopLevelDecl::FuncDef(f) => f,
        _ => panic!("'{}' is not a function definition", name),
    }
}

/// True if any sub-expression in `expr` (recursively) satisfies `pred`.
fn expr_has(expr: &CExpr, pred: &dyn Fn(&CExpr) -> bool) -> bool {
    if pred(expr) { return true; }
    match expr {
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner)
        | CExpr::SizeofExpr(inner) | CExpr::Paren(inner) =>
            expr_has(inner, pred),
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) | CExpr::Index(l, r) =>
            expr_has(l, pred) || expr_has(r, pred),
        CExpr::Ternary(c, t, e) =>
            expr_has(c, pred) || expr_has(t, pred) || expr_has(e, pred),
        CExpr::Call(f, args) =>
            expr_has(f, pred) || args.iter().any(|a| expr_has(a, pred)),
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) =>
            expr_has(inner, pred),
        CExpr::StmtExpr(_, inner) => expr_has(inner, pred),
        _ => false,
    }
}

/// True if any expression anywhere inside `stmt` satisfies `pred`.
fn stmt_has_expr(stmt: &CStmt, pred: &dyn Fn(&CExpr) -> bool) -> bool {
    match stmt {
        CStmt::Expr(e) => expr_has(e, pred),
        CStmt::If(cond, then_s, else_s) =>
            expr_has(cond, pred)
            || stmt_has_expr(then_s, pred)
            || else_s.as_ref().map_or(false, |s| stmt_has_expr(s, pred)),
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) =>
            expr_has(cond, pred) || stmt_has_expr(body, pred),
        CStmt::For(init, cond, update, body) => {
            let in_init = match init {
                Some(ForInit::Expr(e)) => expr_has(e, pred),
                _ => false,
            };
            in_init
            || cond.as_ref().map_or(false, |e| expr_has(e, pred))
            || update.as_ref().map_or(false, |e| expr_has(e, pred))
            || stmt_has_expr(body, pred)
        }
        CStmt::Switch(expr, body) =>
            expr_has(expr, pred) || stmt_has_expr(body, pred),
        CStmt::Return(Some(e)) => expr_has(e, pred),
        CStmt::Block(items) => items.iter().any(|item| match item {
            CBlockItem::Stmt(s) => stmt_has_expr(s, pred),
            CBlockItem::Decl(_) => false,
        }),
        CStmt::Labeled(_, inner) => stmt_has_expr(inner, pred),
        CStmt::Sequence(stmts) => stmts.iter().any(|s| stmt_has_expr(s, pred)),
        _ => false,
    }
}

/// True if `stmt` or any nested statement satisfies `pred`.
fn stmt_has(stmt: &CStmt, pred: &dyn Fn(&CStmt) -> bool) -> bool {
    if pred(stmt) { return true; }
    match stmt {
        CStmt::If(_, t, e) =>
            stmt_has(t, pred) || e.as_ref().map_or(false, |s| stmt_has(s, pred)),
        CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::For(_, _, _, b)
        | CStmt::Switch(_, b) | CStmt::Labeled(_, b) => stmt_has(b, pred),
        CStmt::Block(items) => items.iter().any(|i| match i {
            CBlockItem::Stmt(s) => stmt_has(s, pred),
            _ => false,
        }),
        CStmt::Sequence(stmts) => stmts.iter().any(|s| stmt_has(s, pred)),
        _ => false,
    }
}

// Convenience wrappers

#[allow(dead_code)]
fn has_binop(out: &TestOutput, func: &str, op: BinaryOp) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Binary(o, _, _) if *o == op))
}

#[allow(dead_code)]
fn has_unop(out: &TestOutput, func: &str, op: UnaryOp) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Unary(o, _) if *o == op))
}

/// Strip casts to get the underlying expression (callees are often cast to function pointer types).
fn unwrap_casts(e: &CExpr) -> &CExpr {
    match e {
        CExpr::Cast(_, inner) => unwrap_casts(inner),
        other => other,
    }
}

#[allow(dead_code)]
fn has_call_to(out: &TestOutput, func: &str, callee: &str) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| {
        matches!(e, CExpr::Call(f, _) if matches!(unwrap_casts(f.as_ref()), CExpr::Var(n) if n == callee))
    })
}

#[allow(dead_code)]
fn has_any_loop(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has(&f.body, &|s| matches!(s, CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..)))
}

#[allow(dead_code)]
fn has_if_stmt(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has(&f.body, &|s| matches!(s, CStmt::If(..)))
}

#[allow(dead_code)]
fn count_if(out: &TestOutput, func: &str) -> usize {
    fn count(stmt: &CStmt) -> usize {
        let here = if matches!(stmt, CStmt::If(..)) { 1 } else { 0 };
        let children = match stmt {
            CStmt::If(_, t, e) =>
                count(t) + e.as_ref().map_or(0, |s| count(s)),
            CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::For(_, _, _, b)
            | CStmt::Switch(_, b) | CStmt::Labeled(_, b) => count(b),
            CStmt::Block(items) => items.iter().map(|i| match i {
                CBlockItem::Stmt(s) => count(s),
                _ => 0,
            }).sum(),
            CStmt::Sequence(stmts) => stmts.iter().map(|s| count(s)).sum(),
            _ => 0,
        };
        here + children
    }
    count(&func_def(out, func).body)
}

#[allow(dead_code)]
fn count_loops(out: &TestOutput, func: &str) -> usize {
    fn count(stmt: &CStmt) -> usize {
        let here = if matches!(stmt, CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..)) {
            1
        } else {
            0
        };
        let children = match stmt {
            CStmt::If(_, t, e) =>
                count(t) + e.as_ref().map_or(0, |s| count(s)),
            CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::For(_, _, _, b)
            | CStmt::Switch(_, b) | CStmt::Labeled(_, b) => count(b),
            CStmt::Block(items) => items.iter().map(|i| match i {
                CBlockItem::Stmt(s) => count(s),
                _ => 0,
            }).sum(),
            CStmt::Sequence(stmts) => stmts.iter().map(|s| count(s)).sum(),
            _ => 0,
        };
        here + children
    }
    count(&func_def(out, func).body)
}

#[allow(dead_code)]
fn has_var_ref(out: &TestOutput, func: &str, var: &str) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Var(n) if n == var))
}

#[allow(dead_code)]
fn has_field_access(out: &TestOutput, func: &str, field: &str) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| match e {
        CExpr::Member(_, f) | CExpr::MemberPtr(_, f) => f == field,
        _ => false,
    })
}

#[allow(dead_code)]
fn has_switch(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has(&f.body, &|s| matches!(s, CStmt::Switch(..)))
}

#[allow(dead_code)]
fn has_break_stmt(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has(&f.body, &|s| matches!(s, CStmt::Break))
}

#[allow(dead_code)]
fn has_continue_stmt(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has(&f.body, &|s| matches!(s, CStmt::Continue))
}

#[allow(dead_code)]
fn has_deref(out: &TestOutput, func: &str) -> bool {
    has_unop(out, func, UnaryOp::Deref)
}

#[allow(dead_code)]
fn param_count(out: &TestOutput, func: &str) -> usize {
    func_def(out, func).params.len()
}

#[allow(dead_code)]
fn has_assign(out: &TestOutput, func: &str) -> bool {
    let f = func_def(out, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Assign(..)))
}


macro_rules! dual_compiler_test {
    ($name:ident, $opt:expr) => {
        mod $name {
            mod gcc {
                use super::super::*;
                pub static OUTPUT: LazyLock<TestOutput> = LazyLock::new(||
                    decompile(&compile(stringify!($name), "gcc",
                        include_str!(concat!("source/", stringify!($name), "/input.c")), $opt)));
                include!(concat!("source/", stringify!($name), "/test.rs"));
            }
            mod clang {
                use super::super::*;
                pub static OUTPUT: LazyLock<TestOutput> = LazyLock::new(||
                    decompile(&compile(stringify!($name), "clang",
                        include_str!(concat!("source/", stringify!($name), "/input.c")), $opt)));
                include!(concat!("source/", stringify!($name), "/test.rs"));
            }
        }
    };
}

// Test modules

dual_compiler_test!(smoke, "-O0");
dual_compiler_test!(regressions, "-O1");
dual_compiler_test!(arithmetic, "-O1");
dual_compiler_test!(pointers, "-O1");
dual_compiler_test!(globals, "-O0");
dual_compiler_test!(recursion, "-O1");
dual_compiler_test!(multiarg, "-O1");
dual_compiler_test!(nested_control, "-O0");
dual_compiler_test!(control_recovery, "-O0");
dual_compiler_test!(dataflow, "-O1");

// Tests adopted from angr decompiler test suite

dual_compiler_test!(switch_advanced, "-O1");
dual_compiler_test!(strings, "-O0");
dual_compiler_test!(structs_nested, "-O0");
dual_compiler_test!(expressions, "-O1");
dual_compiler_test!(structuring, "-O0");
dual_compiler_test!(loops_advanced, "-O1");
dual_compiler_test!(call_patterns, "-O1");

// Tests adopted from CompCert small test suite

dual_compiler_test!(compcert_fib, "-O1");
dual_compiler_test!(compcert_qsort, "-O1");
dual_compiler_test!(compcert_lists, "-O1");
dual_compiler_test!(compcert_sha1, "-O1");
dual_compiler_test!(compcert_switch, "-O1");
// -O0: at -O1 gcc/clang emit cmov which the decompiler doesn't reconstruct yet
dual_compiler_test!(compcert_ifconv, "-O0");
dual_compiler_test!(compcert_vmach, "-O1");

// Variable recovery tests

dual_compiler_test!(var_basic, "-O1");
dual_compiler_test!(var_phi, "-O1");
dual_compiler_test!(var_lifetime, "-O1");
dual_compiler_test!(var_copy_prop, "-O1");
dual_compiler_test!(var_register, "-O1");
dual_compiler_test!(var_stack, "-O0");
dual_compiler_test!(var_loop, "-O1");
dual_compiler_test!(var_cross_block, "-O1");
dual_compiler_test!(var_params, "-O1");
dual_compiler_test!(var_return, "-O1");
