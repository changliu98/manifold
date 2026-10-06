use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::{
    AssignOp, BinaryOp, CBlockItem, CExpr, CStmt, CType, Designator, ExprTransform, FloatLiteral,
    FloatLiteralSuffix, ForInit, FuncDef, FuncParam, InitItem, Initializer, IntLiteral,
    IntLiteralBase, IntLiteralSuffix, IntSize, Label, Signedness, SourceLoc, StmtTransform,
    StorageClass, StringLiteral, TypeQualifiers, UnaryOp, VarDecl,
};
use crate::decompile::passes::c_pass::TranslationUnit;
use crate::decompile::passes::clight_select::query::{
    extract_global_struct_decl_layouts, GlobalData,
};
use crate::decompile::passes::clight_select::select::SelectedFunction;
use crate::mreg::Mreg;
use crate::util::{exec_order_key, semantic_node_address};
use crate::x86::op::{Addressing, Operation};
use crate::x86::types as clight;
use crate::x86::types::*;
use log::debug;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

// GCC hot/cold splitting emits `<base>_cold` companions with trivial abort/unreachable bodies; drop only when name ends in `_cold` AND body matches that trivial pattern (empty body is kept, not silently deleted).
fn has_cold_suffix(name: &str) -> bool {
    name.len() > 5 && name.ends_with("_cold")
}

#[cfg(test)]
mod alignment_safe_access_tests {
    use super::{
        aggregate_member_base_type, convert_clight_type, lower_byte_buffer_expr,
        lower_byte_buffer_stmt, memcpy_load_expr, memcpy_store_expr, normalize_call_arity_expr,
        scalar_deref_alignment_proven, should_lower_scalar_deref, unsigned_integer_clight_type,
    };
    use crate::decompile::passes::c_pass::print::{PrintConfig, Printer};
    use crate::decompile::passes::c_pass::types::{
        AssignOp, CExpr, CStmt, CType, FloatSize, Initializer, UnaryOp,
    };
    use crate::x86::types::{ClightAttr, ClightExpr, ClightIntSize, ClightSignedness, ClightType};
    use std::collections::HashMap;
    use std::sync::Arc;

    fn attr() -> ClightAttr {
        ClightAttr::default()
    }

    fn unknown_address() -> ClightExpr {
        ClightExpr::Etempvar(
            1,
            ClightType::Tpointer(
                Arc::new(ClightType::Tint(
                    ClightIntSize::I8,
                    ClightSignedness::Unsigned,
                    attr(),
                )),
                attr(),
            ),
        )
    }

    #[test]
    fn unknown_scalar_alignment_lowers_to_one_exact_memcpy_load() {
        let access_ty = ClightType::Tlong(ClightSignedness::Signed, attr());
        assert!(should_lower_scalar_deref(&unknown_address(), &access_ty));

        let c_ty = CType::long();
        let address = CExpr::Call(Box::new(CExpr::Var("next_address".into())), vec![]);
        let CExpr::Unary(UnaryOp::Deref, cast) = memcpy_load_expr(c_ty.clone(), address.clone())
        else {
            panic!("safe load must read the aligned compound-literal destination")
        };
        let CExpr::Cast(_, copy) = cast.as_ref() else {
            panic!("safe load must cast the memcpy result to its exact type")
        };
        let CExpr::Call(function, args) = copy.as_ref() else {
            panic!("safe load must contain one memcpy call")
        };
        assert_eq!(function.as_ref(), &CExpr::Var("__builtin_memcpy".into()));
        assert_eq!(args.len(), 3);
        assert_eq!(args[2], CExpr::SizeofType(c_ty));
        let CExpr::Cast(_, source) = &args[1] else {
            panic!("source address must be converted to a byte-copy pointer")
        };
        assert_eq!(source.as_ref(), &address);
    }

    #[test]
    fn safe_store_evaluates_address_and_value_once() {
        let ty = CType::Float(FloatSize::Double);
        let address = CExpr::Call(Box::new(CExpr::Var("next_address".into())), vec![]);
        let value = CExpr::Call(Box::new(CExpr::Var("next_value".into())), vec![]);
        let CExpr::Call(function, args) =
            memcpy_store_expr(ty.clone(), address.clone(), value.clone())
        else {
            panic!("safe store must be one memcpy call")
        };
        assert_eq!(function.as_ref(), &CExpr::Var("__builtin_memcpy".into()));
        let CExpr::Cast(_, destination) = &args[0] else {
            panic!("destination must be converted once")
        };
        assert_eq!(destination.as_ref(), &address);
        let CExpr::Unary(UnaryOp::AddrOf, source) = &args[1] else {
            panic!("source value must be addressable")
        };
        let CExpr::CompoundLit(source_ty, initializers) = source.as_ref() else {
            panic!("source must retain its exact scalar type")
        };
        assert_eq!(source_ty, &ty);
        let [Initializer::Expr(CExpr::Cast(_, stored))] = initializers.as_slice() else {
            panic!("source compound literal must evaluate one stored value")
        };
        assert_eq!(stored.as_ref(), &value);
    }

    #[test]
    fn exact_byte_and_volatile_accesses_do_not_use_the_fallback() {
        let long_ty = ClightType::Tlong(ClightSignedness::Signed, attr());
        let exact = ClightExpr::Eaddrof(
            Box::new(ClightExpr::Evar(9, long_ty.clone())),
            ClightType::Tpointer(Arc::new(long_ty.clone()), attr()),
        );
        assert!(scalar_deref_alignment_proven(&exact, &long_ty));
        assert!(!should_lower_scalar_deref(&exact, &long_ty));

        let byte_ty = ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, attr());
        assert!(!should_lower_scalar_deref(&unknown_address(), &byte_ty));

        let volatile_long = ClightType::Tlong(
            ClightSignedness::Signed,
            ClightAttr {
                attr_volatile: true,
                attr_alignas: None,
            },
        );
        assert!(!should_lower_scalar_deref(
            &unknown_address(),
            &volatile_long,
        ));
        let converted = convert_clight_type(&volatile_long, crate::abi::DataModel::Lp64);
        let mut printer = Printer::new(PrintConfig::default());
        printer.print_type_with_name(&converted, "value");
        assert!(printer.into_string().contains("volatile"));

        let volatile_struct = ClightType::Tstruct(
            7,
            ClightAttr {
                attr_volatile: true,
                attr_alignas: None,
            },
        );
        let aggregate = convert_clight_type(&volatile_struct, crate::abi::DataModel::Lp64);
        assert_eq!(
            aggregate_member_base_type(&aggregate),
            Some(aggregate.clone())
        );
        let mut aggregate_printer = Printer::new(PrintConfig::default());
        aggregate_printer.print_type_with_name(&CType::ptr(aggregate), "pointer");
        assert!(aggregate_printer.into_string().contains("volatile"));
    }

    #[test]
    fn machine_left_shift_carriers_keep_exact_unsigned_types() {
        for ty in [
            ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, attr()),
            ClightType::Tlong(ClightSignedness::Signed, attr()),
            ClightType::Tint128(ClightSignedness::Signed, attr()),
        ] {
            let unsigned = unsigned_integer_clight_type(&ty).expect("integer carrier");
            assert!(matches!(
                unsigned,
                ClightType::Tint(_, ClightSignedness::Unsigned, _)
                    | ClightType::Tlong(ClightSignedness::Unsigned, _)
                    | ClightType::Tint128(ClightSignedness::Unsigned, _)
            ));
        }
    }

    #[test]
    fn cleanup_reaches_calls_nested_in_memcpy_compound_literals() {
        let expression = CExpr::CompoundLit(
            CType::long(),
            vec![Initializer::Expr(CExpr::call(
                CExpr::var("producer"),
                vec![CExpr::int(1), CExpr::int(2)],
            ))],
        );
        let normalized =
            normalize_call_arity_expr(&expression, &HashMap::from([("producer".into(), 1)]));
        let CExpr::CompoundLit(_, initializers) = normalized else {
            panic!("compound literal shape changed")
        };
        let [Initializer::Expr(CExpr::Call(_, args))] = initializers.as_slice() else {
            panic!("nested producer call disappeared")
        };
        assert_eq!(args, &[CExpr::int(1)]);
    }

    #[test]
    fn late_byte_buffer_lowering_preserves_load_store_and_address_contexts() {
        let int_ty = CType::int();
        let byte = CExpr::Index(Box::new(CExpr::var("buffer")), Box::new(CExpr::int(4)));
        let address = CExpr::Unary(UnaryOp::AddrOf, Box::new(byte));
        let lvalue = CExpr::Unary(
            UnaryOp::Deref,
            Box::new(CExpr::Cast(
                CType::ptr(int_ty.clone()),
                Box::new(address.clone()),
            )),
        );
        let types = HashMap::from([(
            "buffer".to_string(),
            CType::Array(Box::new(CType::char_unsigned()), Some(12)),
        )]);

        let load = lower_byte_buffer_expr(&lvalue, &types);
        assert!(matches!(
            load,
            CExpr::Unary(UnaryOp::Deref, ref cast)
                if matches!(cast.as_ref(), CExpr::Cast(_, copy)
                    if matches!(copy.as_ref(), CExpr::Call(function, _)
                        if function.as_ref() == &CExpr::var("__builtin_memcpy")))
        ));

        let formed_address = lower_byte_buffer_expr(
            &CExpr::Unary(UnaryOp::AddrOf, Box::new(lvalue.clone())),
            &types,
        );
        assert!(matches!(formed_address, CExpr::Cast(_, _)));
        assert!(!matches!(formed_address, CExpr::Call(..)));

        let store = lower_byte_buffer_stmt(
            &CStmt::Expr(CExpr::Assign(
                AssignOp::Assign,
                Box::new(lvalue),
                Box::new(CExpr::var("value")),
            )),
            &types,
        );
        assert!(matches!(
            store,
            CStmt::Expr(CExpr::Call(function, _))
                if function.as_ref() == &CExpr::var("__builtin_memcpy")
        ));
    }
}

fn is_trivial_cold_body(body: &CStmt) -> bool {
    // Unwrap a single-statement Block/Sequence wrapper, then require exactly one trivial call.
    match body {
        CStmt::Block(items) => {
            let stmts: Vec<&CStmt> = items
                .iter()
                .filter_map(|item| match item {
                    CBlockItem::Stmt(s) => Some(s),
                    CBlockItem::Decl(_) => None,
                })
                .collect();
            stmts.len() == 1 && is_trivial_cold_call(stmts[0])
        }
        CStmt::Sequence(stmts) => stmts.len() == 1 && is_trivial_cold_call(&stmts[0]),
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

/// Clight type -> CType.  CompCert's `Tlong` is the 64-BIT integer type, not the
/// C type `long`, so it takes the model's spelling for 64 bits.
fn apply_clight_volatile(base: CType, attr: &crate::x86::types::ClightAttr) -> CType {
    if attr.attr_volatile {
        CType::Qualified(
            Box::new(base),
            TypeQualifiers {
                is_volatile: true,
                ..TypeQualifiers::none()
            },
        )
    } else {
        base
    }
}

pub(crate) fn convert_clight_type(ty: &crate::x86::types::ClightType, model: crate::abi::DataModel) -> CType {
    use crate::x86::types::*;
    match ty {
        crate::x86::types::ClightType::Tvoid => CType::Void,
        crate::x86::types::ClightType::Tint(size, sign, attr) => {
            let c_size = match size {
                ClightIntSize::I8 => crate::decompile::passes::c_pass::types::IntSize::Char,
                ClightIntSize::I16 => crate::decompile::passes::c_pass::types::IntSize::Short,
                ClightIntSize::I32 | ClightIntSize::IBool => {
                    crate::decompile::passes::c_pass::types::IntSize::Int
                }
            };
            let c_sign = match sign {
                ClightSignedness::Signed => {
                    crate::decompile::passes::c_pass::types::Signedness::Signed
                }
                ClightSignedness::Unsigned => {
                    crate::decompile::passes::c_pass::types::Signedness::Unsigned
                }
            };
            apply_clight_volatile(CType::Int(c_size, c_sign), attr)
        }
        crate::x86::types::ClightType::Tlong(sign, attr) => {
            let c_sign = match sign {
                ClightSignedness::Signed => {
                    crate::decompile::passes::c_pass::types::Signedness::Signed
                }
                ClightSignedness::Unsigned => {
                    crate::decompile::passes::c_pass::types::Signedness::Unsigned
                }
            };
            apply_clight_volatile(CType::int64(model, c_sign), attr)
        }
        crate::x86::types::ClightType::Tint128(sign, attr) => {
            let c_sign = match sign {
                ClightSignedness::Signed => {
                    crate::decompile::passes::c_pass::types::Signedness::Signed
                }
                ClightSignedness::Unsigned => {
                    crate::decompile::passes::c_pass::types::Signedness::Unsigned
                }
            };
            apply_clight_volatile(
                CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Int128,
                    c_sign,
                ),
                attr,
            )
        }
        crate::x86::types::ClightType::Tfloat(size, attr) => {
            let c_size = match size {
                ClightFloatSize::F32 => crate::decompile::passes::c_pass::types::FloatSize::Float,
                ClightFloatSize::F64 => crate::decompile::passes::c_pass::types::FloatSize::Double,
            };
            apply_clight_volatile(CType::Float(c_size), attr)
        }
        crate::x86::types::ClightType::Tpointer(inner, attr) => {
            let qualifiers = TypeQualifiers {
                is_volatile: attr.attr_volatile,
                ..TypeQualifiers::none()
            };
            CType::Pointer(Box::new(convert_clight_type(inner, model)), qualifiers)
        }
        crate::x86::types::ClightType::Tarray(inner, size, attr) => apply_clight_volatile(
            CType::Array(
                Box::new(convert_clight_type(inner, model)),
                Some(*size as usize),
            ),
            attr,
        ),
        crate::x86::types::ClightType::Tfunction(params, ret, cc) => {
            let c_params: Vec<CType> = params
                .iter()
                .map(|t| convert_clight_type(t, model))
                .collect();
            // Carry the calling convention through: varargs gives variadic (T, ...), unproto gives true K&R () (unspecified args, distinct from (void)).
            CType::Function(
                Box::new(convert_clight_type(ret, model)),
                c_params,
                cc.varargs.is_some(),
                cc.unproto,
            )
        }
        crate::x86::types::ClightType::Tstruct(id, attr) => {
            apply_clight_volatile(CType::Struct(format!("struct_{:x}", id)), attr)
        }
        crate::x86::types::ClightType::Tunion(id, attr) => {
            apply_clight_volatile(CType::Union(format!("union_{}", id)), attr)
        }
    }
}

fn clight_expr_to_ctype(expr: &clight::ClightExpr, model: crate::abi::DataModel) -> CType {
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
    convert_clight_type(clight_ty, model)
}

fn aggregate_member_base_type(ty: &CType) -> Option<CType> {
    match ty {
        CType::Struct(_) | CType::Union(_) => Some(ty.clone()),
        CType::Qualified(inner, _)
            if matches!(inner.as_ref(), CType::Struct(_) | CType::Union(_)) =>
        {
            Some(ty.clone())
        }
        _ => None,
    }
}

// Well-known variadic libc/coreutils functions whose recovered prototypes carry only the fixed leading params, so calls passing the variadic tail need the prototype declared variadic.
fn is_known_variadic_fn(name: &str) -> bool {
    matches!(
        name,
        "printf"
            | "fprintf"
            | "sprintf"
            | "snprintf"
            | "dprintf"
            | "scanf"
            | "fscanf"
            | "sscanf"
            | "__printf_chk"
            | "__fprintf_chk"
            | "__sprintf_chk"
            | "__snprintf_chk"
            | "__isoc99_scanf"
            | "__isoc99_fscanf"
            | "__isoc99_sscanf"
            | "error"
            | "error_at_line"
            | "open"
            | "openat"
            | "fcntl"
            | "ioctl"
            | "syslog"
            | "asprintf"
            | "execl"
            | "execlp"
            | "execle"
    )
}

/// XType -> CType.  `Xlong` is the C type `long` and stays `long` on every
/// target; `Xany64` is "some 64-bit value" and has to be spelled for the model,
/// which is the whole reason this takes one.
fn convert_xtype(xt: &XType, model: crate::abi::DataModel) -> CType {
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
            Box::new(CType::Float(
                crate::decompile::passes::c_pass::types::FloatSize::Double,
            )),
            TypeQualifiers::none(),
        ),
        XType::Xsingleptr => CType::Pointer(
            Box::new(CType::Float(
                crate::decompile::passes::c_pass::types::FloatSize::Float,
            )),
            TypeQualifiers::none(),
        ),
        XType::Xfuncptr => CType::Pointer(
            Box::new(CType::Function(
                Box::new(CType::Void),
                Vec::new(),
                false,
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
        XType::Xany64 => CType::int64(
            model,
            crate::decompile::passes::c_pass::types::Signedness::Signed,
        ),
        XType::Xbool => CType::Bool,
        XType::XstructPtr(id) => CType::Pointer(
            Box::new(CType::Struct(format!("struct_{:x}", id))),
            TypeQualifiers::none(),
        ),
    }
}

/// Policy for locally-DEFINED functions colliding with a header declaration: "filter" drops the body, otherwise (and by default) it is emitted renamed <name>_local.
struct LocalDefPolicy {
    renames: HashMap<String, String>,
    filtered: HashSet<String>,
}

/// The canonical type spellings used by header_functions.json "globals" `type` fields (exposed as header_db().variables) -- a closed set kept tiny on purpose (header-declared globals are scalars/pointers, not aggregates).
fn parse_canonical_var_type(spelling: &str, model: crate::abi::DataModel) -> Option<CType> {
    crate::decompile::passes::c_pass::header_db::canonical_variable_clight_type(spelling)
        .as_ref()
        .map(|ty| convert_clight_type(ty, model))
}

fn header_collision_policy(selected_functions: &[SelectedFunction]) -> LocalDefPolicy {
    let hdb = crate::decompile::passes::c_pass::header_db::header_db();
    let is_provided =
        |n: &str| hdb.functions.contains(n) || hdb.prefixes.iter().any(|p| n.starts_with(p));
    let mut policy = LocalDefPolicy {
        renames: HashMap::new(),
        filtered: HashSet::new(),
    };
    for f in selected_functions {
        if f.name.starts_with("FUN_") {
            continue;
        }
        let name = sanitize_c_symbol_name(&f.name);
        if !is_provided(&name) {
            continue;
        }
        if hdb.local_def_filter.contains(name.as_str()) {
            policy.filtered.insert(name);
        } else {
            policy
                .renames
                .insert(name.clone(), format!("{}_local", name));
        }
    }
    policy
}

#[derive(Default)]
pub(crate) struct EscapedStackArrayLayouts {
    pub(crate) arrays: HashMap<Address, HashMap<RTLReg, (MemoryChunk, usize)>>,
    pub(crate) members: HashMap<Address, HashMap<RTLReg, (RTLReg, usize)>>,
}

#[derive(Default)]
pub(crate) struct EscapedStackBufferLayouts {
    pub(crate) buffers: HashMap<Address, HashMap<RTLReg, usize>>,
    pub(crate) members: HashMap<Address, HashMap<RTLReg, (RTLReg, usize, MemoryChunk)>>,
}

/// The same allocation decisions must be visible before declaration selection
/// and during emission. A field/local name absorbed by an allocation is an
/// access view, not an independent scalar whose declaration may be narrowed.
pub(crate) fn escaped_stack_layouts(
    db: &DecompileDB,
) -> (EscapedStackArrayLayouts, EscapedStackBufferLayouts) {
    let mut arrays = derive_escaped_stack_array_layouts(db);
    let buffers = derive_escaped_stack_buffer_layouts(db, &arrays);
    remove_buffer_owned_array_layouts(&mut arrays, &buffers);
    (arrays, buffers)
}

type StackBufferAliases = HashMap<Address, HashMap<RTLReg, (RTLReg, usize)>>;
type StackBufferEndAliases = HashMap<Address, HashMap<RTLReg, (RTLReg, usize)>>;
type ExactStackBufferStores =
    HashMap<Address, HashMap<(RTLReg, RTLReg), (RTLReg, usize, MemoryChunk)>>;

#[derive(Clone, Debug, PartialEq, Eq)]
struct RawFrameBufferRegion {
    start: i64,
    end: i64,
    backing: String,
}

#[derive(Default)]
struct RawFrameBufferLayouts {
    base_pointer_names: HashMap<Address, HashSet<String>>,
    regions: HashMap<Address, Vec<RawFrameBufferRegion>>,
}

#[derive(Default)]
struct GlobalAggregateCoalescing {
    owner_ids: HashSet<Ident>,
    member_ids: HashSet<Ident>,
    member_exprs: HashMap<String, CExpr>,
    owner_initializers: HashMap<Ident, crate::decompile::passes::c_pass::types::Initializer>,
}

/// Materialize one recovered global aggregate owner and coalesce any synthetic
/// labels that name its exact interior fields.
///
/// Machine globals occupy byte ranges; C globals do not overlap. Emitting a
/// struct at `base` and an independent pointer at `base + 8` therefore loses
/// both aliasing and the relocation initializer. This accepts only the bounded
/// case for which recovery has already supplied an exact, non-overlapping
/// aggregate layout and every interior declaration starts on a field boundary.
/// Real ELF names are left alone because their externally visible identity may
/// matter. Nonzero padding also rejects the candidate: there is no field that
/// can carry those bytes without changing the recovered type.
fn derive_global_aggregate_coalescing(
    db: &DecompileDB,
    globals: &[GlobalData],
    layouts: &HashMap<Ident, (usize, Vec<(i64, Ident, MemoryChunk)>)>,
) -> GlobalAggregateCoalescing {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
    use crate::decompile::passes::c_pass::types::{Designator, InitItem, Initializer};

    fn synthetic_label_matches(global: &GlobalData) -> bool {
        global
            .name
            .strip_prefix("L_")
            .and_then(|hex| usize::from_str_radix(hex, 16).ok())
            == Some(global.id)
    }

    fn int_expr(raw: u64, width: usize, chunk: MemoryChunk) -> CExpr {
        let signed = matches!(
            chunk,
            MemoryChunk::MInt8Signed
                | MemoryChunk::MInt16Signed
                | MemoryChunk::MInt32
                | MemoryChunk::MInt64
                | MemoryChunk::MAny32
                | MemoryChunk::MAny64
        );
        let value = if signed {
            match width {
                1 => raw as u8 as i8 as i128,
                2 => raw as u16 as i16 as i128,
                4 => raw as u32 as i32 as i128,
                _ => raw as i64 as i128,
            }
        } else {
            raw as i128
        };
        CExpr::IntLit(IntLiteral {
            value,
            suffix: if width == 8 {
                IntLiteralSuffix::L
            } else {
                IntLiteralSuffix::None
            },
            base: IntLiteralBase::Decimal,
        })
    }

    let initialized_ranges: Vec<(Address, Arc<Vec<u8>>)> = db
        .rel_iter::<(Address, Arc<Vec<u8>>)>("retained_initialized_data_range")
        .map(|(start, bytes)| (*start, bytes.clone()))
        .collect();
    let relocation_slots: BTreeSet<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, _)| *slot)
        .collect();
    let bytes_at = |addr: Address, len: usize| -> Option<Vec<u8>> {
        let end = addr.checked_add(u64::try_from(len).ok()?)?;
        let mut matches = initialized_ranges.iter().filter(|(start, bytes)| {
            addr >= *start
                && end <= start.saturating_add(u64::try_from(bytes.len()).unwrap_or(u64::MAX))
        });
        let (start, bytes) = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        let offset = usize::try_from(addr - *start).ok()?;
        Some(bytes.get(offset..offset.checked_add(len)?)?.to_vec())
    };

    let globals_by_id: HashMap<Ident, &GlobalData> =
        globals.iter().map(|global| (global.id, global)).collect();
    let symbol_sizes: HashMap<Ident, BTreeSet<usize>> = {
        let mut result: HashMap<Ident, BTreeSet<usize>> = HashMap::new();
        for (addr, size, _) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
            if *size > 0 {
                result.entry(*addr as Ident).or_default().insert(*size);
            }
        }
        result
    };

    let mut result = GlobalAggregateCoalescing::default();
    let mut owners: Vec<_> = layouts.keys().copied().collect();
    owners.sort_unstable();
    for owner_id in owners {
        let Some(owner) = globals_by_id.get(&owner_id).copied() else {
            continue;
        };
        if !synthetic_label_matches(owner) {
            continue;
        }
        let Some((_, fields)) = layouts.get(&owner_id) else {
            continue;
        };
        let mut fields = fields.clone();
        fields.sort_by_key(|(offset, name, chunk)| (*offset, *name, *chunk));
        if fields.is_empty() || fields[0].0 != 0 {
            continue;
        }

        let mut field_ranges = Vec::new();
        let mut valid = true;
        for (offset, field_name, chunk) in &fields {
            let width = chunk_byte_size(chunk);
            let Some(end) = offset
                .checked_add(i64::try_from(width).unwrap_or(i64::MAX))
                .filter(|_| *offset >= 0 && width > 0)
            else {
                valid = false;
                break;
            };
            if field_ranges
                .last()
                .is_some_and(|(_, previous_end, _): &(i64, i64, Ident)| *previous_end > *offset)
            {
                valid = false;
                break;
            }
            field_ranges.push((*offset, end, *field_name));
        }
        let Some(extent) = field_ranges.last().map(|(_, end, _)| *end) else {
            continue;
        };
        let Ok(extent_usize) = usize::try_from(extent) else {
            continue;
        };
        let Some(owner_bytes) = bytes_at(owner_id as Address, extent_usize) else {
            continue;
        };

        // No recovered field can preserve initialized padding bytes.
        for (index, byte) in owner_bytes.iter().copied().enumerate() {
            let covered = field_ranges
                .iter()
                .any(|(start, end, _)| (index as i64) >= *start && (index as i64) < *end);
            if !covered && byte != 0 {
                valid = false;
                break;
            }
        }
        if !valid {
            continue;
        }

        let field_by_offset: HashMap<i64, (Ident, MemoryChunk)> = fields
            .iter()
            .map(|(offset, name, chunk)| (*offset, (*name, *chunk)))
            .collect();

        // Every relocation in the recovered byte range must coincide with an
        // exact pointer-width integer field and have a relocatable expression
        // supplied by extraction.  Falling back to the pre-relocation raw word
        // would bake an obsolete link address into the regenerated program.
        let pointer_size = db.abi().pointer_size;
        let Some(owner_end) = (owner_id as Address).checked_add(extent as u64) else {
            continue;
        };
        for slot in relocation_slots.range(owner_id as Address..owner_end) {
            let Ok(offset) = i64::try_from(*slot - owner_id as Address) else {
                valid = false;
                break;
            };
            let Some((_, chunk)) = field_by_offset.get(&offset) else {
                valid = false;
                break;
            };
            let pointer_integer_chunk = match pointer_size {
                4 => matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
                8 => matches!(chunk, MemoryChunk::MInt64 | MemoryChunk::MAny64),
                _ => false,
            };
            if !pointer_integer_chunk || !owner.aggregate_relocation_init.contains_key(&offset) {
                valid = false;
                break;
            }
        }
        if !valid {
            continue;
        }

        let mut member_rows = Vec::new();
        for member in globals.iter().filter(|global| {
            global.id > owner_id
                && i64::try_from(global.id - owner_id).is_ok_and(|offset| offset < extent)
        }) {
            let offset = i64::try_from(member.id - owner_id).unwrap();
            let Some((field_name, chunk)) = field_by_offset.get(&offset).copied() else {
                valid = false;
                break;
            };
            if !synthetic_label_matches(member) || member.is_string {
                valid = false;
                break;
            }
            let width = chunk_byte_size(&chunk);
            if symbol_sizes
                .get(&member.id)
                .is_some_and(|sizes| sizes.len() != 1 || !sizes.contains(&width))
            {
                valid = false;
                break;
            }
            if member.pointer_init.len() > 1 {
                valid = false;
                break;
            }
            member_rows.push((member, offset, field_name, chunk));
        }
        // A direct Aglobal(owner, nonzero_offset) access does not create a
        // second GlobalData row, but the owner's validated field layout still
        // needs the original image bytes.  Requiring an interior label here
        // emitted a correctly shaped yet zero-filled aggregate.  The same
        // bounds, padding, and relocation checks above make a label-free owner
        // just as exact as one which happens to have a named interior field.
        if !valid {
            continue;
        }

        let member_at_offset: HashMap<i64, &GlobalData> = member_rows
            .iter()
            .map(|(member, offset, _, _)| (*offset, *member))
            .collect();
        let mut items = Vec::new();
        for (offset, field_name, chunk) in &fields {
            let width = chunk_byte_size(chunk);
            let value = if let Some(pointer) = owner.aggregate_relocation_init.get(offset) {
                Some(CExpr::Cast(
                    ctype_from_memchunk(chunk, db.data_model()),
                    Box::new(pointer.clone()),
                ))
            } else if let Some(member) = member_at_offset.get(offset).copied() {
                if let Some(pointer) = member.pointer_init.first() {
                    Some(CExpr::Cast(
                        ctype_from_memchunk(chunk, db.data_model()),
                        Box::new(pointer.clone()),
                    ))
                } else {
                    member.scalar_value.as_ref().map(|scalar| {
                        CExpr::Cast(ctype_from_memchunk(chunk, db.data_model()), Box::new(scalar.to_cexpr()))
                    })
                }
            } else {
                None
            };
            let value = value.or_else(|| {
                let start = usize::try_from(*offset).ok()?;
                let bytes = owner_bytes.get(start..start.checked_add(width)?)?;
                let raw = bytes.iter().enumerate().fold(0_u64, |word, (index, byte)| {
                    word | ((*byte as u64) << (index * 8))
                });
                (raw != 0).then(|| int_expr(raw, width, *chunk))
            });
            if let Some(value) = value {
                items.push(InitItem {
                    designator: Some(Designator::Field(
                        crate::decompile::passes::csh_pass::field_ident_to_name(*field_name),
                    )),
                    init: Initializer::Expr(value),
                });
            }
        }

        for (member, _offset, field_name, _) in member_rows {
            result.member_ids.insert(member.id);
            result.member_exprs.insert(
                sanitize_c_symbol_name(&member.name),
                CExpr::Member(
                    Box::new(CExpr::Var(sanitize_c_symbol_name(&owner.name))),
                    crate::decompile::passes::csh_pass::field_ident_to_name(field_name),
                ),
            );
        }
        result.owner_ids.insert(owner_id);
        if !items.is_empty() {
            result
                .owner_initializers
                .insert(owner_id, Initializer::List(items));
        }
    }
    result
}

fn rewrite_global_interior_initializer(
    init: &crate::decompile::passes::c_pass::types::Initializer,
    members: &HashMap<String, CExpr>,
) -> crate::decompile::passes::c_pass::types::Initializer {
    use crate::decompile::passes::c_pass::types::{InitItem, Initializer};
    match init {
        Initializer::Expr(expr) => Initializer::Expr(
            crate::decompile::passes::c_pass::helpers::map_expr(expr, &|candidate| {
                let CExpr::Var(name) = candidate else {
                    return None;
                };
                members.get(name).cloned()
            }),
        ),
        Initializer::List(items) => Initializer::List(
            items
                .iter()
                .map(|item| InitItem {
                    designator: item.designator.as_ref().map(|designator| {
                        transform_designator_exprs(designator, &|expr| {
                            crate::decompile::passes::c_pass::helpers::map_expr(
                                expr,
                                &|candidate| {
                                    let CExpr::Var(name) = candidate else {
                                        return None;
                                    };
                                    members.get(name).cloned()
                                },
                            )
                        })
                    }),
                    init: rewrite_global_interior_initializer(&item.init, members),
                })
                .collect(),
        ),
        Initializer::String(literal) => Initializer::String(literal.clone()),
    }
}

fn order_globals_for_aggregate_initializers<'a>(
    globals: &'a [GlobalData],
    coalescing: &GlobalAggregateCoalescing,
) -> Vec<&'a GlobalData> {
    use crate::decompile::passes::c_pass::types::Initializer;

    fn collect_expr_vars(expr: &CExpr, out: &mut HashSet<String>) {
        match expr {
            CExpr::Var(name) => {
                out.insert(name.clone());
            }
            CExpr::Unary(_, inner)
            | CExpr::Cast(_, inner)
            | CExpr::SizeofExpr(inner)
            | CExpr::Paren(inner)
            | CExpr::Member(inner, _)
            | CExpr::MemberPtr(inner, _) => collect_expr_vars(inner, out),
            CExpr::Binary(_, lhs, rhs) | CExpr::Assign(_, lhs, rhs) | CExpr::Index(lhs, rhs) => {
                collect_expr_vars(lhs, out);
                collect_expr_vars(rhs, out);
            }
            CExpr::Ternary(cond, then_expr, else_expr) => {
                collect_expr_vars(cond, out);
                collect_expr_vars(then_expr, out);
                collect_expr_vars(else_expr, out);
            }
            CExpr::Call(callee, args) => {
                collect_expr_vars(callee, out);
                for arg in args {
                    collect_expr_vars(arg, out);
                }
            }
            CExpr::CompoundLit(_, initializers) => {
                for init in initializers {
                    collect_init_vars(init, out);
                }
            }
            CExpr::Generic(selector, arms) => {
                collect_expr_vars(selector, out);
                for (_, arm) in arms {
                    collect_expr_vars(arm, out);
                }
            }
            CExpr::StmtExpr(stmts, tail) => {
                for stmt in stmts {
                    collect_stmt_vars(stmt, out);
                }
                collect_expr_vars(tail, out);
            }
            _ => {}
        }
    }

    fn collect_init_vars(init: &Initializer, out: &mut HashSet<String>) {
        match init {
            Initializer::Expr(expr) => collect_expr_vars(expr, out),
            Initializer::List(items) => {
                for item in items {
                    if let Some(designator) = &item.designator {
                        match designator {
                            Designator::Field(_) => {}
                            Designator::Index(expr) => collect_expr_vars(expr, out),
                            Designator::Range(first, last) => {
                                collect_expr_vars(first, out);
                                collect_expr_vars(last, out);
                            }
                        }
                    }
                    collect_init_vars(&item.init, out);
                }
            }
            Initializer::String(_) => {}
        }
    }

    fn collect_stmt_vars(stmt: &CStmt, out: &mut HashSet<String>) {
        match stmt {
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => collect_expr_vars(expr, out),
            CStmt::Block(items) => {
                for item in items {
                    match item {
                        CBlockItem::Stmt(stmt) => collect_stmt_vars(stmt, out),
                        CBlockItem::Decl(decls) => {
                            for decl in decls {
                                if let Some(init) = &decl.init {
                                    collect_init_vars(init, out);
                                }
                            }
                        }
                    }
                }
            }
            CStmt::If(cond, then_stmt, else_stmt) => {
                collect_expr_vars(cond, out);
                collect_stmt_vars(then_stmt, out);
                if let Some(else_stmt) = else_stmt {
                    collect_stmt_vars(else_stmt, out);
                }
            }
            CStmt::Switch(expr, body) | CStmt::While(expr, body) | CStmt::DoWhile(body, expr) => {
                collect_expr_vars(expr, out);
                collect_stmt_vars(body, out);
            }
            CStmt::For(init, cond, update, body) => {
                if let Some(init) = init {
                    match init {
                        ForInit::Expr(expr) => collect_expr_vars(expr, out),
                        ForInit::Decl(decls) => {
                            for decl in decls {
                                if let Some(init) = &decl.init {
                                    collect_init_vars(init, out);
                                }
                            }
                        }
                    }
                }
                if let Some(cond) = cond {
                    collect_expr_vars(cond, out);
                }
                if let Some(update) = update {
                    collect_expr_vars(update, out);
                }
                collect_stmt_vars(body, out);
            }
            (CStmt::Labeled(_, body) | CStmt::Effect(_, body)) => collect_stmt_vars(body, out),
            CStmt::Decl(decls) => {
                for decl in decls {
                    if let Some(init) = &decl.init {
                        collect_init_vars(init, out);
                    }
                }
            }
            CStmt::Sequence(stmts) => {
                for stmt in stmts {
                    collect_stmt_vars(stmt, out);
                }
            }
            _ => {}
        }
    }

    let nodes: Vec<&GlobalData> = globals
        .iter()
        .filter(|global| !coalescing.member_ids.contains(&global.id))
        .collect();
    let index_by_name: HashMap<String, usize> = nodes
        .iter()
        .enumerate()
        .map(|(index, global)| (sanitize_c_symbol_name(&global.name), index))
        .collect();
    let mut successors = vec![BTreeSet::new(); nodes.len()];
    let mut indegree = vec![0_usize; nodes.len()];
    for (consumer, global) in nodes.iter().enumerate() {
        let mut dependencies = HashSet::new();
        for expr in &global.pointer_init {
            let rewritten =
                crate::decompile::passes::c_pass::helpers::map_expr(expr, &|candidate| {
                    let CExpr::Var(name) = candidate else {
                        return None;
                    };
                    coalescing.member_exprs.get(name).cloned()
                });
            collect_expr_vars(&rewritten, &mut dependencies);
        }
        if let Some(init) = coalescing.owner_initializers.get(&global.id) {
            collect_init_vars(init, &mut dependencies);
        }
        for name in dependencies {
            let Some(&dependency) = index_by_name.get(&name) else {
                continue;
            };
            if dependency != consumer && successors[dependency].insert(consumer) {
                indegree[consumer] += 1;
            }
        }
    }

    let mut ready: BTreeSet<usize> = indegree
        .iter()
        .enumerate()
        .filter_map(|(index, degree)| (*degree == 0).then_some(index))
        .collect();
    let mut order = Vec::with_capacity(nodes.len());
    while let Some(index) = ready.pop_first() {
        order.push(index);
        for successor in successors[index].iter().copied() {
            indegree[successor] -= 1;
            if indegree[successor] == 0 {
                ready.insert(successor);
            }
        }
    }
    // Preserve deterministic declarations even for an unexpected dependency
    // cycle; the existing C emitter will diagnose that cycle rather than this
    // layout pass silently dropping definitions.
    if order.len() != nodes.len() {
        let emitted: HashSet<usize> = order.iter().copied().collect();
        order.extend((0..nodes.len()).filter(|index| !emitted.contains(index)));
    }
    order.into_iter().map(|index| nodes[index]).collect()
}

/// Read exact frame-layout aliases published by the Clight field pass.
///
/// A conflicting row is not a choice to make here: it means the producer did
/// not establish one physical backing address, so omit that alias rather than
/// making emitted C depend on relation iteration order.
fn derive_stack_buffer_aliases(db: &DecompileDB) -> StackBufferAliases {
    let mut candidates: BTreeMap<(Address, RTLReg), BTreeSet<(RTLReg, usize)>> = BTreeMap::new();
    for &(func, member, base, offset) in
        db.rel_iter::<(Address, RTLReg, RTLReg, usize)>("stack_buffer_alias")
    {
        candidates
            .entry((func, member))
            .or_default()
            .insert((base, offset));
    }
    let coordinates = crate::decompile::analysis::frame_coordinates::FrameCoordinates::collect(db);
    let stack_rows: Vec<_> = db
        .rel_iter::<(Address, Node, i64, RTLReg)>("stack_var")
        .copied()
        .collect();
    // Independently sized byte buffers also own every exact stack cell inside
    // their interval.  Publish those aliases here even when no overlapping
    // range forced the Clight sizer's coalescing path.
    for (&func, buffers) in &db.stack_struct_buffers {
        for (&base, &size) in buffers {
            if size <= 0 {
                continue;
            }
            let base_offsets: BTreeSet<i64> = stack_rows
                .iter()
                .filter_map(|(owner, _, offset, local)| {
                    (*owner == func && *local == base).then_some(*offset)
                })
                .filter_map(|offset| coordinates.start(func, offset))
                .collect();
            for &(owner, _, cell_offset, member) in &stack_rows {
                if owner != func {
                    continue;
                }
                for base_offset in &base_offsets {
                    let Some(end) = base_offset.checked_add(size) else {
                        continue;
                    };
                    if let Some(cell) = coordinates.start(func, cell_offset) {
                        if cell < *base_offset || cell >= end {
                            continue;
                        }
                        let Some(relative) = cell.checked_sub(*base_offset) else {
                            continue;
                        };
                        let Ok(relative) = usize::try_from(relative) else {
                            continue;
                        };
                        candidates
                            .entry((func, member))
                            .or_default()
                            .insert((base, relative));
                    }
                }
            }
        }
    }
    // The chosen backing local is also a semantic stack cell at byte offset
    // zero.  Once its declaration becomes `unsigned char[N]`, a direct scalar
    // read/write of that local must still access the cell rather than decay to
    // the buffer's address.  Publish the identity mapping through the same
    // conflict check as every absorbed root.
    for (&func, buffers) in &db.stack_struct_buffers {
        for &base in buffers.keys() {
            candidates
                .entry((func, base))
                .or_default()
                .insert((base, 0));
        }
    }

    let mut result = StackBufferAliases::default();
    for ((func, member), choices) in candidates {
        let mut choices = choices.into_iter();
        let Some(choice) = choices.next() else {
            continue;
        };
        if choices.next().is_none() {
            result.entry(func).or_default().insert(member, choice);
        }
    }
    result
}

fn semantic_declaration_views(
    db: &DecompileDB,
    function: Address,
    aliases: Option<&HashMap<RTLReg, (RTLReg, usize)>>,
) -> HashMap<String, Vec<crate::decompile::passes::semantic_counterexample::ledger::ObjectView>> {
    use crate::decompile::passes::semantic_counterexample::ledger::{self, ObjectView};
    let mut result: HashMap<String, Vec<ObjectView>> = HashMap::new();
    for contract in ledger::committed(db).into_iter().filter(|e| e.object.function == function) {
        let roots: BTreeSet<_> = db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
            .filter(|r| (r.0, r.1) == (function, contract.object.base)).map(|r| r.2).collect();
        if roots.len() != 1 || contract.extent <= 0 { continue; }
        let mut root = *roots.first().unwrap();
        let mut offset = 0_usize;
        let mut seen = BTreeSet::new();
        let mut valid = true;
        while let Some(&(parent, delta)) = aliases.and_then(|a| a.get(&root)) {
            if parent == root { valid &= delta == 0; break; }
            if !seen.insert(root) { valid = false; break; }
            let Some(next) = offset.checked_add(delta) else { valid = false; break; };
            root = parent; offset = next;
        }
        if !valid { continue; }
        let view = ObjectView { object: contract.object, offset, extent: contract.extent as usize };
        let name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(root);
        let views = result.entry(name).or_default();
        if !views.contains(&view) { views.push(view); }
    }
    for views in result.values_mut() { views.sort_by_key(|v| (v.object, v.offset, v.extent)); }
    result
}

fn derive_stack_buffer_end_aliases(db: &DecompileDB) -> StackBufferEndAliases {
    let mut candidates: BTreeMap<(Address, RTLReg), BTreeSet<(RTLReg, usize)>> = BTreeMap::new();
    for &(func, endpoint, base, offset) in
        db.rel_iter::<(Address, RTLReg, RTLReg, usize)>("stack_buffer_end_alias")
    {
        candidates
            .entry((func, endpoint))
            .or_default()
            .insert((base, offset));
    }
    let mut result = StackBufferEndAliases::default();
    for ((func, endpoint), choices) in candidates {
        let mut choices = choices.into_iter();
        let Some(choice) = choices.next() else {
            continue;
        };
        if choices.next().is_none() {
            result.entry(func).or_default().insert(endpoint, choice);
        }
    }
    result
}

fn stack_local_physical_types(db: &DecompileDB, function: Address) -> HashMap<String, CType> {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;

    let mut chunks: BTreeMap<i64, MemoryChunk> = BTreeMap::new();
    for &(func, offset, chunk) in db.rel_iter::<(Address, i64, MemoryChunk)>("stack_var_chunk") {
        if func != function || matches!(chunk, MemoryChunk::Unknown) {
            continue;
        }
        chunks
            .entry(offset)
            .and_modify(|current| {
                if (chunk_byte_size(&chunk), chunk) < (chunk_byte_size(current), *current) {
                    *current = chunk;
                }
            })
            .or_insert(chunk);
    }

    let exact_store_chunks = crate::decompile::passes::clight_pass::exact_stack_store_chunks(db);
    let mut local_chunks: BTreeMap<RTLReg, MemoryChunk> = BTreeMap::new();
    for &(func, node, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        if func != function {
            continue;
        }
        let Some(chunk) = exact_store_chunks
            .get(&node)
            .or_else(|| chunks.get(&offset))
            .copied()
        else {
            continue;
        };
        local_chunks
            .entry(local)
            .and_modify(|current| {
                if (chunk_byte_size(&chunk), chunk) < (chunk_byte_size(current), *current) {
                    *current = chunk;
                }
            })
            .or_insert(chunk);
    }
    local_chunks
        .into_iter()
        .map(|(local, chunk)| {
            (
                crate::decompile::passes::c_pass::helpers::param_name_for_reg(local),
                ctype_from_memchunk(&chunk, db.data_model()),
            )
        })
        .collect()
}

fn apply_stack_struct_buffer_types(
    db: &DecompileDB,
    function: Address,
    local_var_types: &mut HashMap<String, CType>,
) {
    let Some(buffers) = db.stack_struct_buffers.get(&function) else {
        return;
    };
    let mut widest: BTreeMap<String, usize> = BTreeMap::new();
    for (reg, size) in buffers {
        let Ok(size) = usize::try_from(*size) else {
            continue;
        };
        if size == 0 {
            continue;
        }
        let name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
        widest
            .entry(name)
            .and_modify(|current| *current = (*current).max(size))
            .or_insert(size);
    }
    for (name, size) in widest {
        local_var_types.insert(
            name,
            CType::Array(Box::new(CType::char_unsigned()), Some(size)),
        );
    }
}

fn rewrite_stack_buffer_end_aliases(
    body: &CStmt,
    aliases: &HashMap<RTLReg, (RTLReg, usize)>,
) -> CStmt {
    let names: HashMap<String, (String, usize)> = aliases
        .iter()
        .map(|(endpoint, (base, offset))| {
            (
                crate::decompile::passes::c_pass::helpers::param_name_for_reg(*endpoint),
                (
                    crate::decompile::passes::c_pass::helpers::param_name_for_reg(*base),
                    *offset,
                ),
            )
        })
        .collect();
    crate::decompile::passes::c_pass::helpers::map_stmt_exprs(body, &|expr| {
        let CExpr::Unary(UnaryOp::AddrOf, inner) = expr else {
            return None;
        };
        let CExpr::Var(endpoint) = inner.as_ref() else {
            return None;
        };
        let (base, offset) = names.get(endpoint)?;
        Some(CExpr::Binary(
            BinaryOp::Add,
            Box::new(CExpr::Cast(
                CType::ptr(CType::char_unsigned()),
                Box::new(CExpr::Var(base.clone())),
            )),
            Box::new(CExpr::int(*offset as i64)),
        ))
    })
}

fn stack_buffer_alias_byte_expr(base: &str, offset: usize) -> CExpr {
    CExpr::Index(
        Box::new(CExpr::Cast(
            CType::ptr(CType::char_unsigned()),
            Box::new(CExpr::Var(base.to_string())),
        )),
        Box::new(CExpr::int(offset as i64)),
    )
}

/// Recover the raw frame-pointer coordinates of byte buffers that already
/// have one proven C backing object.
///
/// `stack_var` normally uses the post-prologue coordinate system, while a few
/// expressions retained from machine addressing can still be `RBP + disp`.
/// A conversion between the two is valid only for a conventional framed
/// function with one observed allocation size.  Conflicting frame sizes,
/// multiple locations for one backing local, and buffers extending outside
/// the allocated frame are deliberately rejected.
fn derive_raw_frame_buffer_layouts(db: &DecompileDB) -> RawFrameBufferLayouts {
    let coordinates = crate::decompile::analysis::frame_coordinates::FrameCoordinates::collect(db);
    // Frame-coordinate conversion and ownership of surviving BP values are
    // separate facts. The latter still needs exact instruction ownership.
    let mut node_owners: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        node_owners.entry(node).or_default().insert(function);
    }
    let frame_sizes: HashMap<Address, i64> = db.stack_struct_buffers.keys()
        .filter_map(|&func| coordinates.origin(func).filter(|size| *size > 0).map(|size| (func, size)))
        .collect();

    let mut base_offsets: BTreeMap<(Address, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    for &(func, _, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        if !frame_sizes.contains_key(&func) {
            continue;
        }
        let normalized = coordinates.start(func, offset);
        if let Some(normalized) = normalized.filter(|offset| *offset >= 0) {
            base_offsets
                .entry((func, local))
                .or_default()
                .insert(normalized);
        }
    }

    let mut result = RawFrameBufferLayouts::default();
    for (&func, function_buffers) in &db.stack_struct_buffers {
        let Some(&frame_size) = frame_sizes.get(&func) else {
            continue;
        };
        for (&backing, &size_i64) in function_buffers {
            if size_i64 <= 0 || usize::try_from(size_i64).is_err() {
                continue;
            }
            let Some(offsets) = base_offsets.get(&(func, backing)) else {
                continue;
            };
            let valid_offsets: BTreeSet<i64> = offsets
                .iter()
                .copied()
                .filter(|offset| {
                    offset
                        .checked_add(size_i64)
                        .is_some_and(|end| end <= frame_size)
                })
                .collect();
            if valid_offsets.len() != 1 {
                continue;
            }
            let normalized_start = *valid_offsets.first().unwrap();
            let Some(start) = normalized_start.checked_sub(frame_size) else {
                continue;
            };
            let Some(end) = start.checked_add(size_i64) else {
                continue;
            };
            result
                .regions
                .entry(func)
                .or_default()
                .push(RawFrameBufferRegion {
                    start,
                    end,
                    backing: crate::decompile::passes::c_pass::helpers::param_name_for_reg(backing),
                });
        }
    }

    for regions in result.regions.values_mut() {
        regions.sort_by(|left, right| {
            (left.start, left.end, &left.backing).cmp(&(right.start, right.end, &right.backing))
        });
        regions.dedup();
    }

    for &(node, mreg, rtl) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if mreg != Mreg::BP {
            continue;
        }
        let func = match node_owners.get(&node) {
            Some(owners) if owners.len() == 1 => *owners.first().unwrap(),
            // Entry register facts are keyed by the function address itself;
            // unlike instructions, that synthetic entry does not need an
            // `instr_in_function` row.  It is the exact value used when a raw
            // BP operand survives the prologue normalization.
            _ if frame_sizes.contains_key(&(node as Address)) => node as Address,
            _ => continue,
        };
        if !result.regions.contains_key(&func) {
            continue;
        }
        result
            .base_pointer_names
            .entry(func)
            .or_default()
            .insert(crate::decompile::passes::c_pass::helpers::param_name_for_reg(rtl));
    }

    result
}

fn rewrite_raw_frame_buffer_addresses(
    body: &CStmt,
    base_pointer_names: &HashSet<String>,
    regions: &[RawFrameBufferRegion],
) -> CStmt {
    fn unwrapped_var(expr: &CExpr) -> Option<&str> {
        match expr {
            CExpr::Var(name) => Some(name),
            CExpr::Cast(_, inner) | CExpr::Paren(inner) => unwrapped_var(inner),
            _ => None,
        }
    }

    fn exact_i64(expr: &CExpr) -> Option<i64> {
        let CExpr::IntLit(literal) = expr else {
            return None;
        };
        i64::try_from(literal.value).ok()
    }

    fn raw_displacement(expr: &CExpr, base_pointer_names: &HashSet<String>) -> Option<i64> {
        let CExpr::Binary(op, lhs, rhs) = expr else {
            return None;
        };
        match op {
            BinaryOp::Add => {
                if unwrapped_var(lhs).is_some_and(|name| base_pointer_names.contains(name)) {
                    return exact_i64(rhs);
                }
                if unwrapped_var(rhs).is_some_and(|name| base_pointer_names.contains(name)) {
                    return exact_i64(lhs);
                }
                None
            }
            BinaryOp::Sub
                if unwrapped_var(lhs).is_some_and(|name| base_pointer_names.contains(name)) =>
            {
                exact_i64(rhs)?.checked_neg()
            }
            _ => None,
        }
    }

    crate::decompile::passes::c_pass::helpers::map_stmt_exprs(body, &|expr| {
        let displacement = raw_displacement(expr, base_pointer_names)?;
        let destinations: BTreeSet<(String, usize)> = regions
            .iter()
            .filter(|region| displacement >= region.start && displacement < region.end)
            .filter_map(|region| {
                displacement
                    .checked_sub(region.start)
                    .and_then(|offset| usize::try_from(offset).ok())
                    .map(|offset| (region.backing.clone(), offset))
            })
            .collect();
        if destinations.len() != 1 {
            return None;
        }
        let (backing, offset) = destinations.into_iter().next().unwrap();
        Some(CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(stack_buffer_alias_byte_expr(&backing, offset)),
        ))
    })
}

fn stack_buffer_alias_value_expr(base: &str, offset: usize, value_ty: &CType) -> CExpr {
    let byte = stack_buffer_alias_byte_expr(base, offset);
    CExpr::Unary(
        UnaryOp::Deref,
        Box::new(CExpr::Cast(
            CType::ptr(value_ty.clone()),
            Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(byte))),
        )),
    )
}

/// Preserve a machine store's own width when several SSA accesses share one
/// byte-backed frame cell.
///
/// A canonical stack local can participate in both a qword initializer and
/// later byte updates.  Choosing one declaration type for that local is
/// necessarily lossy.  The exact raw MOV relation plus its RTL source value
/// instead identifies an individual assignment, allowing only that assignment
/// to use its physical access width.
fn derive_exact_stack_buffer_stores(
    db: &DecompileDB,
    aliases: &StackBufferAliases,
    escaped_buffers: &EscapedStackBufferLayouts,
) -> ExactStackBufferStores {
    let exact_chunks = crate::decompile::passes::clight_pass::exact_stack_store_chunks(db);
    let mut stack_cells: BTreeMap<(Node, RTLReg), BTreeSet<Address>> = BTreeMap::new();
    let mut stack_cell_offsets: BTreeMap<(Address, Node, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    let mut local_offsets: BTreeMap<(Address, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    for &(func, node, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        stack_cells.entry((node, local)).or_default().insert(func);
        stack_cell_offsets
            .entry((func, node, local))
            .or_default()
            .insert(offset);
        local_offsets
            .entry((func, local))
            .or_default()
            .insert(offset);
    }

    let mut candidates: BTreeMap<
        (Address, RTLReg, RTLReg),
        BTreeSet<(RTLReg, usize, MemoryChunk)>,
    > = BTreeMap::new();
    for &(node, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let RTLInst::Iop(Operation::Omove, args, destination) = inst else {
            continue;
        };
        if args.len() != 1 {
            continue;
        }
        let Some(&chunk) = exact_chunks.get(&node) else {
            continue;
        };
        let Some(functions) = stack_cells.get(&(node, *destination)) else {
            continue;
        };
        if functions.len() != 1 {
            continue;
        }
        let func = *functions.first().unwrap();
        let mut coordinates = BTreeSet::new();
        if let Some(&(base, offset)) = aliases
            .get(&func)
            .and_then(|function_aliases| function_aliases.get(destination))
        {
            coordinates.insert((base, offset));
        }
        if let Some(&(base, offset, _)) = escaped_buffers
            .members
            .get(&func)
            .and_then(|members| members.get(destination))
        {
            coordinates.insert((base, offset));
        }
        // A direct initializer can be the only observation at one interior
        // coordinate, so it need not appear in the callee-derived member map.
        // The exact stack offsets of the store and of each proven backing base
        // supply that coordinate without guessing a field layout.
        if let (Some(destination_offsets), Some(function_buffers)) = (
            stack_cell_offsets.get(&(func, node, *destination)),
            escaped_buffers.buffers.get(&func),
        ) {
            let width =
                crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(&chunk) as i64;
            for (&base, &size) in function_buffers {
                let Some(base_offsets) = local_offsets.get(&(func, base)) else {
                    continue;
                };
                let Ok(size) = i64::try_from(size) else {
                    continue;
                };
                for &destination_offset in destination_offsets {
                    for &base_offset in base_offsets {
                        let Some(relative) = destination_offset.checked_sub(base_offset) else {
                            continue;
                        };
                        if relative < 0 || relative.checked_add(width).is_none_or(|end| end > size)
                        {
                            continue;
                        }
                        if let Ok(relative) = usize::try_from(relative) {
                            coordinates.insert((base, relative));
                        }
                    }
                }
            }
        }
        if coordinates.len() != 1 {
            continue;
        }
        let (base, offset) = *coordinates.first().unwrap();
        candidates
            .entry((func, *destination, args[0]))
            .or_default()
            .insert((base, offset, chunk));
    }

    let mut result = ExactStackBufferStores::default();
    for ((func, destination, source), choices) in candidates {
        if choices.len() != 1 {
            continue;
        }
        result
            .entry(func)
            .or_default()
            .insert((destination, source), *choices.first().unwrap());
    }
    result
}

/// Exact physical byte-buffer coordinate of each selected machine stack
/// store, keyed by its owning function and instruction node. This is the
/// node-level view of the same proof used by final C store rewriting, so
/// consumers cannot disagree about which buffer and byte offset a store owns.
pub(crate) fn derive_exact_stack_buffer_store_sites(
    db: &DecompileDB,
) -> HashMap<(Address, Node), (RTLReg, usize)> {
    let aliases = derive_stack_buffer_aliases(db);
    let mut escaped_arrays = derive_escaped_stack_array_layouts(db);
    let escaped_buffers = derive_escaped_stack_buffer_layouts(db, &escaped_arrays);
    remove_buffer_owned_array_layouts(&mut escaped_arrays, &escaped_buffers);
    let stores = derive_exact_stack_buffer_stores(db, &aliases, &escaped_buffers);

    let mut owners: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(function);
    }
    let mut candidates: BTreeMap<(Address, Node), BTreeSet<(RTLReg, usize)>> = BTreeMap::new();
    for &(node, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let RTLInst::Iop(Operation::Omove, args, destination) = inst else {
            continue;
        };
        if args.len() != 1 {
            continue;
        }
        let Some(node_owners) = owners.get(&node) else {
            continue;
        };
        for function in node_owners {
            let Some(&(base, offset, _)) = stores
                .get(function)
                .and_then(|function_stores| function_stores.get(&(*destination, args[0])))
            else {
                continue;
            };
            candidates
                .entry((*function, node))
                .or_default()
                .insert((base, offset));
        }
    }

    candidates
        .into_iter()
        .filter_map(|(site, choices)| {
            (choices.len() == 1).then(|| (site, *choices.first().unwrap()))
        })
        .collect()
}

fn rewrite_exact_stack_buffer_stores(
    body: &CStmt,
    stores: &HashMap<(RTLReg, RTLReg), (RTLReg, usize, MemoryChunk)>,
    model: crate::abi::DataModel,
) -> CStmt {
    fn unwrapped_var(expr: &CExpr) -> Option<&str> {
        match expr {
            CExpr::Var(name) => Some(name),
            CExpr::Cast(_, inner) | CExpr::Paren(inner) => unwrapped_var(inner),
            _ => None,
        }
    }

    let named: HashMap<(String, String), (String, usize, CType)> = stores
        .iter()
        .map(|(&(destination, source), &(base, offset, chunk))| {
            (
                (
                    crate::decompile::passes::c_pass::helpers::param_name_for_reg(destination),
                    crate::decompile::passes::c_pass::helpers::param_name_for_reg(source),
                ),
                (
                    crate::decompile::passes::c_pass::helpers::param_name_for_reg(base),
                    offset,
                    ctype_from_memchunk(&chunk, model),
                ),
            )
        })
        .collect();

    crate::decompile::passes::c_pass::helpers::map_stmt_exprs(body, &|expr| {
        let CExpr::Assign(AssignOp::Assign, lhs, rhs) = expr else {
            return None;
        };
        let CExpr::Var(destination) = lhs.as_ref() else {
            return None;
        };
        let source = unwrapped_var(rhs)?;
        let (base, offset, access_ty) = named.get(&(destination.clone(), source.to_string()))?;
        Some(CExpr::Assign(
            AssignOp::Assign,
            Box::new(stack_buffer_alias_value_expr(base, *offset, access_ty)),
            rhs.clone(),
        ))
    })
}

fn rewrite_stack_buffer_aliases_with_access_types(
    body: &CStmt,
    aliases: &HashMap<RTLReg, (RTLReg, usize)>,
    value_types: &HashMap<String, CType>,
    stack_address_regs: &HashSet<RTLReg>,
    access_types: &HashMap<RTLReg, CType>,
    backing_regs: &HashSet<RTLReg>,
) -> CStmt {
    let alias_names: HashMap<String, (String, usize, Option<CType>, bool, bool)> = aliases
        .iter()
        .map(|(member, (base, offset))| {
            let member_name =
                crate::decompile::passes::c_pass::helpers::param_name_for_reg(*member);
            (
                member_name.clone(),
                (
                    crate::decompile::passes::c_pass::helpers::param_name_for_reg(*base),
                    *offset,
                    access_types
                        .get(member)
                        .cloned()
                        .or_else(|| value_types.get(&member_name).cloned()),
                    stack_address_regs.contains(member),
                    backing_regs.contains(member),
                ),
            )
        })
        .collect();

    fn addrof_var_name(expr: &CExpr) -> Option<&str> {
        match expr {
            CExpr::Cast(_, inner) | CExpr::Paren(inner) => addrof_var_name(inner),
            CExpr::Unary(UnaryOp::AddrOf, inner) => match inner.as_ref() {
                CExpr::Var(name) => Some(name.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    fn storage_coordinate(
        name: &str,
        alias_names: &HashMap<String, (String, usize, Option<CType>, bool, bool)>,
    ) -> (String, usize) {
        alias_names
            .get(name)
            .map(|(base, offset, _, _, _)| (base.clone(), *offset))
            .unwrap_or_else(|| (name.to_string(), 0))
    }

    // This walk is deliberately context-aware. The generic bottom-up mapper
    // replaced an array alias `buffer` with `buffer[0]` before seeing an
    // enclosing pointer cast, turning `(T *)buffer` into `(T *)buffer[0]` and
    // treating the first byte's VALUE as an address. Only an alias whose final
    // declaration is an array receives decay/address semantics in pointer-cast
    // position. A scalar-to-pointer cast remains a scalar value conversion.
    fn rewrite_expr(
        expr: &CExpr,
        alias_names: &HashMap<String, (String, usize, Option<CType>, bool, bool)>,
        pointer_cast_operand: bool,
    ) -> CExpr {
        if let CExpr::Var(name) = expr {
            let Some((base, offset, value_ty, is_stack_address, is_backing)) =
                alias_names.get(name)
            else {
                return expr.clone();
            };
            let byte = stack_buffer_alias_byte_expr(base, *offset);
            if *is_stack_address {
                return CExpr::Unary(UnaryOp::AddrOf, Box::new(byte));
            }
            if pointer_cast_operand && (*is_backing || matches!(value_ty, Some(CType::Array(..)))) {
                return CExpr::Unary(UnaryOp::AddrOf, Box::new(byte));
            }
            let Some(value_ty) = value_ty else {
                return byte;
            };
            if matches!(
                value_ty,
                CType::Void | CType::Function(..) | CType::Array(..)
            ) {
                return byte;
            }
            return stack_buffer_alias_value_expr(base, *offset, value_ty);
        }

        match expr {
            CExpr::Unary(op, inner) => {
                if *op == UnaryOp::AddrOf {
                    if let CExpr::Var(name) = inner.as_ref() {
                        if alias_names
                            .get(name)
                            .is_some_and(|(_, _, _, is_stack_address, _)| *is_stack_address)
                        {
                            return rewrite_expr(inner, alias_names, false);
                        }
                    }
                }
                CExpr::Unary(*op, Box::new(rewrite_expr(inner, alias_names, false)))
            }
            CExpr::Binary(op, lhs, rhs) => CExpr::Binary(
                *op,
                Box::new(rewrite_expr(lhs, alias_names, false)),
                Box::new(rewrite_expr(rhs, alias_names, false)),
            ),
            CExpr::Assign(op, lhs, rhs) => {
                if let CExpr::Var(lhs_name) = lhs.as_ref() {
                    if let Some(rhs_name) = addrof_var_name(rhs) {
                        let participates = alias_names.contains_key(lhs_name)
                            || alias_names.contains_key(rhs_name);
                        if participates
                            && storage_coordinate(lhs_name, alias_names)
                                == storage_coordinate(rhs_name, alias_names)
                        {
                            return CExpr::int(0);
                        }
                    }
                }
                CExpr::Assign(
                    *op,
                    Box::new(rewrite_expr(lhs, alias_names, false)),
                    Box::new(rewrite_expr(rhs, alias_names, false)),
                )
            }
            CExpr::Ternary(cond, then_expr, else_expr) => CExpr::Ternary(
                Box::new(rewrite_expr(cond, alias_names, false)),
                Box::new(rewrite_expr(then_expr, alias_names, false)),
                Box::new(rewrite_expr(else_expr, alias_names, false)),
            ),
            CExpr::Call(callee, args) => CExpr::Call(
                Box::new(rewrite_expr(callee, alias_names, false)),
                args.iter()
                    .map(|arg| rewrite_expr(arg, alias_names, false))
                    .collect(),
            ),
            CExpr::Cast(ty, inner) => CExpr::Cast(
                ty.clone(),
                Box::new(rewrite_expr(inner, alias_names, ty.is_pointer())),
            ),
            CExpr::Member(inner, field) => CExpr::Member(
                Box::new(rewrite_expr(inner, alias_names, false)),
                field.clone(),
            ),
            CExpr::MemberPtr(inner, field) => CExpr::MemberPtr(
                Box::new(rewrite_expr(inner, alias_names, false)),
                field.clone(),
            ),
            CExpr::Index(base, index) => CExpr::Index(
                Box::new(rewrite_expr(base, alias_names, false)),
                Box::new(rewrite_expr(index, alias_names, false)),
            ),
            CExpr::SizeofExpr(inner) => {
                CExpr::SizeofExpr(Box::new(rewrite_expr(inner, alias_names, false)))
            }
            CExpr::Paren(inner) => CExpr::Paren(Box::new(rewrite_expr(
                inner,
                alias_names,
                pointer_cast_operand,
            ))),
            CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
                ty.clone(),
                initializers
                    .iter()
                    .map(|init| rewrite_initializer(init, alias_names))
                    .collect(),
            ),
            CExpr::Generic(selector, arms) => CExpr::Generic(
                Box::new(rewrite_expr(selector, alias_names, false)),
                arms.iter()
                    .map(|(ty, arm)| {
                        (
                            ty.clone(),
                            rewrite_expr(arm, alias_names, pointer_cast_operand),
                        )
                    })
                    .collect(),
            ),
            CExpr::StmtExpr(stmts, tail) => CExpr::StmtExpr(
                stmts
                    .iter()
                    .map(|stmt| {
                        crate::decompile::passes::c_pass::helpers::map_stmt_exprs_total(
                            stmt,
                            &|nested| rewrite_expr(nested, alias_names, false),
                        )
                    })
                    .collect(),
                Box::new(rewrite_expr(tail, alias_names, pointer_cast_operand)),
            ),
            _ => expr.clone(),
        }
    }

    fn rewrite_initializer(
        init: &Initializer,
        alias_names: &HashMap<String, (String, usize, Option<CType>, bool, bool)>,
    ) -> Initializer {
        match init {
            Initializer::Expr(expr) => Initializer::Expr(rewrite_expr(expr, alias_names, false)),
            Initializer::List(items) => Initializer::List(
                items
                    .iter()
                    .map(|item| InitItem {
                        designator: item.designator.as_ref().map(|designator| {
                            transform_designator_exprs(designator, &|expr| {
                                rewrite_expr(expr, alias_names, false)
                            })
                        }),
                        init: rewrite_initializer(&item.init, alias_names),
                    })
                    .collect(),
            ),
            Initializer::String(literal) => Initializer::String(literal.clone()),
        }
    }

    crate::decompile::passes::c_pass::helpers::map_stmt_exprs_total(body, &|expr| {
        rewrite_expr(expr, &alias_names, false)
    })
}

fn rewrite_stack_buffer_aliases(
    body: &CStmt,
    aliases: &HashMap<RTLReg, (RTLReg, usize)>,
    value_types: &HashMap<String, CType>,
    stack_address_regs: &HashSet<RTLReg>,
) -> CStmt {
    rewrite_stack_buffer_aliases_with_access_types(
        body,
        aliases,
        value_types,
        stack_address_regs,
        &HashMap::new(),
        &HashSet::new(),
    )
}

/// Turn a callee-observed, uniform stack region into one C array object.
///
/// RTL proves each field through an exact caller argument -> callee parameter
/// link.  Here we require a complete zero-based constant-stride layout and an
/// exact canonical caller local for every element before coalescing anything.
/// That keeps ordinary by-reference scalars and sparse/struct-like regions as
/// separate locals while restoring C aliasing for genuine inline arrays.
fn derive_escaped_stack_array_layouts(db: &DecompileDB) -> EscapedStackArrayLayouts {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
    use std::collections::BTreeSet;

    let mut slot_locals: BTreeMap<(Address, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(func, _node, ofs, local) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        slot_locals.entry((func, ofs)).or_default().insert(local);
    }

    let mut regions: BTreeMap<(Address, i64), BTreeMap<i64, BTreeSet<MemoryChunk>>> =
        BTreeMap::new();
    for &(func, base_ofs, field_ofs, chunk) in
        db.rel_iter::<(Address, i64, i64, MemoryChunk)>("escaped_stack_region_field")
    {
        if field_ofs < 0 || matches!(chunk, MemoryChunk::Unknown) {
            continue;
        }
        regions
            .entry((func, base_ofs))
            .or_default()
            .entry(field_ofs)
            .or_default()
            .insert(chunk);
    }

    let mut result = EscapedStackArrayLayouts::default();
    for ((func, base_ofs), fields) in regions {
        if fields.len() < 2 || !fields.contains_key(&0) {
            continue;
        }
        let Some(base_local) = slot_locals
            .get(&(func, base_ofs))
            .and_then(|locals| locals.first().copied())
        else {
            continue;
        };
        // A byte backing buffer is a different, more conservative model; do
        // not reinterpret its element indices as wider scalar indices.
        if db
            .stack_struct_buffers
            .get(&func)
            .is_some_and(|buffers| buffers.contains_key(&base_local))
        {
            continue;
        }

        let Some(base_chunks) = fields.get(&0) else {
            continue;
        };
        if base_chunks.len() != 1 || fields.values().any(|chunks| chunks != base_chunks) {
            continue;
        }
        let elem_chunk = *base_chunks.iter().next().unwrap();
        let width = chunk_byte_size(&elem_chunk);
        if width == 0 {
            continue;
        }

        let offsets: Vec<i64> = fields.keys().copied().collect();
        let complete = offsets.iter().enumerate().all(|(idx, ofs)| {
            i64::try_from(idx)
                .ok()
                .and_then(|idx| idx.checked_mul(width as i64))
                == Some(*ofs)
        });
        if !complete {
            continue;
        }

        // One physical element can have several SSA names across its lifetime
        // (an initializer/store name and a later LEA/reload name).  Every one
        // denotes the same array element and must be rewritten, while the
        // deterministic minimum remains the backing declaration owner.
        let mut members = Vec::new();
        let mut complete_members = true;
        for (idx, field_ofs) in offsets.iter().enumerate() {
            let Some(slot_ofs) = base_ofs.checked_add(*field_ofs) else {
                complete_members = false;
                break;
            };
            let Some(locals) = slot_locals.get(&(func, slot_ofs)) else {
                complete_members = false;
                break;
            };
            members.extend(locals.iter().map(|local| (*local, idx)));
        }
        if !complete_members {
            continue;
        }

        if let Some((existing_chunk, _)) = db
            .stack_array_buffers
            .get(&func)
            .and_then(|arrays| arrays.get(&base_local))
        {
            if chunk_byte_size(existing_chunk) != width {
                continue;
            }
        }

        result
            .arrays
            .entry(func)
            .or_default()
            .entry(base_local)
            .and_modify(|(_, count)| *count = (*count).max(offsets.len()))
            .or_insert((elem_chunk, offsets.len()));

        let member_map = result.members.entry(func).or_default();
        for (local, idx) in members {
            let candidate = (base_local, idx);
            member_map
                .entry(local)
                .and_modify(|current| *current = (*current).min(candidate))
                .or_insert(candidate);
        }
    }

    result
}

/// Turn a structurally proven escaped mixed-width region into one byte backing
/// object.  Each canonical scalar local is rewritten as an exact typed lvalue
/// at its observed byte offset, so caller initializers and callee accesses
/// alias the same C storage without inventing a source-level struct.
fn derive_escaped_stack_buffer_layouts(
    db: &DecompileDB,
    array_layouts: &EscapedStackArrayLayouts,
) -> EscapedStackBufferLayouts {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
    use std::collections::BTreeSet;
    use std::ops::Bound;

    let mut base_locals: BTreeMap<(Address, i64), RTLReg> = BTreeMap::new();
    for &(func, ofs, local) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical") {
        base_locals
            .entry((func, ofs))
            .and_modify(|current| *current = (*current).min(local))
            .or_insert(local);
    }

    let mut field_locals: BTreeMap<(Address, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(func, ofs, local) in
        db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_region_canonical")
    {
        field_locals.entry((func, ofs)).or_default().insert(local);
        base_locals
            .entry((func, ofs))
            .and_modify(|current| *current = (*current).min(local))
            .or_insert(local);
    }
    // A stack cell has one address but can have several SSA value versions.
    // Once the exact cell is proven to belong to an escaped region, every
    // version must name that same backing storage in C.
    for &(func, _node, ofs, local) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        field_locals.entry((func, ofs)).or_default().insert(local);
    }

    let mut extents: BTreeMap<(Address, i64), i64> = BTreeMap::new();
    for &(func, base_ofs, extent) in
        db.rel_iter::<(Address, i64, i64)>("escaped_stack_region_extent")
    {
        extents
            .entry((func, base_ofs))
            .and_modify(|current| *current = (*current).max(extent))
            .or_insert(extent);
    }

    // This is the same exact ownership map used when raw stack initializers
    // are moved into the backing object.  Sharing it prevents a write from
    // becoming `buffer[offset]` while the corresponding stack web remains an
    // unrelated scalar local.
    let regions = crate::decompile::passes::clight_pass::escaped_stack_region_owned_fields(db);

    // A byte-backed object can be read at several nested widths from the same
    // offset (packed flags are commonly read as byte and short).  Keep the
    // widest observation as the representative member so every touched byte is
    // reserved; the existing Clight casts retain each individual access width
    // and signedness.  This relaxation is local to final byte-buffer layout --
    // raw immediate-store synthesis keeps its stricter exact-tiling guard.
    let exact_region_fields =
        |fields: &BTreeMap<i64, BTreeSet<MemoryChunk>>| -> Option<Vec<(i64, MemoryChunk, usize)>> {
            let mut exact = Vec::with_capacity(fields.len());
            for (field_ofs, chunks) in fields {
                let Some((chunk, width)) = chunks
                    .iter()
                    .filter_map(|chunk| {
                        let width = chunk_byte_size(chunk);
                        (width > 0).then_some((*chunk, width))
                    })
                    .max_by_key(|(chunk, width)| (*width, *chunk))
                else {
                    return None;
                };
                exact.push((*field_ofs, chunk, width));
            }
            Some(exact)
        };

    let mut result = EscapedStackBufferLayouts::default();
    let region_keys: Vec<(Address, i64)> = regions.keys().copied().collect();
    let mut absorbed: HashSet<(Address, i64)> = HashSet::new();
    for (func, base_ofs) in region_keys {
        if absorbed.contains(&(func, base_ofs)) {
            continue;
        }
        let fields = &regions[&(func, base_ofs)];
        // One field is enough when the frame itself proves the object is larger
        // than that field: an out-parameter the caller never reads back still
        // has to reserve everything the callee writes.
        let extent = extents.get(&(func, base_ofs)).copied();
        if !fields.contains_key(&0) || (fields.len() < 2 && extent.is_none()) {
            continue;
        }
        let Some(&base_local) = base_locals.get(&(func, base_ofs)) else {
            continue;
        };
        if array_layouts
            .arrays
            .get(&func)
            .is_some_and(|arrays| arrays.contains_key(&base_local))
        {
            continue;
        }

        let Some(mut exact_fields) = exact_region_fields(fields) else {
            continue;
        };

        // A region whose base falls strictly inside this one's span shares
        // bytes with it, and two C objects cannot share bytes.  Absorb it: the
        // buffer extends to the enclosed region's far end and the enclosed
        // fields become members at their shifted offsets, so a callee writing
        // through the interior pointer still lands inside this storage.
        // Dropping the enclosed region instead is the stack smash -- its ABI
        // extent (fstatfs's 120-byte statfs at +16 of du's 72-byte-spanning
        // region) was the only statement of those bytes.  Bases ascend inside
        // one function, so a single pass with a growing end is the fixpoint;
        // this is offset arithmetic within one frame, not a reachability order.
        let mut span_end = exact_fields
            .iter()
            .filter_map(|(ofs, _, width)| ofs.checked_add(*width as i64))
            .max()
            .into_iter()
            .chain(extent)
            .max()
            .unwrap_or(0);
        let mut occupied: BTreeSet<i64> = exact_fields.iter().map(|(ofs, _, _)| *ofs).collect();
        let mut absorbed_here: Vec<(Address, i64)> = Vec::new();
        for (&(inner_func, inner_base), inner_fields) in
            regions.range((Bound::Excluded((func, base_ofs)), Bound::Unbounded))
        {
            // span_end is a length; the scan cursor is an absolute frame
            // offset, so the far end must be restated in frame coordinates.
            if inner_func != func || inner_base >= base_ofs.saturating_add(span_end) {
                break;
            }
            if absorbed.contains(&(inner_func, inner_base)) {
                continue;
            }
            let delta = inner_base - base_ofs;
            let mut inner_end = extents
                .get(&(inner_func, inner_base))
                .copied()
                .unwrap_or(0)
                .max(0);
            // An enclosed region whose own offsets carry conflicting widths
            // would not have emitted on its own either; only its extent folds.
            // Where an offset is already occupied the enclosing region's own
            // observation stands, mirroring the callee-over-caller merge above.
            if let Some(inner_exact) = exact_region_fields(inner_fields) {
                for (field_ofs, chunk, width) in inner_exact {
                    if let Some(field_end) = field_ofs.checked_add(width as i64) {
                        inner_end = inner_end.max(field_end);
                    }
                    let Some(shifted) = delta.checked_add(field_ofs) else {
                        continue;
                    };
                    if occupied.insert(shifted) {
                        exact_fields.push((shifted, chunk, width));
                    }
                }
            }
            if let Some(inner_span_end) = delta.checked_add(inner_end) {
                span_end = span_end.max(inner_span_end);
            }
            absorbed_here.push((inner_func, inner_base));
        }

        let size = usize::try_from(span_end)
            .ok()
            .filter(|size| *size > 0 && *size <= 1 << 20);
        let Some(size) = size else {
            continue;
        };

        let mut candidate_members = Vec::new();
        for (field_ofs, chunk, _) in exact_fields {
            let Some(slot_ofs) = base_ofs.checked_add(field_ofs) else {
                continue;
            };
            let Some(locals) = field_locals.get(&(func, slot_ofs)) else {
                // The callee can observe a field that the caller never loads
                // into a scalar SSA value.  It still contributes to backing
                // storage size; there is simply no caller local to rewrite.
                continue;
            };
            for &local in locals {
                candidate_members.push((local, (base_local, field_ofs as usize, chunk)));
            }
        }
        if !candidate_members
            .iter()
            .any(|(local, (_, offset, _))| *offset == 0 && *local == base_local)
        {
            continue;
        }

        let member_map = result.members.entry(func).or_default();
        if candidate_members.iter().any(|(local, candidate)| {
            member_map
                .get(local)
                .is_some_and(|existing| existing != candidate)
        }) {
            continue;
        }
        for (local, candidate) in candidate_members {
            member_map.entry(local).or_insert(candidate);
        }
        result
            .buffers
            .entry(func)
            .or_default()
            .entry(base_local)
            .and_modify(|current| *current = (*current).max(size))
            .or_insert(size);
        // Enclosed regions are consumed only by a buffer that actually
        // emitted; a rejected encloser leaves them to stand on their own.
        absorbed.extend(absorbed_here);
    }

    result
}

/// Give every escaped stack local exactly one C backing object.
///
/// A mixed-width escaped region can contain a uniform subregion (for example,
/// an inline array field inside a larger record).  Deriving both layouts would
/// first rewrite the subregion local as `array[index]`, then rewrite that same
/// array base as a scalar field of the outer byte buffer.  Besides producing
/// invalid C, those two objects would not model the machine-level aliasing.
/// The conservative mixed-width buffer therefore owns the whole overlapping
/// uniform layout whenever either its base or one of its members is already a
/// proven field of that buffer.
fn remove_buffer_owned_array_layouts(
    arrays: &mut EscapedStackArrayLayouts,
    buffers: &EscapedStackBufferLayouts,
) {
    let funcs: Vec<Address> = arrays.members.keys().copied().collect();
    for func in funcs {
        let Some(buffer_members) = buffers.members.get(&func) else {
            continue;
        };
        let Some(array_members) = arrays.members.get(&func) else {
            continue;
        };

        let buffer_owned_bases: HashSet<RTLReg> = array_members
            .iter()
            .filter_map(|(member, (base, _))| {
                (buffer_members.contains_key(member) || buffer_members.contains_key(base))
                    .then_some(*base)
            })
            .collect();
        if buffer_owned_bases.is_empty() {
            continue;
        }

        if let Some(func_arrays) = arrays.arrays.get_mut(&func) {
            func_arrays.retain(|base, _| !buffer_owned_bases.contains(base));
        }
        if let Some(func_members) = arrays.members.get_mut(&func) {
            func_members.retain(|_, (base, _)| !buffer_owned_bases.contains(base));
        }
    }

    arrays.arrays.retain(|_, layouts| !layouts.is_empty());
    arrays.members.retain(|_, layouts| !layouts.is_empty());
}

/// Choose the C storage declaration for each recovered global array owner.
///
/// `is_global_array` describes a possible logical element interpretation;
/// `global_storage_extent` describes physical ownership.  When the two agree
/// exactly, retain the typed element shape.  When they disagree (or the
/// logical stride has no scalar C element type), preserve the exact object as
/// a byte array.  This keeps alternative interpretations from overlapping the
/// next ELF object while still giving every interior address one C owner.
pub(crate) fn recovered_global_array_declarations(
    db: &DecompileDB,
) -> HashMap<Ident, (usize, usize)> {
    let mut logical: HashMap<Ident, (usize, usize)> = HashMap::new();
    for (ident, elem_size, count) in db.rel_iter::<(Ident, usize, usize)>("is_global_array") {
        if *elem_size == 0 || *count == 0 {
            continue;
        }
        let candidate = (*elem_size, *count);
        logical
            .entry(*ident)
            .and_modify(|winner| {
                if winner.0 == candidate.0 {
                    // Every producer publishes a minimum represented extent.
                    // For one agreed element width, the larger count subsumes
                    // the shorter observed prefix; choosing the smaller count
                    // makes indexed accesses run beyond the C declaration.
                    winner.1 = winner.1.max(candidate.1);
                } else {
                    // Preserve the established weakest-type choice when the
                    // logical element interpretations themselves disagree.
                    *winner = (*winner).min(candidate);
                }
            })
            .or_insert(candidate);
    }

    let mut extent_candidates: HashMap<Ident, BTreeSet<usize>> = HashMap::new();
    for (ident, extent) in db.rel_iter::<(Ident, usize)>("global_storage_extent") {
        if *extent > 0 {
            extent_candidates.entry(*ident).or_default().insert(*extent);
        }
    }
    let exact_extents: HashMap<Ident, usize> = extent_candidates
        .into_iter()
        .filter_map(|(ident, extents)| {
            (extents.len() == 1).then(|| (ident, *extents.first().unwrap()))
        })
        .collect();

    let mut owners: BTreeSet<Ident> = logical.keys().copied().collect();
    owners.extend(exact_extents.keys().copied());
    owners
        .into_iter()
        .filter_map(
            |ident| match (logical.get(&ident), exact_extents.get(&ident)) {
                (Some(&(elem_size, count)), Some(&extent))
                    if matches!(elem_size, 1 | 2 | 4 | 8)
                        && elem_size.checked_mul(count) == Some(extent) =>
                {
                    Some((ident, (elem_size, count)))
                }
                (_, Some(&extent)) => Some((ident, (1, extent))),
                (Some(&layout), None) => Some((ident, layout)),
                (None, None) => None,
            },
        )
        .collect()
}

pub fn build_cast_from_relations(
    db: &DecompileDB,
    selected_functions: &[SelectedFunction],
    globals: &[GlobalData],
    id_to_name: &HashMap<usize, String>,
    global_lvalue_aliases: &HashMap<usize, CExpr>,
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
    data_model: crate::abi::DataModel,
) -> TranslationUnit {
    let mut ctx = ConversionContext::new(id_to_name.clone(), data_model);
    ctx.global_lvalue_aliases = global_lvalue_aliases.clone();
    ctx.func_renames = header_collision_policy(selected_functions).renames;
    for global in globals {
        if global.is_string {
            ctx.string_globals.insert(global.id);
        }
    }
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        ctx.string_label_to_content
            .insert(label.clone(), content.clone());
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
        for (_, name) in sorted.iter_mut() {
            if let Some(renamed) = ctx.func_renames.get(name) {
                *name = renamed.clone();
            }
        }
        sorted.sort_by_key(|(addr, _)| *addr);
        ctx.func_addrs_sorted = sorted;
    }

    let mut stmt_map: HashMap<(Address, Node), CStmt> = HashMap::new();
    let mut function_edges = HashMap::new();
    for func in selected_functions {
        ctx.var_types.extend(func.concrete_declarations.iter().map(|(&reg, term)|
            (crate::decompile::passes::c_pass::helpers::param_name_for_reg(reg), term.to_c(ctx.data_model))));
        // func.statements is a HashMap; iterating it directly leaks non-deterministic order into convert_stmt -> record_var_type (which is first-wins), so a variable's recorded C type flips between runs. Walk nodes in sorted order.
        let mut nodes: Vec<crate::x86::types::Node> = func.statements.keys().copied().collect();
        nodes.sort_by_key(|node| exec_order_key(*node));
        for node in nodes {
            let clight_stmt = &func.statements[&node];
            let converted = convert_stmt_at(clight_stmt, &mut ctx, node);
            stmt_map.insert((func.address, node), converted);
        }
        function_edges.insert(func.address, edges.iter().copied().filter(|(from,_)|
            func.successors.contains_key(from) || func.statements.contains_key(from)).collect());
    }

    build_translation_unit_from_stmt_map_with_types(
        db,
        selected_functions,
        globals,
        id_to_name,
        global_lvalue_aliases,
        &stmt_map,
        &function_edges,
        &ctx.var_types,
    )
}

pub fn build_translation_unit_from_stmt_map_with_types(
    db: &DecompileDB,
    selected_functions: &[SelectedFunction],
    globals: &[GlobalData],
    id_to_name: &HashMap<usize, String>,
    global_lvalue_aliases: &HashMap<usize, CExpr>,
    stmt_map: &HashMap<(Address, Node), CStmt>,
    edges: &HashMap<Address, Vec<(Node, Node)>>,
    var_types: &HashMap<String, CType>,
) -> TranslationUnit {
    build_translation_unit_with_variable_origins(db, selected_functions, globals, id_to_name,
        global_lvalue_aliases, stmt_map, edges, var_types).0
}

/// Record the emitter's actual register-to-name mapping without annotating or
/// constraining the C AST. Consumers must look up types in the final C tree;
/// a removed or renamed declaration does not retain credit by provenance alone.
pub fn build_translation_unit_with_variable_origins(
    db: &DecompileDB,
    selected_functions: &[SelectedFunction],
    globals: &[GlobalData],
    id_to_name: &HashMap<usize, String>,
    global_lvalue_aliases: &HashMap<usize, CExpr>,
    stmt_map: &HashMap<(Address, Node), CStmt>,
    edges: &HashMap<Address, Vec<(Node, Node)>>,
    var_types: &HashMap<String, CType>,
) -> (TranslationUnit, Vec<(Address, RTLReg, String, String)>) {
    let mut variable_origins = Vec::new();
    let data_model = db.data_model();
    let mut tu = TranslationUnit::new();
    let mut func_var_types = var_types.clone();

    let dwarf_param_names: HashMap<(Address, usize), String> = db
        .rel_iter::<(Address, usize, Symbol)>("dwarf_func_param_name")
        .map(|&(addr, idx, name)| ((addr, idx), name.to_string()))
        .collect();
    let internal_variadic_functions: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_varargs_fn")
        .map(|&(address,)| address)
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

    let mut known_global_types: HashMap<String, CType> = db
        .rel_iter::<(Symbol, XType)>("known_global_type")
        .map(|(name, xtype)| {
            (
                sanitize_c_symbol_name(name),
                convert_xtype(xtype, data_model),
            )
        })
        .collect();
    for (ident, xtype) in &db.committed_interfaces.globals {
        if let Some(name) = id_to_name.get(ident) {
            known_global_types.insert(
                sanitize_c_symbol_name(name),
                convert_xtype(xtype, data_model),
            );
        }
    }

    // Extern return types from abi_pass for variable type inference at call sites
    let extern_return_types: HashMap<String, CType> = db
        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        .map(|(name, _, ret_type, _)| {
            (
                sanitize_c_symbol_name(name),
                convert_xtype(ret_type, data_model),
            )
        })
        .filter(|(_, ty)| !matches!(ty, CType::Void))
        .collect();

    // Build global load chunk map: prefer integer over float (SSE bulk copies produce spurious floats).
    let global_chunks: HashMap<usize, MemoryChunk> = {
        let mut chunks: HashMap<usize, Vec<MemoryChunk>> = HashMap::new();
        for (id, chunk) in db.rel_iter::<(Ident, MemoryChunk)>("global_load_chunk") {
            chunks.entry(*id).or_default().push(*chunk);
        }
        chunks
            .into_iter()
            .map(|(id, mut chunk_list)| {
                // Filter out generic MAny/Unknown when specific chunks exist
                let has_specific = chunk_list.iter().any(|c| {
                    !matches!(
                        c,
                        MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown
                    )
                });
                if has_specific {
                    chunk_list.retain(|c| {
                        !matches!(
                            c,
                            MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown
                        )
                    });
                }
                // Filter out float chunks when integer chunks exist (SSE bulk copies produce MFloat64)
                let has_int = chunk_list.iter().any(|c| {
                    matches!(
                        c,
                        MemoryChunk::MBool
                            | MemoryChunk::MInt8Signed
                            | MemoryChunk::MInt8Unsigned
                            | MemoryChunk::MInt16Signed
                            | MemoryChunk::MInt16Unsigned
                            | MemoryChunk::MInt32
                            | MemoryChunk::MInt64
                    )
                });
                if has_int {
                    chunk_list
                        .retain(|c| !matches!(c, MemoryChunk::MFloat32 | MemoryChunk::MFloat64));
                }
                // Among remaining, prefer the largest integer type; use the chunk itself as a tiebreak so signed/unsigned pairs of the same width don't flip across parallel-Ascent runs.
                let best = chunk_list
                    .iter()
                    .max_by_key(|c| {
                        (
                            match c {
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
                            },
                            **c,
                        )
                    })
                    .copied()
                    .unwrap_or(MemoryChunk::Unknown);
                (id, best)
            })
            .collect()
    };

    // Rodata FP constants recovered from the binary (address, width, raw IEEE-754 bits), keyed by address so an unnamed .rodata slot emits a typed static const instead of a zeroed long.
    let rodata_fp_consts: HashMap<u64, (usize, u64)> = db
        .rel_iter::<(u64, usize, u64)>("rodata_fp_const")
        .map(|(addr, width, bits)| (*addr, (*width, *bits)))
        .collect();
    // Build a static const double/float VarDecl for a recovered rodata FP constant, or None for a non-finite bit pattern, which is more likely a misclassified bitmask.
    let make_rodata_fp_decl =
        |name: String,
         width: usize,
         bits: u64|
         -> Option<crate::decompile::passes::c_pass::types::TopLevelDecl> {
            use crate::decompile::passes::c_pass::types::{
                FloatLiteral, Initializer, TopLevelDecl,
            };
            let (ty, value, suffix) = if width == 4 {
                (
                    CType::float(),
                    f32::from_bits(bits as u32) as f64,
                    FloatLiteralSuffix::F,
                )
            } else {
                (
                    CType::double(),
                    f64::from_bits(bits),
                    FloatLiteralSuffix::None,
                )
            };
            if !value.is_finite() {
                return None;
            }
            Some(TopLevelDecl::VarDecl(VarDecl {
                name,
                ty,
                storage_class: StorageClass::Static,
                qualifiers: TypeQualifiers {
                    is_const: true,
                    ..TypeQualifiers::none()
                },
                alignment: None,
                storage_views: Vec::new(),
                type_committed: false,
                init: Some(Initializer::Expr(CExpr::FloatLit(FloatLiteral {
                    value,
                    suffix,
                }))),
                loc: SourceLoc::unknown(),
            }))
        };

    // Build global pointer sets from rtl_pass analysis
    let global_ptr_ids: HashSet<usize> = db
        .rel_iter::<(Ident,)>("emit_global_is_ptr")
        .map(|(id,)| *id)
        .collect();
    let global_char_ptr_ids: HashSet<usize> = db
        .rel_iter::<(Ident,)>("emit_global_is_char_ptr")
        .map(|(id,)| *id)
        .collect();

    // SR-1: type global declarations from recovered layouts so emit_global_struct_fields keeps the struct definition alive through clight_emit's referenced-filter; catalog guard prevents naming a struct that extract_struct_definitions won't emit (incomplete type at TU end).
    let (global_struct_decl_ids, global_struct_decl_layouts) =
        extract_global_struct_decl_layouts(db);
    let global_aggregate_coalescing =
        derive_global_aggregate_coalescing(db, globals, &global_struct_decl_layouts);
    let global_array_decl = recovered_global_array_declarations(db);
    let ctype_of_chunk = |chunk: &MemoryChunk| -> CType {
        match chunk {
            // c26: MBool is a 1-byte store; emit _Bool rather than widening to a 4-byte int. _Bool is the true storage type and is consistent with the 1-byte chunk_byte_size used for array elements.
            MemoryChunk::MBool => CType::Bool,
            MemoryChunk::MInt32 | MemoryChunk::MAny32 => CType::Int(
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
            MemoryChunk::MFloat32 => {
                CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Float)
            }
            MemoryChunk::MFloat64 => {
                CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Double)
            }
            _ => CType::long(),
        }
    };
    let chunk_byte_size = |chunk: &MemoryChunk| -> usize {
        match chunk {
            MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
            MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
            MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
            MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
            MemoryChunk::Unknown => 0,
        }
    };

    // c26: ELF symbol storage size per global, keyed by id since a global's id IS its address; multi-valued, so keep the smallest as the tightest deterministic upper bound.
    let global_sym_size: HashMap<usize, usize> = {
        let mut m: HashMap<usize, usize> = HashMap::new();
        for (addr, size, _name) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
            if *size == 0 {
                continue;
            }
            m.entry(*addr as usize)
                .and_modify(|e| {
                    if *size < *e {
                        *e = *size;
                    }
                })
                .or_insert(*size);
        }
        m
    };
    // c26: smallest recorded load/store chunk per global, the narrowest width actually touched, preferred over global_chunks' LARGEST pick which promotes a 1-byte global to long.
    let global_narrow_chunk: HashMap<usize, MemoryChunk> = {
        let mut groups: HashMap<usize, Vec<MemoryChunk>> = HashMap::new();
        for (id, chunk) in db.rel_iter::<(Ident, MemoryChunk)>("global_load_chunk") {
            groups.entry(*id).or_default().push(*chunk);
        }
        groups
            .into_iter()
            .map(|(id, mut chunks)| {
                let has_specific = chunks.iter().any(|c| {
                    !matches!(
                        c,
                        MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown
                    )
                });
                if has_specific {
                    chunks.retain(|c| {
                        !matches!(
                            c,
                            MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown
                        )
                    });
                }
                chunks.sort();
                (id, chunks[0])
            })
            .collect()
    };
    // c26: scalar global type, with st_size authoritative when it is a clean scalar size, else the narrowest recorded chunk and then long; recovers a 1-byte char global instead of widening.
    let scalar_global_ctype = |id: usize| -> CType {
        let narrow = global_narrow_chunk.get(&id).copied();
        if let Some(&size) = global_sym_size.get(&id) {
            if matches!(size, 1 | 2 | 4 | 8) {
                if let Some(chunk) = narrow {
                    if chunk_byte_size(&chunk) == size {
                        return ctype_of_chunk(&chunk);
                    }
                }
                return match size {
                    1 => CType::char_unsigned(),
                    2 => CType::Int(
                        crate::decompile::passes::c_pass::types::IntSize::Short,
                        crate::decompile::passes::c_pass::types::Signedness::Signed,
                    ),
                    4 => CType::int(),
                    _ => CType::long(),
                };
            }
        }
        match narrow {
            Some(chunk) => ctype_of_chunk(&chunk),
            None => CType::long(),
        }
    };

    // Initialized image bytes belong to the recovered object owner.  When an
    // array base is introduced only because code referenced interior cells,
    // omitting this initializer creates correctly shaped but zero-filled
    // storage.  Materialize integer arrays from one unambiguous retained image
    // range; relocations are excluded because their runtime value needs the
    // separate relocation-aware initializer path.
    let initialized_ranges: Vec<(Address, Arc<Vec<u8>>)> = db
        .rel_iter::<(Address, Arc<Vec<u8>>)>("retained_initialized_data_range")
        .map(|(start, bytes)| (*start, bytes.clone()))
        .collect();
    let relocation_slots: Vec<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, _)| *slot)
        .collect();
    let pointer_width = db.abi().pointer_size as Address;
    let initialized_array_initializer =
        |id: usize, elem_size: usize, count: usize, elem_ty: &CType| {
            use crate::decompile::passes::c_pass::types::{Designator, InitItem, Initializer};
            if !matches!(elem_size, 1 | 2 | 4 | 8) || count == 0 {
                return None;
            }
            let start = id as Address;
            let extent = elem_size.checked_mul(count)?;
            let end = start.checked_add(Address::try_from(extent).ok()?)?;
            if relocation_slots.iter().any(|slot| {
                let slot_end = slot.saturating_add(pointer_width);
                *slot < end && slot_end > start
            }) {
                return None;
            }
            let mut ranges = initialized_ranges.iter().filter(|(range_start, bytes)| {
                start >= *range_start
                    && end
                        <= range_start
                            .saturating_add(Address::try_from(bytes.len()).unwrap_or(Address::MAX))
            });
            let (range_start, bytes) = ranges.next()?;
            if ranges.next().is_some() {
                return None;
            }
            let offset = usize::try_from(start - *range_start).ok()?;
            let image = bytes.get(offset..offset.checked_add(extent)?)?;
            let (signed, boolean) = match elem_ty {
                CType::Int(_, Signedness::Signed) => (true, false),
                CType::Int(_, Signedness::Unsigned) => (false, false),
                CType::Bool => (false, true),
                _ => return None,
            };
            let mut items = Vec::new();
            for index in 0..count {
                let begin = index.checked_mul(elem_size)?;
                let raw = image[begin..begin + elem_size]
                    .iter()
                    .enumerate()
                    .fold(0_u64, |word, (byte_index, byte)| {
                        word | ((*byte as u64) << (byte_index * 8))
                    });
                if raw == 0 {
                    continue;
                }
                if boolean && raw != 1 {
                    return None;
                }
                let value = if signed {
                    match elem_size {
                        1 => raw as u8 as i8 as i128,
                        2 => raw as u16 as i16 as i128,
                        4 => raw as u32 as i32 as i128,
                        _ => raw as i64 as i128,
                    }
                } else {
                    raw as i128
                };
                let suffix = match (signed, elem_size) {
                    (true, 8) => IntLiteralSuffix::L,
                    (false, 8) => IntLiteralSuffix::ULL,
                    (false, 4) => IntLiteralSuffix::U,
                    _ => IntLiteralSuffix::None,
                };
                items.push(InitItem {
                    designator: Some(Designator::Index(CExpr::int(index as i64))),
                    init: Initializer::Expr(CExpr::IntLit(IntLiteral {
                        value,
                        suffix,
                        base: IntLiteralBase::Decimal,
                    })),
                });
            }
            (!items.is_empty()).then_some(Initializer::List(items))
        };

    // Names the emitted functions write or address-take, used to keep a data global defined rather than extern only when this TU owns its storage.
    let mutated_globals: HashSet<String> = {
        let mut m = HashSet::new();
        for stmt in stmt_map.values() {
            collect_mutated_names_in_stmt(stmt, &mut m);
        }
        m
    };

    for global in order_globals_for_aggregate_initializers(globals, &global_aggregate_coalescing) {
        // String literals emit separately. A read-only scalar can be folded
        // only when it is not also the proven owner of recovered aggregate
        // storage: interior aliases require that one owner declaration and
        // its image initializer to remain materialized.
        let is_recovered_aggregate_owner =
            global_aggregate_coalescing.owner_ids.contains(&global.id)
                || global_struct_decl_ids.contains_key(&global.id)
                || global_array_decl.contains_key(&global.id);
        // An interior identifier is an lvalue coordinate in its owner's
        // storage, not a separately allocated C object. Its expression uses
        // the owner declaration emitted below. Aggregate owners may also have
        // an offset-zero alias so scalar accesses at their base retain the
        // access's Clight type; that alias must never suppress the declaration
        // which provides the storage.
        if global_lvalue_aliases.contains_key(&global.id) && !is_recovered_aggregate_owner {
            continue;
        }
        if global.is_string
            || (global.scalar_value.is_some()
                && !global.scalar_writable
                && !is_recovered_aggregate_owner)
        {
            continue;
        }
        // A recovered rodata FP constant reaches here with no scalar_value, so emit a typed static const with the real bits instead of a loader-zeroed long L_<addr>.
        if !is_recovered_aggregate_owner {
            if let Some(addr) = global
                .name
                .strip_prefix("L_")
                .and_then(|h| u64::from_str_radix(h, 16).ok())
            {
                if let Some(&(width, bits)) = rodata_fp_consts.get(&addr) {
                    if let Some(decl) =
                        make_rodata_fp_decl(sanitize_c_symbol_name(&global.name), width, bits)
                    {
                        tu.decls.push(decl);
                        continue;
                    }
                }
            }
        }
        let sanitized_name = sanitize_c_symbol_name(&global.name);
        // stdin/stdout/stderr are declared by <stdio.h>; emitting our own definition would conflict with the header and shadow libc's real FILE*.
        if is_libc_stdio_global(&global.name) {
            continue;
        }
        let (ty, init) = if global_aggregate_coalescing.owner_ids.contains(&global.id) {
            let Some((sid, _)) = global_struct_decl_layouts.get(&global.id) else {
                continue;
            };
            (
                CType::Struct(format!("struct_{:x}", sid)),
                global_aggregate_coalescing
                    .owner_initializers
                    .get(&global.id)
                    .cloned(),
            )
        } else if !global.pointer_init.is_empty() {
            // Relocated pointer-valued global from ELF ground truth: a single slot is a scalar void*, a run is a pointer table emitted as long name[N] = {...} so the runtime bytes are reconstructed.
            use crate::decompile::passes::c_pass::types::{InitItem, Initializer};
            if global.pointer_init.len() == 1 {
                let e = global.pointer_init[0].clone();
                let init_expr = CExpr::Cast(CType::ptr(CType::Void), Box::new(e));
                (CType::ptr(CType::Void), Some(Initializer::Expr(init_expr)))
            } else {
                let items: Vec<InitItem> = global
                    .pointer_init
                    .iter()
                    .map(|e| InitItem {
                        designator: None,
                        init: Initializer::Expr(CExpr::Cast(CType::long(), Box::new(e.clone()))),
                    })
                    .collect();
                (
                    CType::Array(Box::new(CType::long()), Some(global.pointer_init.len())),
                    Some(Initializer::List(items)),
                )
            }
        } else if let Some(scalar) = global
            .scalar_value
            .as_ref()
            .filter(|_| global.scalar_writable)
        {
            // Writable initialized scalar global: width from the narrowest recorded chunk or ELF symbol size, initializer from the .data bytes, declared here so runtime stores are preserved.
            (
                scalar_global_ctype(global.id),
                Some(crate::decompile::passes::c_pass::types::Initializer::Expr(
                    scalar.to_cexpr(),
                )),
            )
        } else if let Some(known_ty) = known_global_types.get(&sanitized_name) {
            (known_ty.clone(), None)
        } else if let Some(&sid) = global_struct_decl_ids.get(&global.id) {
            // SR-1: naming the struct on the declaration keeps the definition alive through the referenced/needs_layout filter; use-site compatibility is handled by clight_emit's recovered-global rewrite.
            (CType::Struct(format!("struct_{:x}", sid)), None)
        } else if let Some(&(elem_size, count)) = global_array_decl.get(&global.id) {
            // SR-1: non-scalar strides (e.g. 12-byte struct elements) have no honest scalar element type, so declare the full extent as a byte array rather than an undersized `int name[count]` that would let a recompile overlap the following symbol.
            let (elem_ty, decl_count, emitted_elem_size) = match elem_size {
                1 | 2 | 4 | 8 => {
                    let elem_ty = match global_chunks.get(&global.id) {
                        Some(chunk) if chunk_byte_size(chunk) == elem_size => ctype_of_chunk(chunk),
                        _ => match elem_size {
                            1 => CType::Int(
                                crate::decompile::passes::c_pass::types::IntSize::Char,
                                crate::decompile::passes::c_pass::types::Signedness::Unsigned,
                            ),
                            2 => CType::Int(
                                crate::decompile::passes::c_pass::types::IntSize::Short,
                                crate::decompile::passes::c_pass::types::Signedness::Signed,
                            ),
                            8 => CType::long(),
                            _ => CType::int(),
                        },
                    };
                    (elem_ty, count, elem_size)
                }
                _ => (
                    CType::Int(
                        crate::decompile::passes::c_pass::types::IntSize::Char,
                        crate::decompile::passes::c_pass::types::Signedness::Unsigned,
                    ),
                    elem_size * count,
                    1,
                ),
            };
            let init =
                initialized_array_initializer(global.id, emitted_elem_size, decl_count, &elem_ty);
            (CType::Array(Box::new(elem_ty), Some(decl_count)), init)
        } else if global_char_ptr_ids.contains(&global.id) {
            (
                CType::Pointer(
                    Box::new(CType::Int(
                        crate::decompile::passes::c_pass::types::IntSize::Char,
                        crate::decompile::passes::c_pass::types::Signedness::Signed,
                    )),
                    TypeQualifiers::none(),
                ),
                None,
            )
        } else if global.is_pointer || global_ptr_ids.contains(&global.id) {
            (CType::ptr(CType::Void), None)
        } else {
            // c26: scalar global. Width comes from st_size / the narrowest recorded chunk (scalar_global_ctype), not the widened global_chunks pick, so a 1-byte global stays _Bool/char instead of becoming int/long.
            (scalar_global_ctype(global.id), None)
        };

        // A header-declared global VARIABLE must use the header's canonical type, since the declaration cannot be suppressed and any mismatch is a hard error; initialized data keeps the recovered type.
        let ty = match crate::decompile::passes::c_pass::header_db::header_db()
            .variables
            .get(sanitized_name.as_str())
        {
            Some(spelling) if init.is_none() => {
                parse_canonical_var_type(spelling, data_model).unwrap_or(ty)
            }
            _ => ty,
        };

        // A content-less scalar this TU only reads is emitted extern ONLY when a linked library actually defines it (curated gnulib/CRT globals or real-named libc globals); everything else keeps its own definition.
        let is_lib = db.is_lib_global(&global.name)
            || (uses_real_libc_name(&sanitized_name) && !is_libc_stdio_global(&sanitized_name));
        let (storage_class, init) = if is_lib {
            (StorageClass::Extern, None)
        } else {
            (StorageClass::default(), init)
        };
        let init = init.map(|initializer| {
            rewrite_global_interior_initializer(
                &initializer,
                &global_aggregate_coalescing.member_exprs,
            )
        });
        tu.add_global_var(VarDecl {
            name: sanitized_name,
            ty,
            storage_class,
            qualifiers: TypeQualifiers::none(),
            alignment: None,
            storage_views: Vec::new(),
            type_committed: false,
            init,
            loc: SourceLoc::unknown(),
        });
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

    let local_def_policy = header_collision_policy(selected_functions);
    let func_renames = &local_def_policy.renames;
    let (escaped_stack_arrays, escaped_stack_buffers) = escaped_stack_layouts(db);
    let stack_buffer_aliases = derive_stack_buffer_aliases(db);
    let mut absorbed_buffer_roots: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
    for &(func, root) in db.rel_iter::<(Address, RTLReg)>("stack_buffer_address_root") {
        absorbed_buffer_roots.entry(func).or_default().insert(root);
    }
    let stack_buffer_end_aliases = derive_stack_buffer_end_aliases(db);
    let stack_address_regs: HashSet<RTLReg> = db
        .rel_iter::<(Node, RTLInst)>("rtl_inst")
        .filter_map(|(_, inst)| match inst {
            RTLInst::Iop(
                Operation::Olea(Addressing::Ainstack(_))
                | Operation::Oleal(Addressing::Ainstack(_)),
                args,
                destination,
            ) if args.is_empty() => Some(*destination),
            _ => None,
        })
        .collect();
    let exact_stack_buffer_stores =
        derive_exact_stack_buffer_stores(db, &stack_buffer_aliases, &escaped_stack_buffers);
    let raw_frame_buffers = derive_raw_frame_buffer_layouts(db);

    // Loop-structure facts for top-level ordering, keyed by synth-masked header to member addresses, keeping a rotated loop's body contiguous and ahead of its exit instead of address tie-breaking.
    // loop_members must be keyed through the SAME normalization order_nodes_dfs uses (sseq-head resolve then synth-mask), or a header folded into an sseq bundle reads as loop-free and its body orders after its exit.
    let order_sseq_member_to_head: HashMap<crate::x86::types::Node, crate::x86::types::Node> = {
        let mut m: HashMap<crate::x86::types::Node, crate::x86::types::Node> = HashMap::new();
        for f in selected_functions {
            for (&head, members) in &f.sseq_groups {
                for &mem in members {
                    if mem != head {
                        if let Some(existing) = m.insert(mem, head) {
                            assert_eq!(
                                existing, head,
                                "applied straight-line groups overlap at node {mem:#x}"
                            );
                        }
                    }
                }
            }
        }
        m
    };
    let norm_order_id = |n: crate::x86::types::Node| -> crate::x86::types::Node {
        semantic_node_address(order_sseq_member_to_head.get(&n).copied().unwrap_or(n))
    };
    let loop_members: HashMap<crate::x86::types::Node, HashSet<crate::x86::types::Node>> = {
        let mut m: HashMap<crate::x86::types::Node, HashSet<crate::x86::types::Node>> =
            HashMap::new();
        for (_func, header, member) in db.rel_iter::<(Address, Node, Node)>("loop_body") {
            let h = norm_order_id(*header);
            let mem = norm_order_id(*member);
            m.entry(h).or_default().insert(mem);
        }
        m
    };
    // Innermost natural loop per normalized node, memoized once from loop_members (smallest body, ties on header address), turning order_nodes_dfs's per-node rescan into an O(1) lookup.
    let node_innermost_loop: HashMap<crate::x86::types::Node, crate::x86::types::Node> = {
        let mut best: HashMap<crate::x86::types::Node, (usize, crate::x86::types::Node)> =
            HashMap::new();
        for (header, members) in &loop_members {
            let cand = (members.len(), *header);
            for &node in members {
                best.entry(node)
                    .and_modify(|cur| {
                        if cand < *cur {
                            *cur = cand;
                        }
                    })
                    .or_insert(cand);
            }
        }
        best.into_iter()
            .map(|(node, (_, header))| (node, header))
            .collect()
    };

    let mut emitted_func_names: HashSet<String> = HashSet::new();
    for func in selected_functions {
        let params: Vec<FuncParam> = func
            .param_regs
            .iter()
            .zip(func.param_types.iter())
            .map(|(reg, pty)| {
                let name = param_name_for_reg(*reg);
                FuncParam::named(name, convert_param_type_from_param(pty, data_model))
            })
            .collect();

        let param_name_set: HashSet<String> =
            params.iter().filter_map(|p| p.name.clone()).collect();

        let func_addr = func.address;

        // One machine node can belong to several functions, with different
        // selected types, structure worlds and occurrence identities. Never
        // let a program-wide node map overwrite one owner's selected body.
        let statements: HashMap<Node, &CStmt> = stmt_map.iter()
            .filter_map(|(&(owner,node),statement)| (owner==func_addr).then_some((node,statement))).collect();
        let nodes_set: HashSet<_> = statements.keys().copied().collect();
        let function_edges = edges.get(&func_addr).map(Vec::as_slice).unwrap_or(&[]);

        // sseq bundling drops members whose clight_succ edges still point at
        // them, so remap member->synth edges to the live applied anchor.  The
        // query/selection handoff guarantees groups are disjoint.
        let mut sseq_member_to_head: HashMap<crate::x86::types::Node, crate::x86::types::Node> =
            HashMap::new();
        for (&head, members) in &func.sseq_groups {
            for &m in members {
                if m != head {
                    if let Some(existing) = sseq_member_to_head.insert(m, head) {
                        assert_eq!(
                            existing, head,
                            "applied straight-line groups overlap at node {m:#x}"
                        );
                    }
                }
            }
        }
        // Every absorbed member, including tagged synthetic stores, is absent
        // from the top-level statement map.  Normalize BOTH endpoints to the
        // live Sseq anchor so an edge leaving the last absorbed member still
        // orders the anchor before its external successor.
        let mut remapped_edges = remap_sseq_edges(function_edges, &sseq_member_to_head);

        let entry_node = func.entry_node;
        // Normalize a top-level node id to the address loop_body is keyed by: resolve an sseq member to its bundle head, then mask both synthetic-address bits so synth nodes land on their base.
        let order_normalize = |n: crate::x86::types::Node| -> crate::x86::types::Node {
            let resolved = sseq_member_to_head.get(&n).copied().unwrap_or(n);
            semantic_node_address(resolved)
        };
        redirect_structured_loop_entry_edges(
            entry_node,
            &func.statements,
            &nodes_set,
            &mut remapped_edges,
            &loop_members,
            order_normalize,
        );
        remapped_edges.extend(structured_goto_order_edges(&func.statements, &nodes_set));
        remapped_edges.sort_unstable();
        remapped_edges.dedup();
        let dump_emit_order = std::env::var("CF3_DUMP")
            .ok()
            .and_then(|want| u64::from_str_radix(want.trim_start_matches("0x"), 16).ok())
            == Some(func.address);
        if dump_emit_order {
            let mut selected_nodes: Vec<_> = nodes_set.iter().copied().collect();
            selected_nodes.sort_unstable();
            eprintln!("[DUMP-EMIT] nodes_set={selected_nodes:x?}");
            let mut groups: Vec<_> = func
                .sseq_groups
                .iter()
                .map(|(&head, members)| {
                    let mut members = members.clone();
                    members.sort_unstable();
                    (head, members)
                })
                .collect();
            groups.sort_unstable();
            eprintln!("[DUMP-EMIT] sseq_groups={groups:x?}");
            eprintln!("[DUMP-EMIT] remapped_edges={remapped_edges:x?}");
        }
        let nodes = order_nodes_dfs(
            entry_node,
            &nodes_set,
            &remapped_edges,
            |n| statements.get(&n).is_some_and(|s|is_unconditional_exit(s)),
            &loop_members,
            &node_innermost_loop,
            order_normalize,
        );
        if dump_emit_order {
            eprintln!("[DUMP-EMIT] ordered_nodes={nodes:x?}");
            for &node in &nodes {
                if let Some(&stmt) = statements.get(&node) {
                    eprintln!("[DUMP-EMIT] node {node:x}: {stmt:?}");
                }
            }
        }
        let mut body_items = Vec::new();
        let mut body_terminated = false;
        for &node in &nodes {
            if let Some(&stmt) = statements.get(&node) {
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

        let expected_stmts = func.statements.len();
        let actual_leaf_count = count_leaf_stmts_in_block(&body_items);
        let is_incomplete =
            body_items.is_empty() || (expected_stmts > 4 && actual_leaf_count * 2 < expected_stmts);
        if is_incomplete {
            let covered_nodes: HashSet<crate::x86::types::Node> = nodes.iter().copied().collect();

            let mut fb_ctx = ConversionContext::new(id_to_name.clone(), data_model);
            fb_ctx.func_renames = local_def_policy.renames.clone();
            {
                let mut addr_name_map: HashMap<u64, String> = HashMap::new();
                for (addr, name, _entry_node) in
                    db.rel_iter::<(Address, Symbol, Node)>("emit_function")
                {
                    addr_name_map.insert(*addr as u64, sanitize_c_symbol_name(name));
                }
                for f in selected_functions {
                    addr_name_map.insert(f.address as u64, sanitize_c_symbol_name(&f.name));
                }
                let mut sorted: Vec<(u64, String)> = addr_name_map.into_iter().collect();
                for (_, name) in sorted.iter_mut() {
                    if let Some(renamed) = func_renames.get(name) {
                        *name = renamed.clone();
                    }
                }
                sorted.sort_by_key(|(addr, _)| *addr);
                fb_ctx.func_addrs_sorted = sorted;
            }
            let mut fb_nodes: Vec<_> = func
                .statements
                .keys()
                .copied()
                .filter(|n| !covered_nodes.contains(n))
                .collect();
            fb_nodes.sort_by_key(|node| exec_order_key(*node));
            for node in fb_nodes {
                if let Some(cl_stmt) = func.statements.get(&node) {
                    let cstmt = convert_stmt_at(cl_stmt, &mut fb_ctx, node);
                    let cstmt =
                        crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                            crate::decompile::passes::c_pass::helpers::inline_string_literals(
                                e,
                                &string_map,
                            )
                        });
                    let cstmt = strip_trivial_casts(&cstmt, &fb_ctx.var_types);
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
        body = eliminate_dead_code_preserving_section_labels(&body);

        simplify_xor_self_in_stmt(&mut body);
        strip_dead_expr_stmts(&mut body);

        // Interior image labels admitted by the exact aggregate coalescer are
        // coordinates in their owner's storage, not independent C variables.
        // Rewrite value and address uses before local inference so `L_base.f`
        // participates with its real field type throughout later cleanup.
        if !global_aggregate_coalescing.member_exprs.is_empty() {
            body = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&body, &|expr| {
                let CExpr::Var(name) = expr else {
                    return None;
                };
                global_aggregate_coalescing.member_exprs.get(name).cloned()
            });
        }

        // Per-function local variable types seeded from clight_select's refined candidates, built BEFORE strip_trivial_casts so a (long)float_var is not reduced to a bare float under a pointer cast.
        let mut local_var_types = func_var_types.clone();
        let concrete_declarations: HashMap<_, _> = func.concrete_declarations.iter()
            .map(|(&reg, term)| (crate::decompile::passes::c_pass::helpers::param_name_for_reg(reg), term.to_c(data_model)))
            .collect();
        let committed_names: HashSet<_> = concrete_declarations.keys().cloned().collect();
        for (reg, candidates) in &func.var_type_candidates {
            let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
            if let Some(type_str) = candidates.get(idx).or_else(|| func.var_types.get(reg)) {
                let var_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
                let ctype = crate::decompile::passes::c_pass::helpers::candtype_to_ctype(
                    *type_str, data_model,
                );
                local_var_types.insert(var_name, ctype);
            }
        }
        local_var_types.extend(concrete_declarations.iter().map(|(name, ty)| (name.clone(), ty.clone())));

        let function_stack_buffer_aliases = stack_buffer_aliases.get(&func.address);
        let stack_buffer_alias_names: HashSet<String> = function_stack_buffer_aliases
            .into_iter()
            .flat_map(|aliases| aliases.keys())
            .map(|member| crate::decompile::passes::c_pass::helpers::param_name_for_reg(*member))
            .collect();
        if let Some(stores) = exact_stack_buffer_stores.get(&func.address) {
            body = rewrite_exact_stack_buffer_stores(&body, stores, data_model);
        }

        // Every canonical local in a proven escaped uniform region denotes an
        // element of one C array object.  Rewrite before type inference so
        // assignments, reads, and address-taking all share that storage.
        if let Some(members) = escaped_stack_arrays.members.get(&func.address) {
            let member_names: HashMap<String, (String, usize)> = members
                .iter()
                .map(|(member, (base, index))| {
                    (
                        crate::decompile::passes::c_pass::helpers::param_name_for_reg(*member),
                        (
                            crate::decompile::passes::c_pass::helpers::param_name_for_reg(*base),
                            *index,
                        ),
                    )
                })
                .collect();
            body = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&body, &|expr| {
                let CExpr::Var(name) = expr else {
                    return None;
                };
                // The frame-layout alias below is more specific: it maps this
                // root into the backing object's byte coordinate system.  Let
                // it survive this generic escaped-array rewrite.
                if stack_buffer_alias_names.contains(name) {
                    return None;
                }
                let (base, index) = member_names.get(name)?;
                Some(CExpr::Index(
                    Box::new(CExpr::Var(base.clone())),
                    Box::new(CExpr::int(*index as i64)),
                ))
            });
        }
        if let Some(arrays) = escaped_stack_arrays.arrays.get(&func.address) {
            for (base, (chunk, count)) in arrays {
                let name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*base);
                local_var_types.insert(
                    name,
                    CType::Array(Box::new(ctype_from_memchunk(chunk, data_model)), Some(*count)),
                );
            }
        }

        // Mixed-width escaped regions use one byte buffer.  Install the final
        // backing types before the context-aware alias walk: a backing name in
        // pointer position denotes the array address, while a direct field
        // access retains the member's own exact scalar type.
        if let Some(buffers) = escaped_stack_buffers.buffers.get(&func.address) {
            for (base, size) in buffers {
                let name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*base);
                local_var_types.insert(
                    name,
                    CType::Array(Box::new(CType::char_unsigned()), Some(*size)),
                );
            }
        }
        if let Some(members) = escaped_stack_buffers.members.get(&func.address) {
            let aliases: HashMap<RTLReg, (RTLReg, usize)> = members
                .iter()
                .map(|(member, (base, offset, _))| (*member, (*base, *offset)))
                .collect();
            let access_types: HashMap<RTLReg, CType> = members
                .iter()
                .map(|(member, (_, _, chunk))| (*member, ctype_from_memchunk(chunk, data_model)))
                .collect();
            let mut backing_regs: HashSet<RTLReg> = escaped_stack_buffers
                .buffers
                .get(&func.address)
                .into_iter()
                .flat_map(|buffers| buffers.keys().copied())
                .collect();
            backing_regs.extend(absorbed_buffer_roots.get(&func.address).into_iter().flatten().copied());
            body = rewrite_stack_buffer_aliases_with_access_types(
                &body,
                &aliases,
                &local_var_types,
                &stack_address_regs,
                &access_types,
                &backing_regs,
            );
        }
        // These backing objects are final declarations, not an inference
        // guess.  Publish their array types before alias rewriting so a base
        // used under a pointer cast decays to its storage address rather than
        // being read as an offset-zero scalar value.
        apply_stack_struct_buffer_types(db, func.address, &mut local_var_types);

        // An indexed stack anchor and an overlapping/adjacent address-taken
        // buffer denote one physical frame object.  Apply this after escaped
        // member rewrites: generated references to the chosen backing name
        // must not themselves be reinterpreted as an offset-zero scalar field.
        // An enclosing Eaddrof names `backing[offset]`, while a direct value
        // access retains the selected local's scalar width at that offset.
        let stack_physical_types = stack_local_physical_types(db, func.address);
        for (name, physical_type) in &stack_physical_types {
            if stack_buffer_alias_names.contains(name)
                && !matches!(local_var_types.get(name), Some(CType::Array(..)))
            {
                local_var_types.insert(name.clone(), physical_type.clone());
            }
        }
        if let Some(aliases) = function_stack_buffer_aliases {
            // A byte-array declaration describes storage ownership, not the
            // width of a direct scalar access to that storage.  Preserve the
            // narrowest observed physical stack access for ordinary reads;
            // exact wider stores were already rewritten above.  Mark backing
            // locals explicitly so pointer casts still use array decay rather
            // than converting the offset-zero scalar value into an address.
            let access_types: HashMap<RTLReg, CType> = aliases
                .keys()
                .filter_map(|member| {
                    let name =
                        crate::decompile::passes::c_pass::helpers::param_name_for_reg(*member);
                    stack_physical_types
                        .get(&name)
                        .cloned()
                        .map(|ty| (*member, ty))
                })
                .collect();
            let mut backing_regs: HashSet<RTLReg> = db
                .stack_struct_buffers
                .get(&func.address)
                .into_iter()
                .flat_map(|buffers| buffers.keys().copied())
                .collect();
            backing_regs.extend(absorbed_buffer_roots.get(&func.address).into_iter().flatten().copied());
            body = rewrite_stack_buffer_aliases_with_access_types(
                &body,
                aliases,
                &local_var_types,
                &stack_address_regs,
                &access_types,
                &backing_regs,
            );
        }
        if let Some(aliases) = stack_buffer_end_aliases.get(&func.address) {
            body = rewrite_stack_buffer_end_aliases(&body, aliases);
        }
        if let (Some(base_pointer_names), Some(regions)) = (
            raw_frame_buffers.base_pointer_names.get(&func.address),
            raw_frame_buffers.regions.get(&func.address),
        ) {
            body = rewrite_raw_frame_buffer_addresses(&body, base_pointer_names, regions);
        }

        // Ownership recovery above can replace scalar locals with byte-array
        // coordinates after the initial Clight conversion.  Recheck those
        // newly introduced lvalues now that final local declarations are
        // known, lowering only scalar accesses rooted in recovered char[]
        // storage through exact-width byte copies.
        body = lower_byte_buffer_stmt(&body, &local_var_types);

        body = strip_trivial_casts(&body, &local_var_types);
        body = forward_return_value(&body);

        // Definitions consume the same committed return seen by callers and
        // the selector.  Evidence relations are intentionally not re-joined
        // here: this is a reader, not a fifth authority.
        let return_type = db
            .committed_interfaces
            .function(func.address as Ident)
            .map(|sig| convert_xtype(&sig.return_type, data_model))
            .unwrap_or_else(|| convert_clight_type(&func.return_type, data_model));
        let is_reconciled_void = matches!(return_type, CType::Void);

        if is_reconciled_void {
            strip_return_values_in_stmt(&mut body);
        }
        if !matches!(return_type, CType::Void) {
            fix_bare_returns_in_stmt(&mut body);
            // Repair a shared-return-merge orphan: a value-returning function never legitimately ends in a fall-through, so append the body's own tail return to a trailing non-diverging block.
            fix_falloff_return_orphan(&mut body);
        }

        // Lay the body out flat, but leave every goto explicit.  Fall-through
        // elision is a property of the layout that is actually printed, and the
        // postselect passes still move statements after this point, so it runs
        // once at the end of the pipeline in postselect::goto_elide.
        body = crate::decompile::passes::c_pass::helpers::flatten_blocks_and_cleanup(&body);

        if is_dead_expr_stmt(&body) {
            continue;
        }

        // local_var_types was seeded from func.var_type_candidates above. The
        // following overrides are populated only by the explicit
        // function-scope ablation; Stage B commits them before tree assembly
        // in the normal pipeline.

        // Legacy pointerness override: seed void * before usage inference so
        // the pointee can still refine.
        if let Some(forced) = db.decl_solve_force_ptr_regs.get(&func.address) {
            for reg in forced {
                let var_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
                if committed_names.contains(&var_name) { continue; }
                local_var_types.insert(var_name, CType::ptr(CType::Void));
            }
        }

        infer_var_types_from_usage(&body, &committed_names, &mut local_var_types, &extern_return_types);

        // Legacy force-long override, the register analogue of field
        // force-long.
        if let Some(forced) = db.decl_solve_force_long_regs.get(&func.address) {
            for reg in forced {
                let var_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
                if committed_names.contains(&var_name) { continue; }
                local_var_types.insert(var_name, CType::long());
            }
        }

        // Reassert the authoritative backing declarations after usage
        // inference, which is allowed to refine ordinary locals but not to
        // turn one physical byte buffer back into a scalar object.
        apply_stack_struct_buffer_types(db, func.address, &mut local_var_types);

        // Runtime-indexed stack arrays declare with the element type so arr + i strides by element width; a stack_struct_buffers byte-buffer entry is more specific and wins.
        if let Some(arrays) = db.stack_array_buffers.get(&func.address) {
            for (reg, (chunk, count)) in arrays {
                let var_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(*reg);
                if matches!(local_var_types.get(&var_name), Some(CType::Array(..))) {
                    continue;
                }
                let elem = ctype_from_memchunk(chunk, data_model);
                local_var_types.insert(var_name, CType::Array(Box::new(elem), Some(*count)));
            }
        }

        // A scalar-promoted store to an array local's base is illegal C, so reconcile it into the matching element store var[0] = val; keyed on the array-typed local with a bare-Var LHS.
        let array_locals: HashSet<String> = local_var_types
            .iter()
            .filter_map(|(n, t)| matches!(t, CType::Array(..)).then(|| n.clone()))
            .collect();
        if !array_locals.is_empty() {
            body = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&body, &|e| {
                if let CExpr::Assign(op, lhs, rhs) = e {
                    if let CExpr::Var(name) = lhs.as_ref() {
                        if array_locals.contains(name) {
                            let elem_lhs = CExpr::Index(
                                Box::new(CExpr::Var(name.clone())),
                                Box::new(CExpr::int(0)),
                            );
                            return Some(CExpr::Assign(*op, Box::new(elem_lhs), rhs.clone()));
                        }
                    }
                }
                None
            });
        }

        let bool_vars = detect_bool_variables(&body);

        let mut params: Vec<FuncParam> = params
            .into_iter()
            .map(|mut p| {
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
            })
            .collect();

        // const-qualify a read-only char * parameter whose name is never a write target in the emitted body, sound because the mutated-name set comes from the same body that will be compiled.
        {
            let mut mutated_names: HashSet<String> = HashSet::new();
            collect_mutated_names_in_stmt(&body, &mut mutated_names);
            let const_char_ptr = CType::Pointer(
                Box::new(CType::Qualified(
                    Box::new(CType::char_signed()),
                    crate::decompile::passes::c_pass::types::TypeQualifiers {
                        is_const: true,
                        is_volatile: false,
                        is_restrict: false,
                    },
                )),
                crate::decompile::passes::c_pass::types::TypeQualifiers::none(),
            );
            for p in &mut params {
                if let Some(name) = &p.name {
                    if p.ty == CType::ptr(CType::char_signed()) && !mutated_names.contains(name) {
                        p.ty = const_char_ptr.clone();
                    }
                }
            }
        }

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
        // __builtin_* markers are never locals: synthesizing one as a zero-init local lets the optimizer fold the guard it protects into if (0), so they are declared at file scope instead.
        local_names.retain(|n| {
            !param_name_set.contains(n) && !global_names.contains(n) && !n.starts_with("__builtin_")
        });

        let semantic_views = semantic_declaration_views(db, func.address, stack_buffer_aliases.get(&func.address));
        let mut local_vars: Vec<VarDecl> = local_names
            .into_iter()
            .map(|name| {
                let ty = local_var_types
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(CType::int);
                let storage_views = semantic_views.get(&name).cloned().unwrap_or_default();
                if let Some(committed) = concrete_declarations.get(&name) {
                    assert_eq!(&ty, committed, "emission changed a selected declaration in {}: {name}", func.name);
                }
                VarDecl {
                    type_committed: committed_names.contains(&name),
                    name,
                    ty,
                    storage_class: StorageClass::default(),
                    qualifiers: TypeQualifiers::none(),
                    alignment: None,
                    storage_views,
                    init: None,
                    loc: SourceLoc::unknown(),
                }
            })
            .collect();
        local_vars.sort_by(|a, b| a.name.cmp(&b.name));

        if std::env::var("DET_FP").is_ok() {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let body_str = crate::decompile::passes::c_pass::print::print_stmt(&body);
            let mut lv: Vec<String> = local_vars.iter().map(|v| format!("{:?}", v)).collect();
            lv.sort();
            let mut h = DefaultHasher::new();
            body_str.hash(&mut h);
            lv.join(",").hash(&mut h);
            eprintln!(
                "[FP-PR] {:016x} {} {:016x}",
                func_addr,
                func.name,
                h.finish()
            );
        }
        if let Ok(pat) = std::env::var("MANIFOLD_PR_DUMP") {
            if !pat.is_empty() && func.name.contains(&pat) {
                let body_str = crate::decompile::passes::c_pass::print::print_stmt(&body);
                let mut lv: Vec<String> = local_vars.iter().map(|v| format!("{:?}", v)).collect();
                lv.sort();
                eprintln!(
                    "[PR-DUMP] fn {} ({:#x}) locals:\n{}\n[PR-DUMP] body:\n{}",
                    func.name,
                    func_addr,
                    lv.join("\n"),
                    body_str
                );
            }
        }
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
        let origins: Vec<_> = local_vars.iter().map(|v| &v.name)
            .chain(params.iter().filter_map(|p| p.name.as_ref()))
            .filter_map(|name| name.strip_prefix("var_")?.parse::<RTLReg>().ok()
                .map(|reg| (reg, renamer.rename(name))))
            .collect();
        let body = StmtTransform::transform_stmt(&mut renamer, body);
        let params: Vec<FuncParam> = params
            .iter()
            .map(|p| {
                let new_name = p.name.as_ref().map(|n| renamer.rename(n));
                FuncParam::new(new_name, p.ty.clone())
            })
            .collect();
        let local_vars: Vec<VarDecl> = local_vars
            .into_iter()
            .map(|mut v| {
                v.name = renamer.rename(&v.name);
                v
            })
            .collect();

        // Use-before-def guard: a local that is read but never assigned, address-taken or inc/dec'd has no producer, so zero-initialize it; a defensive last resort, with the real fixes upstream.
        let mut local_origin_names: HashSet<String> = HashSet::new();
        for p in &params {
            if let Some(n) = &p.name {
                local_origin_names.insert(n.clone());
            }
        }
        collect_var_origins_stmt(&body, &mut local_origin_names);
        let mut semantic_storage_names = HashSet::new();
        // The counterexample engine constructs storage, not an invented
        // initial value. Its explicit machine stores initialize the observed
        // bytes; do not satisfy a missing-value heuristic by adding {0} to
        // this new representation. Padding/unknown bytes remain uninitialized.
        for declaration in &local_vars {
            if !declaration.storage_views.is_empty() {
                local_origin_names.insert(declaration.name.clone());
                semantic_storage_names.insert(declaration.name.clone());
            }
        }
        let local_vars: Vec<VarDecl> = local_vars
            .into_iter()
            .map(|mut v| {
                if semantic_storage_names.contains(&v.name) {
                    // The initial representation grammar admits at most
                    // eight-byte scalar views. A char array alone would only
                    // promise byte alignment, insufficient when a callee
                    // accesses this storage through an inferred struct pointer.
                    v.alignment = Some(8);
                }
                if v.init.is_none() && !local_origin_names.contains(&v.name) {
                    v.init = zero_initializer_for_var(&v.ty);
                }
                v
            })
            .collect();

        let func_name = if func.name.starts_with("FUN_") {
            recovered_func_names
                .get(&func.address)
                .cloned()
                .unwrap_or_else(|| func.name.clone())
        } else {
            func.name.clone()
        };
        let func_name = sanitize_c_symbol_name(&func_name);
        // Header-collision policy: a filtered definition is dropped entirely and its call sites bind to the system header, while a kept one is renamed <name>_local to match its converted call sites.
        if local_def_policy.filtered.contains(&func_name) {
            continue;
        }
        let func_name = func_renames.get(&func_name).cloned().unwrap_or(func_name);

        if !emitted_func_names.insert(func_name.clone()) {
            continue;
        }

        if has_cold_suffix(&func_name) && is_trivial_cold_body(&body) {
            continue;
        }

        let is_variadic = internal_variadic_functions.contains(&func.address) && !params.is_empty();
        let func_def = FuncDef {
            name: func_name,
            return_type,
            params,
            is_variadic,
            storage_class: StorageClass::default(),
            body,
            local_vars,
            loc: SourceLoc::unknown(),
        };

        if std::env::var("DET_FP").is_ok() {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let body_str = crate::decompile::passes::c_pass::print::print_stmt(&func_def.body);
            let mut lv: Vec<String> = func_def
                .local_vars
                .iter()
                .map(|v| format!("{:?}", v))
                .collect();
            lv.sort();
            let mut h = DefaultHasher::new();
            body_str.hash(&mut h);
            lv.join(",").hash(&mut h);
            eprintln!(
                "[FP-E] {:016x} {} {:016x}",
                func_addr,
                func_def.name,
                h.finish()
            );
        }
        variable_origins.extend(origins.into_iter().map(|(reg, name)|
            (func_addr, reg, func_def.name.clone(), name)));
        tu.add_function(func_def);
    }

    // A function whose declaration the compiler already provides (header prototype or builtin); our own decl only yields "conflicting types". Name/prefix lists live in header_functions.json (parsed once in c_pass::header_db, shared with print.rs's include selection), so this is data, not hardcoded.
    let is_compiler_provided = |n: &str| {
        let hdb = crate::decompile::passes::c_pass::header_db::header_db();
        hdb.functions.contains(n) || hdb.prefixes.iter().any(|p| n.starts_with(p))
    };
    let committed_decl = |name: &str| {
        let sig = db.committed_interfaces.named_function(name)?;
        let params = sig
            .param_types
            .iter()
            .enumerate()
            .map(|(index, xtype)| {
                FuncParam::named(format!("arg{index}"), convert_xtype(xtype, data_model))
            })
            .collect();
        let mut decl = crate::decompile::passes::c_pass::types::FuncDecl::new(
            name.to_string(),
            convert_xtype(&sig.return_type, data_model),
            params,
        );
        decl.is_variadic = sig.is_varargs;
        Some(decl)
    };

    // resolved_extern_signature has set semantics and may carry several rows per name, so group by sanitized name, pick one deterministically, and emit in sorted order for a byte-stable file.
    let mut extern_by_name: BTreeMap<String, Vec<(usize, XType, Arc<Vec<XType>>)>> =
        BTreeMap::new();
    for (name, param_count, ret_type, param_types) in
        db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
    {
        let sanitized = sanitize_c_symbol_name(name);
        extern_by_name.entry(sanitized).or_default().push((
            *param_count,
            *ret_type,
            param_types.clone(),
        ));
    }
    for (sanitized_name, mut sigs) in extern_by_name {
        if emitted_func_names.contains(&sanitized_name) || is_compiler_provided(&sanitized_name) {
            continue;
        }
        // Deterministic pick: prefer the row whose XType vector compares smallest.
        sigs.sort_by(|a, b| {
            a.2.cmp(&b.2)
                .then_with(|| a.1.cmp(&b.1))
                .then_with(|| a.0.cmp(&b.0))
        });
        // The relation row is retained only as a total fallback for malformed
        // input; normal emission reads the constructor's committed record.
        let (_param_count, ret_type, param_types) = sigs.into_iter().next().unwrap();
        let decl = committed_decl(&sanitized_name).unwrap_or_else(|| {
            let params = param_types
                .iter()
                .enumerate()
                .map(|(index, xtype)| {
                    FuncParam::named(format!("arg{index}"), convert_xtype(xtype, data_model))
                })
                .collect();
            let mut decl = crate::decompile::passes::c_pass::types::FuncDecl::new(
                sanitized_name.clone(),
                convert_xtype(&ret_type, data_model),
                params,
            );
            decl.is_variadic = is_known_variadic_fn(&sanitized_name);
            decl
        });
        tu.add_func_decl(decl);
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

        let decl = committed_decl(&sanitized_name).unwrap_or_else(|| {
            crate::decompile::passes::c_pass::types::FuncDecl::new_unspecified(
                sanitized_name.clone(),
                CType::int(),
            )
        });
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
                || (name.starts_with('L')
                    && name.len() > 1
                    && name[1..].chars().all(|c| c.is_ascii_hexdigit()));
            if !declared.contains(name)
                && !is_label
                && !is_compiler_provided(name)
                && !emitted_func_names.contains(name)
            {
                let decl = committed_decl(name).unwrap_or_else(|| {
                    crate::decompile::passes::c_pass::types::FuncDecl::new_unspecified(
                        name.clone(),
                        CType::int(),
                    )
                });
                forward_decls
                    .push(crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(decl));
            }
        }
        for decl in forward_decls {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(fd) = decl {
                tu.add_func_decl(fd);
            }
        }
    }

    // Forward declarations for internal functions, so a call preceding the definition does not get a conflicting implicit int name(); pushed directly to preserve the symbol->definition mapping.
    {
        let mut internal_decls = Vec::new();
        for decl in tu.decls.iter() {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDef(fdef) = decl {
                // main is declared like any other definition.  It is referenced
                // before its definition -- the CRT stub passes &main to
                // __libc_start_main -- and definitions are printed after forward
                // declarations, so whenever that stub sorts ahead of main the
                // file failed to compile on an undeclared identifier.  The
                // declaration is generated FROM the definition, so it cannot
                // contradict it.
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
            tu.decls
                .push(crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDecl(fd));
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
        // Seed the curated arity for header-suppressed non-variadic libc functions, whose fixed arity never reaches arity_counts, so an over-recovered call cannot clash with the header prototype.
        let known_variadic: HashSet<Symbol> = db
            .rel_iter::<(Symbol, usize)>("known_varargs_function")
            .map(|(n, _)| *n)
            .collect();
        for (name, arity, _ret, _params) in
            db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        {
            let sanitized = sanitize_c_symbol_name(name);
            if known_variadic.contains(name) || is_known_variadic_fn(&sanitized) {
                continue;
            }
            arity_counts.entry(sanitized).or_insert(*arity);
        }
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                f.body = normalize_call_arity_stmt(&f.body, &arity_counts);
            }
        }
    }

    // Compilability: insert explicit casts at int<->pointer assignment/argument/return mismatches, after arity normalization so padded arguments are coerced too.
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
                        (
                            f.params.iter().map(|p| p.ty.clone()).collect(),
                            f.is_variadic,
                            false,
                        ),
                    );
                    callee_ret.insert(f.name.clone(), f.return_type.clone());
                }
                TopLevelDecl::FuncDecl(d) => {
                    callee_params.entry(d.name.clone()).or_insert_with(|| {
                        (
                            d.params.iter().map(|p| p.ty.clone()).collect(),
                            d.is_variadic,
                            d.unspecified_params,
                        )
                    });
                    callee_ret
                        .entry(d.name.clone())
                        .or_insert_with(|| d.return_type.clone());
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

    // Compilability: declare any referenced-but-undeclared file-scope identifier as a tentative long; synthesized locals are excluded, since an undeclared one is a recovery gap to fix upstream.
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
        // __builtin_overflow, the opaque marker for the x86 OF flag, is declared once on use as a static volatile object so it recompiles and the optimizer cannot collapse the guarded branch.
        let uses_overflow_marker = referenced.contains("__builtin_overflow");
        let mut undeclared: Vec<String> = referenced
            .into_iter()
            .filter(|n| {
                !declared.contains(n)
                    && !locals.contains(n)
                    && is_global_like_name(n)
                    && !is_libc_stdio_global(n)
            })
            .collect();
        undeclared.sort();
        undeclared.dedup();
        for name in undeclared {
            // An undeclared L_<addr> label holding a recovered .rodata FP constant emits a typed read-only definition, so uses read the real constant rather than a zero-initialized long.
            if let Some(addr) = name
                .strip_prefix("L_")
                .and_then(|h| u64::from_str_radix(h, 16).ok())
            {
                if let Some(&(width, bits)) = rodata_fp_consts.get(&addr) {
                    if let Some(decl) = make_rodata_fp_decl(name.clone(), width, bits) {
                        tu.decls.push(decl);
                        continue;
                    }
                }
            }
            // A skip-listed library function that is only ADDRESS-TAKEN gets an extern function declaration, or a tentative long object makes &name point at a fresh .bss slot instead of the function.
            if db.should_skip_function(&name) {
                // Prefer the curated signature (void close_stdout(void), ...) over a K&R `int name()`.
                let decl = committed_decl(&name).unwrap_or_else(|| {
                    crate::decompile::passes::c_pass::types::FuncDecl::new_unspecified(
                        name.clone(),
                        CType::Int(
                            crate::decompile::passes::c_pass::types::IntSize::Int,
                            Signedness::Signed,
                        ),
                    )
                });
                tu.add_func_decl(decl);
                continue;
            }
            // A header-declared global reaching the undeclared path must use the header's canonical type, since a long tentative definition against an extern int is a hard conflicting-types error.
            let var_ty = crate::decompile::passes::c_pass::header_db::header_db()
                .variables
                .get(name.as_str())
                .and_then(|spelling| parse_canonical_var_type(spelling, data_model))
                .unwrap_or_else(CType::long);
            // A library/CRT-provided global reaching the undeclared path must be extern, or a local tentative definition is a multiple-definition error at link.
            let storage_class = if db.is_lib_global(&name)
                || (uses_real_libc_name(&name) && !is_libc_stdio_global(&name))
            {
                StorageClass::Extern
            } else {
                StorageClass::default()
            };
            tu.decls.push(TopLevelDecl::VarDecl(VarDecl {
                name,
                ty: var_ty,
                storage_class,
                qualifiers: TypeQualifiers::none(),
                alignment: None,
                storage_views: Vec::new(),
                type_committed: false,
                init: None,
                loc: SourceLoc::unknown(),
            }));
        }

        if uses_overflow_marker {
            tu.decls.push(TopLevelDecl::VarDecl(VarDecl {
                name: "__builtin_overflow".to_string(),
                ty: CType::Int(
                    crate::decompile::passes::c_pass::types::IntSize::Char,
                    Signedness::Unsigned,
                ),
                storage_class: StorageClass::Static,
                qualifiers: TypeQualifiers {
                    is_volatile: true,
                    ..TypeQualifiers::none()
                },
                alignment: None,
                storage_views: Vec::new(),
                type_committed: false,
                init: None,
                loc: SourceLoc::unknown(),
            }));
        }
    }

    // Drop captures of void-returning calls: lhs = free(p) is a frontend error, so emit the call as a bare statement; only direct assignment-of-call statements are rewritten.
    let void_fns: HashSet<String> = db
        .committed_interfaces
        .by_name
        .iter()
        .filter(|(_, interface)| matches!(interface.signature.return_type, XType::Xvoid))
        .map(|(n, _)| n.clone())
        .collect();
    if !void_fns.is_empty() {
        for decl in tu.decls.iter_mut() {
            if let crate::decompile::passes::c_pass::types::TopLevelDecl::FuncDef(f) = decl {
                drop_void_captures_stmt(&mut f.body, &void_fns);
            }
        }
    }

    variable_origins.sort();
    variable_origins.dedup();
    (tu, variable_origins)
}

// The innermost Call(Var(name), ...) of a possibly cast-wrapped call expression, returning the callee name, or None when it is not such a call.
fn call_name_through_casts(e: &CExpr) -> Option<&str> {
    match e {
        CExpr::Call(callee, _) => match callee.as_ref() {
            CExpr::Var(n) => Some(n.as_str()),
            _ => None,
        },
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => call_name_through_casts(inner),
        _ => None,
    }
}

// The bare `Call(...)` node inside a cast/paren-wrapped call expression.
fn unwrap_to_call(e: CExpr) -> CExpr {
    match e {
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => unwrap_to_call(*inner),
        other => other,
    }
}

fn drop_void_captures_stmt(stmt: &mut CStmt, void_fns: &HashSet<String>) {
    match stmt {
        CStmt::Expr(CExpr::Assign(_, _, rhs)) => {
            if call_name_through_casts(rhs).is_some_and(|n| void_fns.contains(n)) {
                let call = unwrap_to_call((**rhs).clone());
                *stmt = CStmt::Expr(call);
            }
        }
        CStmt::If(_, then_s, else_s) => {
            drop_void_captures_stmt(then_s, void_fns);
            if let Some(e) = else_s {
                drop_void_captures_stmt(e, void_fns);
            }
        }
        CStmt::Switch(_, body) => drop_void_captures_stmt(body, void_fns),
        CStmt::While(_, body) | CStmt::DoWhile(body, _) => drop_void_captures_stmt(body, void_fns),
        CStmt::For(_, _, _, body) => drop_void_captures_stmt(body, void_fns),
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => drop_void_captures_stmt(inner, void_fns),
        CStmt::Block(items) => {
            for item in items.iter_mut() {
                if let CBlockItem::Stmt(s) = item {
                    drop_void_captures_stmt(s, void_fns);
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts.iter_mut() {
                drop_void_captures_stmt(s, void_fns);
            }
        }
        _ => {}
    }
}

fn param_name_for_reg(reg: RTLReg) -> String {
    let ident = ident_from_reg(reg);
    format!("var_{}", ident)
}

pub(crate) fn convert_param_type_from_param(
    param: &ParamType,
    model: crate::abi::DataModel,
) -> CType {
    match param {
        ParamType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::ptr(CType::Struct(struct_name))
        }
        ParamType::Pointer => CType::ptr(CType::Void),
        ParamType::Typed(xtype) => convert_xtype(xtype, model),
        ParamType::Integer | ParamType::Unknown => CType::int(),
    }
}

// Collect locals with an origin in the body (assignment LHS, address-taken, or inc/dec target) for the use-before-def guard; a referenced local with none of these comes from nowhere.
fn collect_var_origins_expr(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Assign(_, lhs, rhs) => {
            if let CExpr::Var(n) = lhs.as_ref() {
                out.insert(n.clone());
            }
            collect_var_origins_expr(lhs, out);
            collect_var_origins_expr(rhs, out);
        }
        CExpr::Unary(op, inner) => {
            if matches!(
                op,
                UnaryOp::AddrOf
                    | UnaryOp::PreInc
                    | UnaryOp::PreDec
                    | UnaryOp::PostInc
                    | UnaryOp::PostDec
            ) {
                if let CExpr::Var(n) = inner.as_ref() {
                    out.insert(n.clone());
                }
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
            for a in args {
                collect_var_origins_expr(a, out);
            }
        }
        CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _)
        | CExpr::SizeofExpr(inner) => {
            collect_var_origins_expr(inner, out);
        }
        CExpr::StmtExpr(stmts, fin) => {
            for s in stmts {
                collect_var_origins_stmt(s, out);
            }
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
            if let Some(s) = e {
                collect_var_origins_stmt(s, out);
            }
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
                Some(ForInit::Decl(decls)) => {
                    for d in decls {
                        out.insert(d.name.clone());
                    }
                }
                None => {}
            }
            if let Some(c) = cond {
                collect_var_origins_expr(c, out);
            }
            if let Some(u) = update {
                collect_var_origins_expr(u, out);
            }
            collect_var_origins_stmt(body, out);
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_var_origins_stmt(s, out),
                    CBlockItem::Decl(decls) => {
                        for d in decls {
                            out.insert(d.name.clone());
                        }
                    }
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_var_origins_stmt(s, out);
            }
        }
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_var_origins_stmt(inner, out),
        _ => {}
    }
}

// Zero initializer for a "variable from nowhere": scalars/pointers get `= 0`, aggregates get `= {0}` (both valid C); function/void-typed declarations are left untouched.
fn zero_initializer_for_var(
    ty: &CType,
) -> Option<crate::decompile::passes::c_pass::types::Initializer> {
    use crate::decompile::passes::c_pass::types::{InitItem, Initializer};
    match ty {
        CType::Void | CType::Function(..) => None,
        CType::Struct(_) | CType::Union(_) | CType::Array(..) => {
            Some(Initializer::List(vec![InitItem {
                designator: None,
                init: Initializer::Expr(CExpr::int(0)),
            }]))
        }
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_var_names_from_stmt(inner, vars),
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

/// The base symbol(s) an lvalue ultimately names (`x`, `*x`, `x.f`, `x[i]`, `(T)x` all base on `x`).
fn collect_lvalue_base_names(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Var(n) => {
            out.insert(n.clone());
        }
        CExpr::Unary(_, e)
        | CExpr::Cast(_, e)
        | CExpr::Paren(e)
        | CExpr::Member(e, _)
        | CExpr::MemberPtr(e, _) => collect_lvalue_base_names(e, out),
        CExpr::Index(a, _) => collect_lvalue_base_names(a, out),
        _ => {}
    }
}

/// Collect names appearing in a MUTATION context (assignment LHS, & operand, inc/dec target), distinguishing a library-provided global from one this TU owns; over-collecting only keeps a global defined.
fn collect_mutated_names_in_expr(expr: &CExpr, out: &mut HashSet<String>) {
    match expr {
        CExpr::Assign(_, lhs, rhs) => {
            collect_lvalue_base_names(lhs, out);
            collect_mutated_names_in_expr(lhs, out);
            collect_mutated_names_in_expr(rhs, out);
        }
        CExpr::Unary(op, inner) => {
            if matches!(
                op,
                UnaryOp::AddrOf
                    | UnaryOp::PreInc
                    | UnaryOp::PreDec
                    | UnaryOp::PostInc
                    | UnaryOp::PostDec
            ) {
                collect_lvalue_base_names(inner, out);
            }
            collect_mutated_names_in_expr(inner, out);
        }
        CExpr::Binary(_, a, b) | CExpr::Index(a, b) => {
            collect_mutated_names_in_expr(a, out);
            collect_mutated_names_in_expr(b, out);
        }
        CExpr::Cast(_, e)
        | CExpr::Paren(e)
        | CExpr::SizeofExpr(e)
        | CExpr::Member(e, _)
        | CExpr::MemberPtr(e, _) => collect_mutated_names_in_expr(e, out),
        CExpr::Ternary(c, t, e) => {
            collect_mutated_names_in_expr(c, out);
            collect_mutated_names_in_expr(t, out);
            collect_mutated_names_in_expr(e, out);
        }
        CExpr::Call(f, args) => {
            collect_mutated_names_in_expr(f, out);
            for a in args {
                collect_mutated_names_in_expr(a, out);
            }
        }
        _ => {}
    }
}

fn collect_mutated_names_in_stmt(stmt: &CStmt, out: &mut HashSet<String>) {
    match stmt {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => collect_mutated_names_in_expr(e, out),
        CStmt::If(cond, then_s, else_s) => {
            collect_mutated_names_in_expr(cond, out);
            collect_mutated_names_in_stmt(then_s, out);
            if let Some(e) = else_s {
                collect_mutated_names_in_stmt(e, out);
            }
        }
        CStmt::Switch(expr, body) => {
            collect_mutated_names_in_expr(expr, out);
            collect_mutated_names_in_stmt(body, out);
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_mutated_names_in_stmt(body, out);
            collect_mutated_names_in_expr(cond, out);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(crate::decompile::passes::c_pass::types::ForInit::Expr(e)) = init {
                collect_mutated_names_in_expr(e, out);
            }
            if let Some(cond) = cond {
                collect_mutated_names_in_expr(cond, out);
            }
            if let Some(update) = update {
                collect_mutated_names_in_expr(update, out);
            }
            collect_mutated_names_in_stmt(body, out);
        }
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_mutated_names_in_stmt(inner, out),
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_mutated_names_in_stmt(s, out);
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_mutated_names_in_stmt(s, out);
            }
        }
        _ => {}
    }
}

fn infer_var_types_from_usage(
    stmt: &CStmt,
    fixed: &HashSet<String>,
    var_types: &mut HashMap<String, CType>,
    extern_return_types: &HashMap<String, CType>,
) {
    match stmt {
        CStmt::Expr(e) => infer_types_from_expr(e, fixed, var_types, extern_return_types),
        CStmt::Return(Some(e)) => infer_types_from_expr(e, fixed, var_types, extern_return_types),
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    infer_var_types_from_usage(s, fixed, var_types, extern_return_types);
                }
            }
        }
        CStmt::If(cond, then_s, else_s) => {
            infer_types_from_expr(cond, fixed, var_types, extern_return_types);
            infer_var_types_from_usage(then_s, fixed, var_types, extern_return_types);
            if let Some(e) = else_s {
                infer_var_types_from_usage(e, fixed, var_types, extern_return_types);
            }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            infer_types_from_expr(cond, fixed, var_types, extern_return_types);
            infer_var_types_from_usage(body, fixed, var_types, extern_return_types);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(fi) = init {
                if let crate::decompile::passes::c_pass::types::ForInit::Expr(e) = fi {
                    infer_types_from_expr(e, fixed, var_types, extern_return_types);
                }
            }
            if let Some(e) = cond {
                infer_types_from_expr(e, fixed, var_types, extern_return_types);
            }
            if let Some(e) = update {
                infer_types_from_expr(e, fixed, var_types, extern_return_types);
            }
            infer_var_types_from_usage(body, fixed, var_types, extern_return_types);
        }
        CStmt::Switch(e, body) => {
            infer_types_from_expr(e, fixed, var_types, extern_return_types);
            infer_var_types_from_usage(body, fixed, var_types, extern_return_types);
        }
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => {
            infer_var_types_from_usage(inner, fixed, var_types, extern_return_types)
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                infer_var_types_from_usage(s, fixed, var_types, extern_return_types);
            }
        }
        _ => {}
    }
}

fn insert_or_refine(fixed: &HashSet<String>, var_types: &mut HashMap<String, CType>, name: String, new_ty: CType) {
    if fixed.contains(&name) { return; }
    match var_types.get(&name) {
        None => {
            var_types.insert(name, new_ty);
        }
        Some(existing) => {
            if *existing == CType::ptr(CType::Void)
                && new_ty != CType::ptr(CType::Void)
                && new_ty.is_pointer()
            {
                var_types.insert(name, new_ty);
            }
            // NOTE (plan 5.4): the int/long -> pointer FLIP is retired. Pointerness is decided by the solver and force_ptr_regs; usage inference defers on that axis and only refines the pointee or width.
            else if *existing == CType::long() && !new_ty.is_pointer() && new_ty != CType::long()
            {
                var_types.insert(name, new_ty);
            } else if existing.is_generic_long_ptr()
                && new_ty.is_pointer()
                && !new_ty.is_generic_long_ptr()
            {
                var_types.insert(name, new_ty);
            }
        }
    }
}

#[cfg(test)]
mod declaration_commitment_tests {
    use super::*;
    #[test]
    fn usage_inference_cannot_retype_a_selected_structural_declaration() {
        let short_pointer = CType::ptr(CType::Int(IntSize::Short, Signedness::Unsigned));
        let mut types = HashMap::from([
            ("precise".to_owned(), short_pointer.clone()),
            ("unknown".to_owned(), CType::ptr(CType::Void)),
        ]);
        let body = CStmt::Sequence(["precise", "unknown"].into_iter().map(|name|
            CStmt::Expr(CExpr::deref(CExpr::cast(CType::ptr(CType::char_signed()), CExpr::var(name))))).collect());
        infer_var_types_from_usage(&body, &HashSet::from(["precise".to_owned()]), &mut types, &HashMap::new());
        assert_eq!(types["precise"], short_pointer);
        assert_eq!(types["unknown"], CType::ptr(CType::char_signed()));
    }
    #[test]
    fn known_call_return_is_not_a_second_authority_over_committed_types() {
        let mut types = HashMap::from([("result".to_owned(), CType::long())]);
        let body = CStmt::Expr(CExpr::assign(CExpr::var("result"), CExpr::call(CExpr::var("allocate"), vec![])));
        let returns = HashMap::from([("allocate".to_owned(), CType::ptr(CType::Void))]);
        infer_var_types_from_usage(&body, &HashSet::from(["result".to_owned()]), &mut types, &returns);
        assert_eq!(types["result"], CType::long());
    }
}

fn extract_var_name(expr: &CExpr) -> Option<&str> {
    match expr {
        CExpr::Var(name) => Some(name.as_str()),
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => extract_var_name(inner),
        _ => None,
    }
}

// A 32/64-bit int/long, the default scalar the seeding hands an untyped result reg; sub-int, float and pointer types are excluded so the pointer-return override never downgrades them.
fn is_default_int_scalar_ty(t: Option<&CType>) -> bool {
    use crate::decompile::passes::c_pass::types::IntSize;
    matches!(t, Some(CType::Int(IntSize::Int | IntSize::Long, _)))
}

fn infer_types_from_expr(
    expr: &CExpr,
    fixed: &HashSet<String>,
    var_types: &mut HashMap<String, CType>,
    extern_return_types: &HashMap<String, CType>,
) {
    match expr {
        CExpr::Unary(UnaryOp::Deref, inner) => {
            if let CExpr::Cast(ty, cast_inner) = inner.as_ref() {
                if let Some(name) = extract_var_name(cast_inner) {
                    if ty.is_pointer() {
                        insert_or_refine(fixed, var_types, name.to_string(), ty.clone());
                    }
                }
            } else if let CExpr::Paren(paren_inner) = inner.as_ref() {
                if let CExpr::Binary(BinaryOp::Add, lhs, _) | CExpr::Binary(BinaryOp::Sub, lhs, _) =
                    paren_inner.as_ref()
                {
                    if let CExpr::Cast(ty, cast_inner) = lhs.as_ref() {
                        if let Some(name) = extract_var_name(cast_inner) {
                            if ty.is_pointer() {
                                insert_or_refine(fixed, var_types, name.to_string(), ty.clone());
                            }
                        }
                    }
                }
            } else if let CExpr::Var(name) = inner.as_ref() {
                var_types
                    .entry(name.clone())
                    .or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(inner, fixed, var_types, extern_return_types);
        }
        CExpr::Unary(UnaryOp::Not, inner) => {
            if let Some(name) = extract_var_name(inner) {
                // Operand of `!` says nothing about its value set; keep int
                // (the spelling CType::Bool used to print as).
                var_types.entry(name.to_string()).or_insert(CType::int());
            }
            infer_types_from_expr(inner, fixed, var_types, extern_return_types);
        }
        CExpr::Assign(_, lhs, rhs) => {
            if let CExpr::Var(name) = lhs.as_ref() {
                if let CExpr::Cast(ty, _) = rhs.as_ref() {
                    if ty.is_pointer() {
                        insert_or_refine(fixed, var_types, name.clone(), ty.clone());
                    }
                }
                if matches!(rhs.as_ref(), CExpr::StringLit(_)) {
                    insert_or_refine(fixed, var_types, name.clone(), CType::ptr(CType::char_signed()));
                }
                if let CExpr::Call(callee, _) = rhs.as_ref() {
                    if let CExpr::Var(func_name) = callee.as_ref() {
                        if let Some(ret_ty) = extern_return_types.get(func_name.as_str()) {
                            // The result of a known POINTER-returning call is that pointer (a declared return type, not a cast inference); overrides only a default int/long scalar that would truncate it.
                            if !fixed.contains(name) && ret_ty.is_pointer() && is_default_int_scalar_ty(var_types.get(name))
                            {
                                var_types.insert(name.clone(), ret_ty.clone());
                            } else {
                                var_types.entry(name.clone()).or_insert(ret_ty.clone());
                            }
                        }
                    }
                }
            }
            infer_types_from_expr(lhs, fixed, var_types, extern_return_types);
            infer_types_from_expr(rhs, fixed, var_types, extern_return_types);
        }
        CExpr::Call(func, args) => {
            if let CExpr::Var(func_name) = func.as_ref() {
                infer_call_arg_types(func_name, args, fixed, var_types);
            }
            infer_types_from_expr(func, fixed, var_types, extern_return_types);
            for arg in args {
                infer_types_from_expr(arg, fixed, var_types, extern_return_types);
            }
        }
        CExpr::MemberPtr(inner, _) => {
            if let CExpr::Var(name) = inner.as_ref() {
                var_types
                    .entry(name.clone())
                    .or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(inner, fixed, var_types, extern_return_types);
        }
        CExpr::Index(base, index) => {
            if let CExpr::Var(name) = base.as_ref() {
                var_types
                    .entry(name.clone())
                    .or_insert_with(|| CType::ptr(CType::Void));
            }
            infer_types_from_expr(base, fixed, var_types, extern_return_types);
            infer_types_from_expr(index, fixed, var_types, extern_return_types);
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Member(inner, _) => {
            infer_types_from_expr(inner, fixed, var_types, extern_return_types);
        }
        CExpr::Binary(_, lhs, rhs) => {
            infer_types_from_expr(lhs, fixed, var_types, extern_return_types);
            infer_types_from_expr(rhs, fixed, var_types, extern_return_types);
        }
        CExpr::Ternary(c, t, e) => {
            infer_types_from_expr(c, fixed, var_types, extern_return_types);
            infer_types_from_expr(t, fixed, var_types, extern_return_types);
            infer_types_from_expr(e, fixed, var_types, extern_return_types);
        }
        _ => {}
    }
}

fn infer_call_arg_types(func_name: &str, args: &[CExpr], fixed: &HashSet<String>, var_types: &mut HashMap<String, CType>) {
    let char_ptr = || CType::ptr(CType::char_signed());
    let void_ptr = || CType::ptr(CType::Void);
    let str_first: &[&str] = &[
        "strlen",
        "strcmp",
        "strncmp",
        "strcpy",
        "strdup",
        "strndup",
        "strcat",
        "strncat",
        "strchr",
        "strrchr",
        "strstr",
        "strtol",
        "strtoul",
        "strtoll",
        "strtoull",
        "strtod",
        "atoi",
        "atol",
        "atoll",
        "fputs",
        "puts",
        "printf",
        "sprintf",
        "snprintf",
        "__sprintf_chk",
        "__snprintf_chk",
        "__fprintf_chk",
        "__printf_chk",
        "dcgettext",
        "gettext",
        "ngettext",
        "dgettext",
        "setlocale",
        "getenv",
        "putenv",
        "opendir",
        "stat",
        "lstat",
        "access",
        "unlink",
        "rmdir",
        "mkdir",
        "fopen",
        "freopen",
        "remove",
        "rename",
        "error",
        "error_at_line",
    ];
    if str_first.contains(&func_name) {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
    }
    let str_second: &[&str] = &[
        "strcmp",
        "strncmp",
        "strcpy",
        "strncpy",
        "strcat",
        "strncat",
        "strstr",
        "fprintf",
        "sprintf",
        "snprintf",
        "fopen",
        "freopen",
        "rename",
        "__sprintf_chk",
        "__snprintf_chk",
    ];
    if str_second.contains(&func_name) {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
    }
    if func_name == "fprintf" {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
    }
    if func_name == "snprintf" || func_name == "__snprintf_chk" {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
    }
    if matches!(func_name, "memset" | "memcpy" | "memmove" | "memcmp") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), void_ptr());
        }
        if matches!(func_name, "memcpy" | "memmove" | "memcmp") {
            if let Some(name) = args.get(1).and_then(extract_var_name) {
                insert_or_refine(fixed, var_types, name.to_string(), void_ptr());
            }
        }
    }
    if matches!(func_name, "memset" | "memcpy" | "memmove" | "memcmp") {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::ulong());
        }
    }
    if func_name == "error" || func_name == "error_at_line" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "getopt_long" || func_name == "getopt" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(
                fixed,
                var_types,
                name.to_string(),
                CType::ptr(CType::ptr(CType::char_signed())),
            );
        }
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
    }
    if matches!(func_name, "exit" | "_exit" | "_Exit") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if matches!(func_name, "fwrite" | "fread") {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), void_ptr());
        }
    }
    if func_name == "fgets" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), char_ptr());
        }
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "setlocale" {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if func_name == "open" {
        if let Some(name) = args.get(1).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if matches!(
        func_name,
        "close" | "read" | "write" | "dup" | "dup2" | "fcntl" | "ioctl" | "isatty"
    ) {
        if let Some(name) = args.first().and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
    if matches!(
        func_name,
        "strtol" | "strtoul" | "strtoll" | "strtoull" | "strtod"
    ) {
        if let Some(name) = args.get(2).and_then(extract_var_name) {
            insert_or_refine(fixed, var_types, name.to_string(), CType::int());
        }
    }
}

fn detect_bool_variables(stmt: &CStmt) -> HashSet<&str> {
    let mut bool_uses: HashMap<&str, (usize, usize)> = HashMap::new();
    collect_bool_evidence(stmt, &mut bool_uses, false);
    bool_uses
        .into_iter()
        .filter(|(_, (bool_count, non_bool_count))| *bool_count > 0 && *non_bool_count == 0)
        .map(|(name, _)| name)
        .collect()
}

fn collect_bool_evidence<'a>(
    stmt: &'a CStmt,
    evidence: &mut HashMap<&'a str, (usize, usize)>,
    _in_bool_ctx: bool,
) {
    match stmt {
        CStmt::If(cond, then_s, else_s) => {
            collect_bool_evidence_expr(cond, evidence, true);
            collect_bool_evidence(then_s, evidence, false);
            if let Some(e) = else_s {
                collect_bool_evidence(e, evidence, false);
            }
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
            if let Some(e) = cond {
                collect_bool_evidence_expr(e, evidence, true);
            }
            if let Some(e) = update {
                collect_bool_evidence_expr(e, evidence, false);
            }
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_bool_evidence(inner, evidence, false),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_bool_evidence(s, evidence, false);
            }
        }
        _ => {}
    }
}

fn collect_bool_evidence_expr<'a>(
    expr: &'a CExpr,
    evidence: &mut HashMap<&'a str, (usize, usize)>,
    in_bool_ctx: bool,
) {
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
            let lhs_is_bool_const =
                matches!(rhs.as_ref(), CExpr::IntLit(lit) if lit.value == 0 || lit.value == 1);
            let rhs_is_bool_const =
                matches!(lhs.as_ref(), CExpr::IntLit(lit) if lit.value == 0 || lit.value == 1);
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
            for arg in args {
                collect_bool_evidence_expr(arg, evidence, false);
            }
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) => {
            collect_bool_evidence_expr(inner, evidence, false);
        }
        _ => {}
    }
}

fn strip_trivial_casts(stmt: &CStmt, var_types: &HashMap<String, CType>) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(strip_trivial_casts_expr(e, var_types)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(strip_trivial_casts(s, var_types)),
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            strip_trivial_casts_expr(cond, var_types),
            Box::new(strip_trivial_casts(then_s, var_types)),
            else_s
                .as_ref()
                .map(|e| Box::new(strip_trivial_casts(e, var_types))),
        ),
        CStmt::While(cond, body) => CStmt::While(
            strip_trivial_casts_expr(cond, var_types),
            Box::new(strip_trivial_casts(body, var_types)),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(strip_trivial_casts(body, var_types)),
            strip_trivial_casts_expr(cond, var_types),
        ),
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.as_ref()
                .map(|e| strip_trivial_casts_expr(e, var_types)),
            update
                .as_ref()
                .map(|e| strip_trivial_casts_expr(e, var_types)),
            Box::new(strip_trivial_casts(body, var_types)),
        ),
        CStmt::Return(Some(e)) => CStmt::Return(Some(strip_trivial_casts_expr(e, var_types))),
        CStmt::Switch(e, body) => CStmt::Switch(
            strip_trivial_casts_expr(e, var_types),
            Box::new(strip_trivial_casts(body, var_types)),
        ),
        CStmt::Labeled(lbl, inner) => {
            CStmt::Labeled(lbl.clone(), Box::new(strip_trivial_casts(inner, var_types)))
        }
        CStmt::Effect(lbl, inner) => {
            CStmt::Effect(lbl.clone(), Box::new(strip_trivial_casts(inner, var_types)))
        }
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts
                .iter()
                .map(|s| strip_trivial_casts(s, var_types))
                .collect(),
        ),
        other => other.clone(),
    }
}

// A cast is trivial only when it names the variable's exact declared C type.
// Width and signedness are both semantic: dropping `(unsigned long)signed_long`
// changes an unsigned machine comparison at values such as -1/UINT64_MAX, and
// dropping `(long)int_var` can change promotions in its enclosing expression.
// Float, pointer, and array casts are conversions for the same reason.  The
// declaration is what the emitted operand means, so equality is the complete
// safe test here rather than the operand merely belonging to the integer class.
fn var_cast_is_exact_type(var_types: &HashMap<String, CType>, name: &str, target: &CType) -> bool {
    var_types.get(name) == Some(target)
}

fn strip_trivial_casts_expr(expr: &CExpr, var_types: &HashMap<String, CType>) -> CExpr {
    fn unwrap_parens(expr: &CExpr) -> &CExpr {
        match expr {
            CExpr::Paren(inner) => unwrap_parens(inner),
            other => other,
        }
    }

    match expr {
        CExpr::Cast(ty, inner) => {
            let inner_stripped = strip_trivial_casts_expr(inner, var_types);

            if ty.is_integer() {
                let unwrapped_inner = unwrap_parens(&inner_stripped);
                if let CExpr::Var(name) = unwrapped_inner {
                    if var_cast_is_exact_type(var_types, name, ty) {
                        return inner_stripped;
                    }
                }
            }

            if is_long_type(ty) {
                let unwrapped_inner = unwrap_parens(&inner_stripped);
                match unwrapped_inner {
                    // A mismatched variable type is a real conversion, even
                    // when both sides happen to be long-sized integers.
                    CExpr::Var(_) => {}
                    // Literal typing depends on suffix, base, value, and the C
                    // data model.  Keep the explicit selected cast rather than
                    // guessing that the literal already has this exact type.
                    CExpr::IntLit(_) | CExpr::StringLit(_) => {}
                    CExpr::Cast(inner_ty, _) if inner_ty == ty => return inner_stripped,
                    // Likewise keep (long)(float)x: the inner float-cast is the float->int step, so stripping the (long) would put a float directly under an outer pointer cast.
                    CExpr::Cast(inner_ty, _) if inner_ty.is_float() => {}
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
            Box::new(strip_trivial_casts_expr(lhs, var_types)),
            Box::new(strip_trivial_casts_expr(rhs, var_types)),
        ),
        CExpr::Binary(op, lhs, rhs) => CExpr::Binary(
            *op,
            Box::new(strip_trivial_casts_expr(lhs, var_types)),
            Box::new(strip_trivial_casts_expr(rhs, var_types)),
        ),
        CExpr::Unary(op, inner) => {
            CExpr::Unary(*op, Box::new(strip_trivial_casts_expr(inner, var_types)))
        }
        CExpr::Call(func, args) => CExpr::Call(
            Box::new(strip_trivial_casts_expr(func, var_types)),
            args.iter()
                .map(|a| strip_trivial_casts_expr(a, var_types))
                .collect(),
        ),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(strip_trivial_casts_expr(inner, var_types))),
        CExpr::Index(arr, idx) => CExpr::Index(
            Box::new(strip_trivial_casts_expr(arr, var_types)),
            Box::new(strip_trivial_casts_expr(idx, var_types)),
        ),
        CExpr::Member(inner, field) => CExpr::Member(
            Box::new(strip_trivial_casts_expr(inner, var_types)),
            field.clone(),
        ),
        CExpr::MemberPtr(inner, field) => CExpr::MemberPtr(
            Box::new(strip_trivial_casts_expr(inner, var_types)),
            field.clone(),
        ),
        CExpr::Ternary(cond, then_e, else_e) => CExpr::Ternary(
            Box::new(strip_trivial_casts_expr(cond, var_types)),
            Box::new(strip_trivial_casts_expr(then_e, var_types)),
            Box::new(strip_trivial_casts_expr(else_e, var_types)),
        ),
        other => other.clone(),
    }
}

// Last top-level return <expr> in a body block (the function's tail return), scanning only the immediate item list so it picks the function-level exit, not an early in-cascade return.
fn last_toplevel_return_expr(body: &CStmt) -> Option<CExpr> {
    let items = match body {
        CStmt::Block(items) => items,
        _ => return None,
    };
    let mut found: Option<CExpr> = None;
    for it in items {
        if let CBlockItem::Stmt(s) = it {
            match s {
                CStmt::Return(Some(e)) => found = Some(e.clone()),
                // A labeled block whose inner directly returns also exposes a tail return.
                (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => {
                    if let CStmt::Return(Some(e)) = &**inner {
                        found = Some(e.clone());
                    }
                }
                _ => {}
            }
        }
    }
    found
}

// Repair the shared-return-merge orphan: append the tail return inside a final labeled block that does not end in an unconditional exit, always a defect in a value-returning function.
fn fix_falloff_return_orphan(body: &mut CStmt) {
    let ret_expr = match last_toplevel_return_expr(body) {
        Some(e) => e,
        None => return,
    };
    let items = match body {
        CStmt::Block(items) => items,
        _ => return,
    };
    let Some(CBlockItem::Stmt(last)) = items.last_mut() else {
        return;
    };
    let (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) = last else {
        return;
    };
    if is_unconditional_exit(inner) {
        return;
    }
    // Append `return <tail expr>` to the labeled block's body, preserving its existing statements.
    let appended = CStmt::Return(Some(ret_expr));
    let new_inner = match &**inner {
        CStmt::Block(inner_items) => {
            let mut v = inner_items.clone();
            v.push(CBlockItem::Stmt(appended));
            CStmt::Block(v)
        }
        CStmt::Empty => appended,
        other => CStmt::Block(vec![
            CBlockItem::Stmt(other.clone()),
            CBlockItem::Stmt(appended),
        ]),
    };
    **inner = new_inner;
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => fix_bare_returns_in_stmt(inner),
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => strip_return_values_in_stmt(inner),
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

/// libc stdio FILE* globals keep their REAL name and are left UNDEFINED so <stdio.h>'s extern binds them to libc; renaming them silently disconnects them and any fputs on them segfaults.
pub(crate) fn is_libc_stdio_global(name: &str) -> bool {
    let base = name.split('@').next().unwrap_or(name);
    crate::decompile::passes::c_pass::header_db::header_db()
        .stdio_globals
        .contains(base)
}

/// libc globals that must keep their REAL name (the stdio FILE*s plus the getopt globals and environ) so they bind to libc; the getopt/environ ones are emitted as a plain extern.
fn uses_real_libc_name(name: &str) -> bool {
    let base = name.split('@').next().unwrap_or(name);
    crate::decompile::passes::c_pass::header_db::header_db()
        .real_libc_globals
        .contains(base)
}

pub(crate) fn sanitize_c_symbol_name(name: &str) -> String {
    if uses_real_libc_name(name) {
        return name.split('@').next().unwrap_or(name).to_string();
    }
    // Globals colliding with a libc symbol but holding a PROGRAM copy are renamed <name>_sym so the recovered definition neither binds to nor shadows the libc one.
    let reserved = &crate::decompile::passes::c_pass::header_db::header_db().reserved_globals;

    let base_name = name.split('@').next().unwrap_or(name);
    if reserved.contains(base_name) {
        let mut out = sanitize_c_ident(base_name);
        out.push_str("_sym");
        return out;
    }

    let mut out = sanitize_c_ident(name);
    if reserved.contains(out.as_str()) {
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
        self.map
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
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
            // Collect ALL referenced names; a __builtin_* identifier is a compiler builtin, filtered out at the locals call-site but kept at the undeclared-globals one so the marker is declared.
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
            // A bare-name callee is usually a direct call needing no VarDecl, but an indirect call's target is a var_* local that DOES need declaring; collect that, skip symbols, and recurse into complex callees.
            let callee_var = match func.as_ref() {
                CExpr::Var(n) => Some(n),
                CExpr::Cast(_, inner) => match inner.as_ref() {
                    CExpr::Var(n) => Some(n),
                    _ => None,
                },
                _ => None,
            };
            match callee_var {
                Some(n) if n.starts_with("var_") => {
                    vars.insert(n.clone());
                }
                Some(_) => {}
                None => collect_var_names_from_expr(func, vars),
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
        crate::decompile::passes::c_pass::types::Initializer::Expr(e) => {
            collect_var_names_from_expr(e, vars)
        }
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
    /// Exact lvalue coordinates for identifiers that name a byte of a
    /// recovered global object, including scalar accesses at offset zero.
    /// Keeping this as CExpr (rather than encoding `owner[index]` into a
    /// string) preserves aliasing and prevents the name sanitizer from turning
    /// an address coordinate into an unrelated C global.
    pub global_lvalue_aliases: HashMap<usize, CExpr>,
    /// The target's C data model, so a 64-bit value gets a 64-bit spelling.
    pub data_model: crate::abi::DataModel,
    /// Source ABI effects licensed by a unique, selected machine event. They
    /// follow statement provenance, not the printable spelling of its lvalue.
    pub source_post_effects: HashMap<Node, CStmt>,
    pub applied_source_effects: HashSet<Node>,
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
    /// Locally-DEFINED functions colliding with a header declaration, mapped to their emitted name (atexit -> atexit_local), applied to every symbol reference so call sites track the rename.
    pub func_renames: HashMap<String, String>,
    /// CAST-2: label id -> final injective C identifier, computed once so Slabel(id) and Sgoto(id) always resolve to the SAME name while distinct ids never share one.
    label_disambig: HashMap<usize, String>,
}

impl ConversionContext {
    pub fn new(id_to_name: HashMap<usize, String>, data_model: crate::abi::DataModel) -> Self {
        let global_names = id_to_name.values().cloned().collect();
        let label_disambig = Self::build_label_disambig(&id_to_name);
        Self {
            id_to_name,
            global_lvalue_aliases: HashMap::new(),
            data_model,
            source_post_effects: HashMap::new(),
            applied_source_effects: HashSet::new(),
            global_names,
            string_globals: HashSet::new(),
            name_counter: 0,
            temp_names: HashMap::new(),
            var_types: HashMap::new(),
            string_label_to_content: HashMap::new(),
            suppress_string_literals: false,
            func_addrs_sorted: Vec::new(),
            func_renames: HashMap::new(),
            label_disambig,
        }
    }

    // CAST-2: the un-disambiguated label spelling for a raw id_to_name entry. label_name resolves through this, then through label_disambig for colliding ids.
    fn label_name_base(raw: &str) -> String {
        if raw.chars().all(|c| c.is_ascii_digit()) {
            format!("L{}", raw)
        } else {
            sanitize_c_ident(raw)
        }
    }

    // CAST-2: resolve label ids that sanitize to the same identifier; the smallest id in a colliding group keeps the plain name and the rest get <base>_<id>, sorted so the choice is order-independent.
    fn build_label_disambig(id_to_name: &HashMap<usize, String>) -> HashMap<usize, String> {
        let mut by_base: HashMap<String, Vec<usize>> = HashMap::new();
        for (id, raw) in id_to_name {
            by_base
                .entry(Self::label_name_base(raw))
                .or_default()
                .push(*id);
        }
        let mut out: HashMap<usize, String> = HashMap::new();
        for (base, mut ids) in by_base {
            if ids.len() <= 1 {
                continue;
            }
            ids.sort();
            for &id in ids.iter().skip(1) {
                out.insert(id, format!("{}_{}", base, id));
            }
        }
        out
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
        // CAST-2: a colliding id resolves through the per-context disambiguation map (built once in new); Slabel(id) and Sgoto(id) hit the same entry, so a goto and its target always agree.
        if let Some(name) = self.label_disambig.get(&id) {
            return name.clone();
        }
        match self.id_to_name.get(&id) {
            Some(raw) => Self::label_name_base(raw),
            None => format!("L{}", id),
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
        match self
            .func_addrs_sorted
            .binary_search_by_key(&addr, |(a, _)| *a)
        {
            Ok(idx) => sanitize_c_symbol_name(&self.func_addrs_sorted[idx].1),
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
        // A string literal IS a char *, and the repairs below are the ones that decide whether a
        // subtraction is a pointer difference or an integer one. Leaving it unclassified made
        // `(long)p - "..."` -- long minus char *, which gcc rejects -- fall through every arm
        // untouched (stripped dircolors, dir, ls and vdir).
        CExpr::StringLit(_) => true,
        // ptr +/- int yields a pointer; comparisons/other ops do not.
        CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, l, r) => {
            cexpr_is_pointer(l, types) || cexpr_is_pointer(r, types)
        }
        _ => false,
    }
}

/// A floating-typed operand under the FINAL declarations: the mirror of `cexpr_is_pointer`, used only to keep a pointer away from a float partner.
fn cexpr_is_float(e: &CExpr, types: &HashMap<String, CType>) -> bool {
    match e {
        CExpr::Cast(ty, _) => ty.is_float(),
        CExpr::Var(name) => types.get(name).map_or(false, |t| t.is_float()),
        CExpr::Paren(inner) => cexpr_is_float(inner, types),
        CExpr::FloatLit(_) => true,
        _ => false,
    }
}

// Cast pointer operands of machine address arithmetic to long so the arithmetic is valid C; MEASURED non-subsumable (bypassing it regressed +3010 invalid-binop) and disjoint from decl-level force_long.
fn repair_pointer_arith(
    op: BinaryOp,
    lhs: CExpr,
    lhs_ptr: bool,
    lhs_float: bool,
    rhs: CExpr,
    rhs_ptr: bool,
    rhs_float: bool,
) -> (CExpr, CExpr) {
    let to_long = |e: CExpr| CExpr::Cast(CType::long(), Box::new(e));
    // No C binary operator accepts one pointer-shaped operand together with one floating operand:
    // classify_add/classify_sub/classify_cmp have no such case and every binarith fallback rejects
    // pointers outright, so the pair is ill-typed for EVERY operator -- comparisons included, where
    // `double == void *` is a hard gcc error. This is the last point at which the declarations the
    // C will actually carry are known, so integerize here rather than trusting each upstream layer
    // to have kept the pair apart. The POINTER side is the one that moves: (long)p is an integer
    // that converts to the floating type, whereas integerizing the float side would leave a
    // pointer/integer comparison, still not a legal pair.
    if lhs_ptr && rhs_float {
        return (to_long(lhs), rhs);
    }
    if rhs_ptr && lhs_float {
        return (lhs, to_long(rhs));
    }
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

// Walk an expression bottom-up, repairing invalid pointer arithmetic at every Binary node. The Clight type annotation carried by an expression node (every variant's last field).
fn clight_expr_ctype(e: &clight::ClightExpr) -> &clight::ClightType {
    use clight::ClightExpr::*;
    match e {
        EconstInt(_, t)
        | EconstFloat(_, t)
        | EconstSingle(_, t)
        | EconstLong(_, t)
        | Evar(_, t)
        | EvarSymbol(_, t)
        | Etempvar(_, t)
        | Ederef(_, t)
        | Eaddrof(_, t)
        | Eunop(_, _, t)
        | Ebinop(_, _, _, t)
        | Ecast(_, t)
        | Efield(_, _, t)
        | Esizeof(_, t)
        | Ealignof(_, t)
        | Econdition(_, _, _, t) => t,
    }
}

/// Strip a materialized annotation cast on a bare variable when the final decl renders it redundant: `(T *)v` with v declared exactly `T *` is just `v`.
fn strip_matching_var_cast(e: CExpr, types: &HashMap<String, CType>) -> CExpr {
    if let CExpr::Cast(cty, inner) = &e {
        if let CExpr::Var(name) = inner.as_ref() {
            if types.get(name) == Some(cty) {
                return (**inner).clone();
            }
        }
    }
    e
}

/// A string literal is a char * base that code indexes into, never the integer offset; paren/cast-transparent, targeting the case cexpr_is_pointer does not classify as a pointer at all.
fn is_string_base(e: &CExpr) -> bool {
    match e {
        CExpr::StringLit(_) => true,
        CExpr::Paren(inner) | CExpr::Cast(_, inner) => is_string_base(inner),
        _ => false,
    }
}

/// An "indexable base" of pointer arithmetic that must stay a pointer: a string literal, &x, or an array-declared Var; the caller integerizes the OTHER operand instead of scalarizing both.
fn is_indexable_base(e: &CExpr, types: &HashMap<String, CType>) -> bool {
    match e {
        CExpr::Unary(UnaryOp::AddrOf, _) => true,
        CExpr::Var(name) => matches!(types.get(name), Some(CType::Array(..))),
        // A cast whose TARGET is a pointer type is itself a pointer base, even when an outer integer cast later scalarizes it (`(long)(T *)p`): recursing lets the inner `(T *)` cast still register as the base.
        CExpr::Cast(ty, inner) => ty.is_pointer() || is_indexable_base(inner, types),
        CExpr::Paren(inner) => is_indexable_base(inner, types),
        _ => is_string_base(e),
    }
}

/// Undo a scalarizing integer cast wrapping a pointer base -- `(long)(T *)p` -> `(T *)p` -- so an address base survives as a pointer through additive arithmetic. Strips only when the outer cast is integer and the inner is itself an indexable (pointer) base; otherwise returns `e` unchanged.
fn strip_scalarizing_cast(e: CExpr, types: &HashMap<String, CType>) -> CExpr {
    if let CExpr::Cast(ty, inner) = &e {
        if ty.is_integer() && is_indexable_base(inner, types) {
            return (**inner).clone();
        }
    }
    e
}

/// Peel leading casts/parens to the underlying value, so a mis-typed pointer index `(long)(void *)v` can be re-expressed cleanly as `(long)v`.
fn peel_casts(e: &CExpr) -> &CExpr {
    match e {
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => peel_casts(inner),
        _ => e,
    }
}

/// True when the innermost pointer cast of `e` is `void *` -- the degenerate pointer type a mis-typed integer index usually carries.
fn inner_ptr_is_void(e: &CExpr) -> bool {
    match e {
        CExpr::Cast(CType::Pointer(inner, _), _) if matches!(**inner, CType::Void) => true,
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => inner_ptr_is_void(inner),
        _ => false,
    }
}

/// True when a pointee type SCALES under C pointer arithmetic (stride > 1): anything but char (stride 1) and void (GNU stride 1) and an array pointee. A scaling pointee is what makes a raw byte offset get re-multiplied.
fn pointee_scales_ctype(pointee: &CType) -> bool {
    !matches!(
        pointee,
        CType::Void | CType::Int(IntSize::Char, _) | CType::Array(..)
    )
}

/// Recognize a typed pointer already rebased through char-sized arithmetic.
/// Ordinary machine address arithmetic can fold a later raw byte offset into
/// this expression; an actual dereference/memcpy address must instead preserve
/// the explicit T-pointer element stride selected by Clight.
fn peel_char_byte_rebase(e: &CExpr) -> Option<(CType, CExpr)> {
    let (ptr_ty, inner) = match e {
        CExpr::Cast(CType::Pointer(pointee, q), inner) if pointee_scales_ctype(pointee) => {
            (CType::Pointer(pointee.clone(), *q), inner.as_ref())
        }
        _ => return None,
    };
    let byte_expr = match inner {
        CExpr::Paren(inner) => inner.as_ref(),
        other => other,
    };
    if let CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, lhs, _) = byte_expr {
        let char_base = matches!(
            lhs.as_ref(),
            CExpr::Cast(CType::Pointer(pointee, _), _)
                if matches!(pointee.as_ref(), CType::Int(IntSize::Char, _))
        );
        if char_base {
            return Some((ptr_ty, byte_expr.clone()));
        }
    }
    None
}

/// A scaling pointer whose sibling integral operand is a raw byte offset.
/// Bare pointer variables always need byte rebasing. An already-rebased typed
/// pointer does so only outside a proven memory-access address.
fn scaling_ptr_byte_base(
    e: &CExpr,
    types: &HashMap<String, CType>,
    preserve_typed_stride: bool,
) -> Option<(CType, Option<CExpr>)> {
    match e {
        CExpr::Paren(inner) => scaling_ptr_byte_base(inner, types, preserve_typed_stride),
        CExpr::Var(name) => match types.get(name) {
            Some(CType::Pointer(pointee, _)) if pointee_scales_ctype(pointee) => {
                Some((types.get(name).cloned().unwrap(), None))
            }
            _ => None,
        },
        _ if !preserve_typed_stride => {
            peel_char_byte_rebase(e).map(|(ty, inner)| (ty, Some(inner)))
        }
        _ => None,
    }
}

/// Apply a raw BYTE offset to a scaling pointer base exactly once through char*, folding into an already-rebased inner expression; byte-correct under any pointee size since char* has stride 1.
fn rebase_byte_add_through_char(
    op: BinaryOp,
    base: CExpr,
    inner_byte_expr: Option<CExpr>,
    offset: CExpr,
    ptr_ty: CType,
) -> CExpr {
    let off = CExpr::Cast(CType::long(), Box::new(offset));
    let byte_addr = match inner_byte_expr {
        Some(inner) => CExpr::Binary(op, Box::new(inner), Box::new(off)),
        None => {
            let base_char = CExpr::Cast(CType::ptr(CType::char_signed()), Box::new(base));
            CExpr::Binary(op, Box::new(base_char), Box::new(off))
        }
    };
    CExpr::Cast(ptr_ty, Box::new(CExpr::Paren(Box::new(byte_addr))))
}

/// CType for a memory chunk (element type of a runtime-indexed stack array).
fn ctype_from_memchunk(chunk: &MemoryChunk, model: crate::abi::DataModel) -> CType {
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize, Signedness};
    match chunk {
        // CompCert MBool is a one-byte memory chunk.  CType::Bool currently
        // prints as C `int`, so using it here would widen recovered storage to
        // four bytes and invalidate alignment/extent reasoning.
        MemoryChunk::MBool => CType::char_unsigned(),
        MemoryChunk::MInt8Signed => CType::Int(IntSize::Char, Signedness::Signed),
        MemoryChunk::MInt8Unsigned => CType::Int(IntSize::Char, Signedness::Unsigned),
        MemoryChunk::MInt16Signed => CType::Int(IntSize::Short, Signedness::Signed),
        MemoryChunk::MInt16Unsigned => CType::Int(IntSize::Short, Signedness::Unsigned),
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => CType::Int(IntSize::Int, Signedness::Signed),
        MemoryChunk::MFloat32 => CType::Float(FloatSize::Float),
        MemoryChunk::MFloat64 => CType::Float(FloatSize::Double),
        MemoryChunk::MInt64 | MemoryChunk::MAny64 if model.long_size() != 8 =>
            CType::Int(IntSize::LongLong, Signedness::Signed),
        _ => CType::long(),
    }
}

fn transform_initializer_exprs(
    init: &Initializer,
    transform: &impl Fn(&CExpr) -> CExpr,
) -> Initializer {
    match init {
        Initializer::Expr(expr) => Initializer::Expr(transform(expr)),
        Initializer::List(items) => Initializer::List(
            items
                .iter()
                .map(|item| InitItem {
                    designator: item
                        .designator
                        .as_ref()
                        .map(|designator| transform_designator_exprs(designator, transform)),
                    init: transform_initializer_exprs(&item.init, transform),
                })
                .collect(),
        ),
        Initializer::String(literal) => Initializer::String(literal.clone()),
    }
}

fn transform_designator_exprs(
    designator: &Designator,
    transform: &impl Fn(&CExpr) -> CExpr,
) -> Designator {
    match designator {
        Designator::Field(field) => Designator::Field(field.clone()),
        Designator::Index(expr) => Designator::Index(transform(expr)),
        Designator::Range(first, last) => Designator::Range(transform(first), transform(last)),
    }
}

fn transform_decl_initializers(
    decls: &[VarDecl],
    transform: &impl Fn(&CExpr) -> CExpr,
) -> Vec<VarDecl> {
    decls
        .iter()
        .map(|decl| VarDecl {
            init: decl
                .init
                .as_ref()
                .map(|init| transform_initializer_exprs(init, transform)),
            ..decl.clone()
        })
        .collect()
}

fn transform_for_initializer(init: &ForInit, transform: &impl Fn(&CExpr) -> CExpr) -> ForInit {
    match init {
        ForInit::Expr(expr) => ForInit::Expr(transform(expr)),
        ForInit::Decl(decls) => ForInit::Decl(transform_decl_initializers(decls, transform)),
    }
}

fn repair_arith_expr(e: &CExpr, types: &HashMap<String, CType>) -> CExpr {
    repair_arith_expr_context(e, types, false)
}

fn repair_arith_expr_context(
    e: &CExpr,
    types: &HashMap<String, CType>,
    preserve_typed_stride: bool,
) -> CExpr {
    // &arr on an array-typed local is pointer-to-array, so &arr + i strides by whole arrays; rewrite it to the bare name, which decays to an element pointer.
    if let CExpr::Unary(UnaryOp::AddrOf, inner) = e {
        if let CExpr::Var(name) = inner.as_ref() {
            if matches!(types.get(name), Some(CType::Array(..))) {
                return CExpr::Var(name.clone());
            }
        }
    }
    match e {
        CExpr::Binary(op, l, r) => {
            let l_raw = repair_arith_expr_context(l, types, preserve_typed_stride);
            let r_raw = repair_arith_expr_context(r, types, preserve_typed_stride);
            // Byte-offset re-scaling fix on the UN-stripped children:
            // re-express a bare scaling base plus a raw byte offset through
            // char*. Explicit pointer casts keep their C element stride.
            if matches!(op, BinaryOp::Add | BinaryOp::Sub) {
                let l_byte_base = scaling_ptr_byte_base(&l_raw, types, preserve_typed_stride);
                let r_byte_base = scaling_ptr_byte_base(&r_raw, types, preserve_typed_stride);
                match (l_byte_base, r_byte_base) {
                    (Some((lty, inner)), None) if !cexpr_is_pointer(&r_raw, types) => {
                        return rebase_byte_add_through_char(*op, l_raw, inner, r_raw, lty);
                    }
                    // offset + base (Add is commutative; Sub of int - ptr is not a base subtraction).
                    (None, Some((rty, inner)))
                        if matches!(op, BinaryOp::Add) && !cexpr_is_pointer(&l_raw, types) =>
                    {
                        return rebase_byte_add_through_char(*op, r_raw, inner, l_raw, rty);
                    }
                    _ => {}
                }
            }
            let l = strip_matching_var_cast(l_raw, types);
            let r = r_raw;
            // An indexable base added to a pointer-TYPED operand means that operand is really the integer offset, so keep the base and cast the offset to long rather than scalarizing both.
            if matches!(op, BinaryOp::Add | BinaryOp::Sub) {
                let l_base = is_indexable_base(&l, types);
                let r_base = is_indexable_base(&r, types);
                let to_long = |e: CExpr| CExpr::Cast(CType::long(), Box::new(e));
                if l_base ^ r_base {
                    match op {
                        // base +/- offset / offset + base: keep the base, integerize the pointer offset.
                        BinaryOp::Add if l_base && cexpr_is_pointer(&r, types) => {
                            return CExpr::Binary(*op, Box::new(l), Box::new(to_long(r)));
                        }
                        BinaryOp::Add if r_base && cexpr_is_pointer(&l, types) => {
                            return CExpr::Binary(*op, Box::new(to_long(l)), Box::new(r));
                        }
                        BinaryOp::Sub if l_base && cexpr_is_pointer(&r, types) => {
                            return CExpr::Binary(*op, Box::new(l), Box::new(to_long(r)));
                        }
                        // ptr - base: a pointer minus a base is a mismatched difference; normalize to an integer one.
                        BinaryOp::Sub if r_base && cexpr_is_pointer(&l, types) => {
                            return CExpr::Binary(*op, Box::new(to_long(l)), Box::new(to_long(r)));
                        }
                        // A scalarized pointer base plus a plain integer offset: the outer (long) hid the pointer from the arms above, so strip the base's scalarizing cast to keep base + off a T * + long.
                        BinaryOp::Add if l_base && !cexpr_is_pointer(&r, types) => {
                            return CExpr::Binary(
                                *op,
                                Box::new(strip_scalarizing_cast(l, types)),
                                Box::new(r),
                            );
                        }
                        BinaryOp::Add if r_base && !cexpr_is_pointer(&l, types) => {
                            return CExpr::Binary(
                                *op,
                                Box::new(l),
                                Box::new(strip_scalarizing_cast(r, types)),
                            );
                        }
                        BinaryOp::Sub if l_base && !cexpr_is_pointer(&r, types) => {
                            return CExpr::Binary(
                                *op,
                                Box::new(strip_scalarizing_cast(l, types)),
                                Box::new(r),
                            );
                        }
                        _ => {}
                    }
                }
                // Both operands carry pointer casts, and ptr + ptr is never valid C, so keep the typed pointer as the base and integerize the void*-cast operand.
                if matches!(op, BinaryOp::Add)
                    && is_indexable_base(&l, types)
                    && is_indexable_base(&r, types)
                {
                    let l_void = inner_ptr_is_void(&l);
                    let r_void = inner_ptr_is_void(&r);
                    if r_void && !l_void {
                        return CExpr::Binary(
                            *op,
                            Box::new(strip_scalarizing_cast(l, types)),
                            Box::new(to_long(peel_casts(&r).clone())),
                        );
                    }
                    if l_void && !r_void {
                        return CExpr::Binary(
                            *op,
                            Box::new(to_long(peel_casts(&l).clone())),
                            Box::new(strip_scalarizing_cast(r, types)),
                        );
                    }
                }
            }
            let lp = cexpr_is_pointer(&l, types);
            let rp = cexpr_is_pointer(&r, types);
            let lf = cexpr_is_float(&l, types);
            let rf = cexpr_is_float(&r, types);
            let (l, r) = repair_pointer_arith(*op, l, lp, lf, r, rp, rf);
            CExpr::Binary(*op, Box::new(l), Box::new(r))
        }
        CExpr::Unary(op, inner) => {
            let child_preserves_stride = preserve_typed_stride || matches!(op, UnaryOp::Deref);
            let inner = repair_arith_expr_context(inner, types, child_preserves_stride);
            // `-ptr` and `~ptr` are invalid C; cast the pointer operand to long (Deref/AddrOf/Not are valid on pointers and left alone).
            let inner = if matches!(op, UnaryOp::Neg | UnaryOp::BitNot)
                && cexpr_is_pointer(&inner, types)
            {
                CExpr::Cast(CType::long(), Box::new(inner))
            } else {
                inner
            };
            // Strip the materialized access cast (Ederef conversion) when the final decl makes it redundant: `*(T *)v` with v declared exactly `T *` prints `*v`.
            let inner = if matches!(op, UnaryOp::Deref) {
                strip_matching_var_cast(inner, types)
            } else {
                inner
            };
            CExpr::Unary(*op, Box::new(inner))
        }
        CExpr::Assign(op, l, r) => CExpr::Assign(
            *op,
            Box::new(repair_arith_expr_context(l, types, preserve_typed_stride)),
            Box::new(repair_arith_expr_context(r, types, preserve_typed_stride)),
        ),
        CExpr::Ternary(c, t, f) => CExpr::Ternary(
            Box::new(repair_arith_expr_context(c, types, preserve_typed_stride)),
            Box::new(repair_arith_expr_context(t, types, preserve_typed_stride)),
            Box::new(repair_arith_expr_context(f, types, preserve_typed_stride)),
        ),
        CExpr::Call(f, args) => {
            let is_memcpy = matches!(f.as_ref(), CExpr::Var(name) if name == "__builtin_memcpy");
            CExpr::Call(
                Box::new(repair_arith_expr_context(f, types, preserve_typed_stride)),
                args.iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        repair_arith_expr_context(
                            arg,
                            types,
                            preserve_typed_stride || (is_memcpy && index < 2),
                        )
                    })
                    .collect(),
            )
        }
        CExpr::Cast(ty, inner) => CExpr::Cast(
            ty.clone(),
            Box::new(repair_arith_expr_context(
                inner,
                types,
                preserve_typed_stride,
            )),
        ),
        CExpr::Member(inner, fld) => {
            // `e.field` where e is a pointer must be `e->field`; type recovery sometimes declares the base as a pointer while emitting a value member access ("X is a pointer; use ->").
            let inner = repair_arith_expr_context(inner, types, preserve_typed_stride);
            if cexpr_is_pointer(&inner, types) {
                CExpr::MemberPtr(Box::new(inner), fld.clone())
            } else {
                CExpr::Member(Box::new(inner), fld.clone())
            }
        }
        CExpr::MemberPtr(inner, fld) => CExpr::MemberPtr(
            Box::new(repair_arith_expr_context(
                inner,
                types,
                preserve_typed_stride,
            )),
            fld.clone(),
        ),
        CExpr::Index(a, i) => CExpr::Index(
            Box::new(repair_arith_expr_context(a, types, preserve_typed_stride)),
            Box::new(repair_arith_expr_context(i, types, preserve_typed_stride)),
        ),
        CExpr::SizeofExpr(inner) => CExpr::SizeofExpr(Box::new(repair_arith_expr_context(
            inner,
            types,
            preserve_typed_stride,
        ))),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(repair_arith_expr_context(
            inner,
            types,
            preserve_typed_stride,
        ))),
        CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
            ty.clone(),
            initializers
                .iter()
                .map(|init| {
                    transform_initializer_exprs(init, &|expr| {
                        repair_arith_expr_context(expr, types, preserve_typed_stride)
                    })
                })
                .collect(),
        ),
        CExpr::Generic(selector, arms) => CExpr::Generic(
            Box::new(repair_arith_expr_context(
                selector,
                types,
                preserve_typed_stride,
            )),
            arms.iter()
                .map(|(ty, arm)| {
                    (
                        ty.clone(),
                        repair_arith_expr_context(arm, types, preserve_typed_stride),
                    )
                })
                .collect(),
        ),
        CExpr::StmtExpr(stmts, inner) => CExpr::StmtExpr(
            stmts.iter().map(|s| repair_arith_stmt(s, types)).collect(),
            Box::new(repair_arith_expr_context(
                inner,
                types,
                preserve_typed_stride,
            )),
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
                    CBlockItem::Decl(decls) => {
                        CBlockItem::Decl(transform_decl_initializers(decls, &|expr| {
                            repair_arith_expr(expr, types)
                        }))
                    }
                })
                .collect(),
        ),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            repair_arith_expr(cond, types),
            Box::new(repair_arith_stmt(then_s, types)),
            else_s
                .as_ref()
                .map(|e| Box::new(repair_arith_stmt(e, types))),
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
            init.as_ref().map(|init| {
                transform_for_initializer(init, &|expr| repair_arith_expr(expr, types))
            }),
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
        CStmt::Labeled(lbl, inner) => {
            CStmt::Labeled(lbl.clone(), Box::new(repair_arith_stmt(inner, types)))
        }
        CStmt::Effect(lbl, inner) => {
            CStmt::Effect(lbl.clone(), Box::new(repair_arith_stmt(inner, types)))
        }
        CStmt::Sequence(stmts) => {
            CStmt::Sequence(stmts.iter().map(|s| repair_arith_stmt(s, types)).collect())
        }
        CStmt::Decl(decls) => CStmt::Decl(transform_decl_initializers(decls, &|expr| {
            repair_arith_expr(expr, types)
        })),
        other => other.clone(),
    }
}

// Pad or truncate each call's argument list to the callee's declared fixed arity, padding with 0; counts holds only fixed-arity callees, so variadic and K&R calls are untouched.
fn normalize_call_arity_expr(e: &CExpr, counts: &HashMap<String, usize>) -> CExpr {
    match e {
        CExpr::Call(func, args) => {
            let nf = normalize_call_arity_expr(func, counts);
            let mut nargs: Vec<CExpr> = args
                .iter()
                .map(|a| normalize_call_arity_expr(a, counts))
                .collect();
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
        CExpr::Binary(op, l, r) => CExpr::Binary(
            *op,
            Box::new(normalize_call_arity_expr(l, counts)),
            Box::new(normalize_call_arity_expr(r, counts)),
        ),
        CExpr::Assign(op, l, r) => CExpr::Assign(
            *op,
            Box::new(normalize_call_arity_expr(l, counts)),
            Box::new(normalize_call_arity_expr(r, counts)),
        ),
        CExpr::Ternary(c, t, f) => CExpr::Ternary(
            Box::new(normalize_call_arity_expr(c, counts)),
            Box::new(normalize_call_arity_expr(t, counts)),
            Box::new(normalize_call_arity_expr(f, counts)),
        ),
        CExpr::Cast(ty, i) => {
            CExpr::Cast(ty.clone(), Box::new(normalize_call_arity_expr(i, counts)))
        }
        CExpr::Member(i, f) => {
            CExpr::Member(Box::new(normalize_call_arity_expr(i, counts)), f.clone())
        }
        CExpr::MemberPtr(i, f) => {
            CExpr::MemberPtr(Box::new(normalize_call_arity_expr(i, counts)), f.clone())
        }
        CExpr::Index(a, i) => CExpr::Index(
            Box::new(normalize_call_arity_expr(a, counts)),
            Box::new(normalize_call_arity_expr(i, counts)),
        ),
        CExpr::SizeofExpr(i) => CExpr::SizeofExpr(Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::Paren(i) => CExpr::Paren(Box::new(normalize_call_arity_expr(i, counts))),
        CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
            ty.clone(),
            initializers
                .iter()
                .map(|init| {
                    transform_initializer_exprs(init, &|expr| {
                        normalize_call_arity_expr(expr, counts)
                    })
                })
                .collect(),
        ),
        CExpr::Generic(selector, arms) => CExpr::Generic(
            Box::new(normalize_call_arity_expr(selector, counts)),
            arms.iter()
                .map(|(ty, arm)| (ty.clone(), normalize_call_arity_expr(arm, counts)))
                .collect(),
        ),
        CExpr::StmtExpr(stmts, i) => CExpr::StmtExpr(
            stmts
                .iter()
                .map(|s| normalize_call_arity_stmt(s, counts))
                .collect(),
            Box::new(normalize_call_arity_expr(i, counts)),
        ),
        other => other.clone(),
    }
}

fn normalize_call_arity_stmt(stmt: &CStmt, counts: &HashMap<String, usize>) -> CStmt {
    match stmt {
        CStmt::Expr(e) => CStmt::Expr(normalize_call_arity_expr(e, counts)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(normalize_call_arity_stmt(s, counts)),
                    CBlockItem::Decl(decls) => {
                        CBlockItem::Decl(transform_decl_initializers(decls, &|expr| {
                            normalize_call_arity_expr(expr, counts)
                        }))
                    }
                })
                .collect(),
        ),
        CStmt::If(c, t, e) => CStmt::If(
            normalize_call_arity_expr(c, counts),
            Box::new(normalize_call_arity_stmt(t, counts)),
            e.as_ref()
                .map(|x| Box::new(normalize_call_arity_stmt(x, counts))),
        ),
        CStmt::While(c, b) => CStmt::While(
            normalize_call_arity_expr(c, counts),
            Box::new(normalize_call_arity_stmt(b, counts)),
        ),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(
            Box::new(normalize_call_arity_stmt(b, counts)),
            normalize_call_arity_expr(c, counts),
        ),
        CStmt::For(init, c, u, b) => CStmt::For(
            init.as_ref().map(|init| {
                transform_for_initializer(init, &|expr| normalize_call_arity_expr(expr, counts))
            }),
            c.as_ref().map(|x| normalize_call_arity_expr(x, counts)),
            u.as_ref().map(|x| normalize_call_arity_expr(x, counts)),
            Box::new(normalize_call_arity_stmt(b, counts)),
        ),
        CStmt::Return(Some(e)) => CStmt::Return(Some(normalize_call_arity_expr(e, counts))),
        CStmt::Switch(e, b) => CStmt::Switch(
            normalize_call_arity_expr(e, counts),
            Box::new(normalize_call_arity_stmt(b, counts)),
        ),
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(
            lbl.clone(),
            Box::new(normalize_call_arity_stmt(inner, counts)),
        ),
        CStmt::Effect(lbl, inner) => CStmt::Effect(
            lbl.clone(),
            Box::new(normalize_call_arity_stmt(inner, counts)),
        ),
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts
                .iter()
                .map(|s| normalize_call_arity_stmt(s, counts))
                .collect(),
        ),
        CStmt::Decl(decls) => CStmt::Decl(transform_decl_initializers(decls, &|expr| {
            normalize_call_arity_expr(expr, counts)
        })),
        other => other.clone(),
    }
}

// Compilability: insert explicit casts at int<->pointer mismatches, which modern clang and gcc reject as hard errors even under -w; float<->pointer and unknown-class operands are left alone.

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
        CType::Qualified(inner, _) => ctype_scalar_class(inner),
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
        CExpr::Var(name) => types
            .get(name)
            .map(ctype_scalar_class)
            .unwrap_or(ScalarClass::Other),
        CExpr::Paren(inner) => cexpr_scalar_class(inner, types, callee_ret),
        CExpr::IntLit(_) => ScalarClass::Int,
        CExpr::FloatLit(_) => ScalarClass::Float,
        CExpr::StringLit(_) => ScalarClass::Ptr,
        CExpr::Unary(UnaryOp::AddrOf, _) => ScalarClass::Ptr,
        CExpr::Unary(UnaryOp::Neg | UnaryOp::BitNot | UnaryOp::Not | UnaryOp::Plus, _) => {
            ScalarClass::Int
        }
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
            CExpr::Var(n) => callee_ret
                .get(n)
                .map(ctype_scalar_class)
                .unwrap_or(ScalarClass::Other),
            _ => ScalarClass::Other,
        },
        CExpr::CompoundLit(ty, _) => ctype_scalar_class(ty),
        CExpr::StmtExpr(_, tail) => cexpr_scalar_class(tail, types, callee_ret),
        CExpr::Generic(_, arms) => {
            let mut classes = arms
                .iter()
                .map(|(_, arm)| cexpr_scalar_class(arm, types, callee_ret));
            let Some(first) = classes.next() else {
                return ScalarClass::Other;
            };
            if classes.all(|class| class == first) {
                first
            } else {
                ScalarClass::Other
            }
        }
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
        (
            ctype_scalar_class(target),
            cexpr_scalar_class(&e, types, callee_ret)
        ),
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
        CExpr::Unary(UnaryOp::Deref, inner) => {
            lvalue_ctype(inner, types).and_then(|pointer| pointer.pointee().cloned())
        }
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
        CExpr::Unary(op, i) => CExpr::Unary(
            *op,
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
        ),
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
        CExpr::Cast(ty, i) => CExpr::Cast(
            ty.clone(),
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
        ),
        CExpr::Member(i, fld) => CExpr::Member(
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
            fld.clone(),
        ),
        CExpr::MemberPtr(i, fld) => CExpr::MemberPtr(
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
            fld.clone(),
        ),
        CExpr::Index(a, i) => CExpr::Index(
            Box::new(insert_casts_expr(a, types, callee_params, callee_ret)),
            Box::new(insert_casts_expr(i, types, callee_params, callee_ret)),
        ),
        CExpr::SizeofExpr(i) => CExpr::SizeofExpr(Box::new(insert_casts_expr(
            i,
            types,
            callee_params,
            callee_ret,
        ))),
        CExpr::Paren(i) => CExpr::Paren(Box::new(insert_casts_expr(
            i,
            types,
            callee_params,
            callee_ret,
        ))),
        CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
            ty.clone(),
            initializers
                .iter()
                .map(|init| {
                    transform_initializer_exprs(init, &|expr| {
                        insert_casts_expr(expr, types, callee_params, callee_ret)
                    })
                })
                .collect(),
        ),
        CExpr::Generic(selector, arms) => CExpr::Generic(
            Box::new(insert_casts_expr(
                selector,
                types,
                callee_params,
                callee_ret,
            )),
            arms.iter()
                .map(|(ty, arm)| {
                    (
                        ty.clone(),
                        insert_casts_expr(arm, types, callee_params, callee_ret),
                    )
                })
                .collect(),
        ),
        CExpr::StmtExpr(stmts, i) => CExpr::StmtExpr(
            stmts
                .iter()
                .map(|s| insert_casts_stmt(s, types, callee_params, callee_ret, &CType::Void))
                .collect(),
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
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(insert_casts_stmt(
                        s,
                        types,
                        callee_params,
                        callee_ret,
                        ret_type,
                    )),
                    CBlockItem::Decl(decls) => {
                        CBlockItem::Decl(transform_decl_initializers(decls, &|expr| {
                            insert_casts_expr(expr, types, callee_params, callee_ret)
                        }))
                    }
                })
                .collect(),
        ),
        CStmt::If(c, t, e) => CStmt::If(
            insert_casts_expr(c, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(
                t,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
            e.as_ref().map(|x| {
                Box::new(insert_casts_stmt(
                    x,
                    types,
                    callee_params,
                    callee_ret,
                    ret_type,
                ))
            }),
        ),
        CStmt::While(c, b) => CStmt::While(
            insert_casts_expr(c, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(
                b,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
        ),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(
            Box::new(insert_casts_stmt(
                b,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
            insert_casts_expr(c, types, callee_params, callee_ret),
        ),
        CStmt::For(init, c, u, b) => CStmt::For(
            init.as_ref().map(|init| {
                transform_for_initializer(init, &|expr| {
                    insert_casts_expr(expr, types, callee_params, callee_ret)
                })
            }),
            c.as_ref()
                .map(|x| insert_casts_expr(x, types, callee_params, callee_ret)),
            u.as_ref()
                .map(|x| insert_casts_expr(x, types, callee_params, callee_ret)),
            Box::new(insert_casts_stmt(
                b,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
        ),
        CStmt::Switch(e, b) => CStmt::Switch(
            insert_casts_expr(e, types, callee_params, callee_ret),
            Box::new(insert_casts_stmt(
                b,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
        ),
        CStmt::Labeled(lbl, inner) => CStmt::Labeled(
            lbl.clone(),
            Box::new(insert_casts_stmt(
                inner,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
        ),
        CStmt::Effect(lbl, inner) => CStmt::Effect(
            lbl.clone(),
            Box::new(insert_casts_stmt(
                inner,
                types,
                callee_params,
                callee_ret,
                ret_type,
            )),
        ),
        CStmt::Sequence(ss) => CStmt::Sequence(
            ss.iter()
                .map(|s| insert_casts_stmt(s, types, callee_params, callee_ret, ret_type))
                .collect(),
        ),
        CStmt::Return(Some(e)) => {
            let ne = insert_casts_expr(e, types, callee_params, callee_ret);
            let ne = if matches!(ret_type, CType::Void) {
                ne
            } else {
                coerce_scalar(ret_type, ne, types, callee_ret)
            };
            CStmt::Return(Some(ne))
        }
        CStmt::Decl(decls) => CStmt::Decl(transform_decl_initializers(decls, &|expr| {
            insert_casts_expr(expr, types, callee_params, callee_ret)
        })),
        other => other.clone(),
    }
}

// Whether a referenced-but-undeclared identifier should become a file-scope object; synthesized local names are excluded, since masking one with a global would hide the real recovery gap.
fn is_global_like_name(n: &str) -> bool {
    if n.is_empty() {
        return false;
    }
    if n.starts_with("var_") || n.starts_with("tmp") {
        return false;
    }
    // Compiler builtins (the opaque markers for un-encodable ops) are neither file-scope objects nor locals, and declaring one as a tentative long would let the optimizer constant-fold it.
    if n.starts_with("__builtin_") {
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

// A Clight temporary read carries the integer interpretation selected for this
// operation, while its single emitted C declaration covers the whole RTL value
// web.  Those can legitimately differ when one machine register is reused at
// unrelated widths or signednesses.  Materialize the read annotation here so
// C's usual arithmetic conversions implement the selected Clight operation;
// strip_trivial_casts removes it later when the final declaration is exact.
fn convert_integer_operand(expr: &clight::ClightExpr, ctx: &mut ConversionContext) -> CExpr {
    let converted = convert_expr(expr, ctx);
    match expr {
        clight::ClightExpr::Etempvar(
            _,
            ty @ (clight::ClightType::Tint(..)
            | clight::ClightType::Tlong(..)
            | clight::ClightType::Tint128(..)),
        ) => CExpr::Cast(convert_clight_type(ty, ctx.data_model), Box::new(converted)),
        _ => converted,
    }
}

fn clight_access_is_volatile(ty: &clight::ClightType) -> bool {
    match ty {
        clight::ClightType::Tint(_, _, attr)
        | clight::ClightType::Tlong(_, attr)
        | clight::ClightType::Tint128(_, attr)
        | clight::ClightType::Tfloat(_, attr)
        | clight::ClightType::Tpointer(_, attr)
        | clight::ClightType::Tarray(_, _, attr)
        | clight::ClightType::Tstruct(_, attr)
        | clight::ClightType::Tunion(_, attr) => attr.attr_volatile,
        clight::ClightType::Tvoid | clight::ClightType::Tfunction(..) => false,
    }
}

// Character lvalues are alignment-1 and may alias every C object.  Other
// scalar machine accesses require either exact typed-owner evidence or an
// alignment/effective-type-neutral byte copy at the C boundary.
fn scalar_access_needs_alignment(ty: &clight::ClightType) -> bool {
    match ty {
        clight::ClightType::Tint(clight::ClightIntSize::I8, _, _) => false,
        clight::ClightType::Tint(..)
        | clight::ClightType::Tlong(..)
        | clight::ClightType::Tint128(..)
        | clight::ClightType::Tfloat(..)
        | clight::ClightType::Tpointer(..) => true,
        _ => false,
    }
}

fn peel_clight_pointer_casts(expr: &clight::ClightExpr) -> &clight::ClightExpr {
    match expr {
        clight::ClightExpr::Ecast(inner, _) => peel_clight_pointer_casts(inner),
        _ => expr,
    }
}

// Only the address of a scalar Clight object with the same exact type proves
// natural alignment.  Inferred pointers, integer addresses, byte arithmetic,
// and recovered fields are deliberately not treated as proofs.
fn scalar_deref_alignment_proven(
    address: &clight::ClightExpr,
    access_ty: &clight::ClightType,
) -> bool {
    let clight::ClightExpr::Eaddrof(object, _) = peel_clight_pointer_casts(address) else {
        return false;
    };
    match object.as_ref() {
        clight::ClightExpr::Evar(_, object_ty) | clight::ClightExpr::Etempvar(_, object_ty) => {
            object_ty == access_ty
        }
        _ => false,
    }
}

fn should_lower_scalar_deref(address: &clight::ClightExpr, access_ty: &clight::ClightType) -> bool {
    scalar_access_needs_alignment(access_ty)
        && !clight_access_is_volatile(access_ty)
        && !scalar_deref_alignment_proven(address, access_ty)
}

fn should_lower_scalar_field(
    address: &clight::ClightExpr,
    aggregate_ty: &clight::ClightType,
    field_ty: &clight::ClightType,
) -> bool {
    // An inferred aggregate is not evidence that a C object of that effective
    // type exists. Even character MEMBERS can acquire aggregate TBAA during
    // optimization. Use the same bytewise access contract as wider fields;
    // the character-alias exception applies to a character lvalue, not to an
    // arbitrary guessed aggregate view. Proven exact owners remain readable.
    (scalar_access_needs_alignment(field_ty)
        || matches!(field_ty, clight::ClightType::Tint(clight::ClightIntSize::I8, _, _)))
        && !clight_access_is_volatile(aggregate_ty)
        && !clight_access_is_volatile(field_ty)
        && !scalar_deref_alignment_proven(address, aggregate_ty)
}

fn byte_offset_expr(base: CExpr, offset: i64) -> CExpr {
    let byte_base = CExpr::Cast(CType::ptr(CType::char_unsigned()), Box::new(base));
    if offset == 0 {
        byte_base
    } else {
        CExpr::Binary(
            if offset > 0 {
                BinaryOp::Add
            } else {
                BinaryOp::Sub
            },
            Box::new(byte_base),
            Box::new(CExpr::int(offset.unsigned_abs() as i64)),
        )
    }
}

fn memcpy_load_expr(access_ty: CType, address: CExpr) -> CExpr {
    let object = CExpr::CompoundLit(access_ty.clone(), vec![Initializer::Expr(CExpr::int(0))]);
    let destination = CExpr::Unary(UnaryOp::AddrOf, Box::new(object));
    let source = CExpr::Cast(CType::ptr(CType::Void), Box::new(address));
    let copy = CExpr::Call(
        Box::new(CExpr::Var("__builtin_memcpy".to_string())),
        vec![destination, source, CExpr::SizeofType(access_ty.clone())],
    );
    CExpr::Unary(
        UnaryOp::Deref,
        Box::new(CExpr::Cast(CType::ptr(access_ty), Box::new(copy))),
    )
}

fn memcpy_store_expr(access_ty: CType, address: CExpr, value: CExpr) -> CExpr {
    let destination = CExpr::Cast(CType::ptr(CType::Void), Box::new(address));
    let source_object = CExpr::CompoundLit(
        access_ty.clone(),
        vec![Initializer::Expr(CExpr::Cast(
            access_ty.clone(),
            Box::new(value),
        ))],
    );
    let source = CExpr::Unary(UnaryOp::AddrOf, Box::new(source_object));
    CExpr::Call(
        Box::new(CExpr::Var("__builtin_memcpy".to_string())),
        vec![destination, source, CExpr::SizeofType(access_ty)],
    )
}

fn ctype_is_byte(ty: &CType) -> bool {
    matches!(
        ty,
        CType::Int(IntSize::Char, Signedness::Signed | Signedness::Unsigned)
    )
}

fn ctype_needs_byte_copy(ty: &CType) -> bool {
    match ty {
        CType::Int(IntSize::Char, _) | CType::Bool => false,
        CType::Int(..) | CType::Float(..) => true,
        CType::Pointer(_, qualifiers) => !qualifiers.is_volatile,
        CType::Qualified(inner, qualifiers) => {
            !qualifiers.is_volatile && ctype_needs_byte_copy(inner)
        }
        _ => false,
    }
}

fn expression_is_rooted_in_byte_buffer(expr: &CExpr, types: &HashMap<String, CType>) -> bool {
    match expr {
        CExpr::Var(name) => matches!(
            types.get(name),
            Some(CType::Array(element, _)) if ctype_is_byte(element)
        ),
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) => expression_is_rooted_in_byte_buffer(inner, types),
        CExpr::Binary(_, left, right) | CExpr::Index(left, right) => {
            expression_is_rooted_in_byte_buffer(left, types)
                || expression_is_rooted_in_byte_buffer(right, types)
        }
        CExpr::Ternary(cond, yes, no) => {
            expression_is_rooted_in_byte_buffer(cond, types)
                || expression_is_rooted_in_byte_buffer(yes, types)
                || expression_is_rooted_in_byte_buffer(no, types)
        }
        _ => false,
    }
}

// Return the exact scalar access type and byte address for a dereference
// synthesized over recovered character-array storage.
fn byte_buffer_scalar_access(
    expr: &CExpr,
    types: &HashMap<String, CType>,
) -> Option<(CType, CExpr)> {
    if let CExpr::Paren(inner) = expr {
        return byte_buffer_scalar_access(inner, types);
    }
    let CExpr::Unary(UnaryOp::Deref, pointer) = expr else {
        return None;
    };
    let CExpr::Cast(CType::Pointer(access_ty, _), address) = pointer.as_ref() else {
        return None;
    };
    if !ctype_needs_byte_copy(access_ty) || !expression_is_rooted_in_byte_buffer(address, types) {
        return None;
    }
    Some(((**access_ty).clone(), (**address).clone()))
}

fn compound_assign_binary_op(op: AssignOp) -> Option<BinaryOp> {
    match op {
        AssignOp::Assign => None,
        AssignOp::AddAssign => Some(BinaryOp::Add),
        AssignOp::SubAssign => Some(BinaryOp::Sub),
        AssignOp::MulAssign => Some(BinaryOp::Mul),
        AssignOp::DivAssign => Some(BinaryOp::Div),
        AssignOp::ModAssign => Some(BinaryOp::Mod),
        AssignOp::AndAssign => Some(BinaryOp::BitAnd),
        AssignOp::OrAssign => Some(BinaryOp::BitOr),
        AssignOp::XorAssign => Some(BinaryOp::BitXor),
        AssignOp::ShlAssign => Some(BinaryOp::Shl),
        AssignOp::ShrAssign => Some(BinaryOp::Shr),
    }
}

fn lower_byte_buffer_expr(expr: &CExpr, types: &HashMap<String, CType>) -> CExpr {
    if let Some((access_ty, address)) = byte_buffer_scalar_access(expr, types) {
        return memcpy_load_expr(access_ty, lower_byte_buffer_expr(&address, types));
    }
    match expr {
        // Address and unevaluated contexts must never trigger the value-load
        // fallback.  `&*(T *)addr` is simply that typed pointer.
        CExpr::Unary(UnaryOp::AddrOf, inner) => {
            if let Some((access_ty, address)) = byte_buffer_scalar_access(inner, types) {
                return CExpr::Cast(
                    CType::ptr(access_ty),
                    Box::new(lower_byte_buffer_expr(&address, types)),
                );
            }
            CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(lower_byte_buffer_expr(inner, types)),
            )
        }
        CExpr::SizeofExpr(_) => expr.clone(),
        CExpr::Assign(AssignOp::Assign, lhs, rhs) => {
            if let Some((access_ty, address)) = byte_buffer_scalar_access(lhs, types) {
                let store = memcpy_store_expr(
                    access_ty.clone(),
                    lower_byte_buffer_expr(&address, types),
                    lower_byte_buffer_expr(rhs, types),
                );
                // Assignment is itself an expression.  Load back through the
                // returned destination pointer so address and RHS are each
                // evaluated once without an unaligned typed dereference.
                return memcpy_load_expr(access_ty, store);
            }
            CExpr::Assign(
                AssignOp::Assign,
                Box::new(lower_byte_buffer_expr(lhs, types)),
                Box::new(lower_byte_buffer_expr(rhs, types)),
            )
        }
        CExpr::Assign(op, lhs, rhs) => {
            if let (Some(binary_op), Some((access_ty, address))) = (
                compound_assign_binary_op(*op),
                byte_buffer_scalar_access(lhs, types),
            ) {
                // Recovered byte-buffer coordinates are pure address
                // expressions.  If a future producer supplies a side effect,
                // retain the original lvalue rather than evaluating it twice.
                if address.has_side_effects() {
                    return expr.clone();
                }
                let lowered_address = lower_byte_buffer_expr(&address, types);
                let old_value = memcpy_load_expr(access_ty.clone(), lowered_address.clone());
                let new_value = CExpr::Binary(
                    binary_op,
                    Box::new(old_value),
                    Box::new(lower_byte_buffer_expr(rhs, types)),
                );
                let store = memcpy_store_expr(access_ty.clone(), lowered_address, new_value);
                return memcpy_load_expr(access_ty, store);
            }
            CExpr::Assign(
                *op,
                Box::new(lower_byte_buffer_expr(lhs, types)),
                Box::new(lower_byte_buffer_expr(rhs, types)),
            )
        }
        CExpr::Unary(
            op @ (UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec),
            inner,
        ) if byte_buffer_scalar_access(inner, types).is_some() => {
            // A correct post-inc/dec lowering needs an explicit single-use
            // old-value temporary.  Keep the original lvalue until that
            // representation exists; converting only its read would mutate a
            // temporary and change behavior.
            CExpr::Unary(*op, inner.clone())
        }
        CExpr::Unary(op, inner) => {
            CExpr::Unary(*op, Box::new(lower_byte_buffer_expr(inner, types)))
        }
        CExpr::Binary(op, left, right) => CExpr::Binary(
            *op,
            Box::new(lower_byte_buffer_expr(left, types)),
            Box::new(lower_byte_buffer_expr(right, types)),
        ),
        CExpr::Ternary(cond, yes, no) => CExpr::Ternary(
            Box::new(lower_byte_buffer_expr(cond, types)),
            Box::new(lower_byte_buffer_expr(yes, types)),
            Box::new(lower_byte_buffer_expr(no, types)),
        ),
        CExpr::Call(callee, args) => CExpr::Call(
            Box::new(lower_byte_buffer_expr(callee, types)),
            args.iter()
                .map(|arg| lower_byte_buffer_expr(arg, types))
                .collect(),
        ),
        CExpr::Cast(ty, inner) => {
            CExpr::Cast(ty.clone(), Box::new(lower_byte_buffer_expr(inner, types)))
        }
        CExpr::Member(inner, field) => CExpr::Member(
            Box::new(lower_byte_buffer_expr(inner, types)),
            field.clone(),
        ),
        CExpr::MemberPtr(inner, field) => CExpr::MemberPtr(
            Box::new(lower_byte_buffer_expr(inner, types)),
            field.clone(),
        ),
        CExpr::Index(base, index) => CExpr::Index(
            Box::new(lower_byte_buffer_expr(base, types)),
            Box::new(lower_byte_buffer_expr(index, types)),
        ),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(lower_byte_buffer_expr(inner, types))),
        CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
            ty.clone(),
            initializers
                .iter()
                .map(|init| {
                    transform_initializer_exprs(init, &|nested| {
                        lower_byte_buffer_expr(nested, types)
                    })
                })
                .collect(),
        ),
        // The controlling expression of _Generic is unevaluated.  Transform
        // every association conservatively; only the selected one will run.
        CExpr::Generic(selector, arms) => CExpr::Generic(
            selector.clone(),
            arms.iter()
                .map(|(ty, arm)| (ty.clone(), lower_byte_buffer_expr(arm, types)))
                .collect(),
        ),
        CExpr::StmtExpr(stmts, tail) => CExpr::StmtExpr(
            stmts
                .iter()
                .map(|stmt| lower_byte_buffer_stmt(stmt, types))
                .collect(),
            Box::new(lower_byte_buffer_expr(tail, types)),
        ),
        _ => expr.clone(),
    }
}

fn lower_byte_buffer_initializer(
    init: &Initializer,
    types: &HashMap<String, CType>,
) -> Initializer {
    transform_initializer_exprs(init, &|expr| lower_byte_buffer_expr(expr, types))
}

fn lower_byte_buffer_decls(decls: &[VarDecl], types: &HashMap<String, CType>) -> Vec<VarDecl> {
    decls
        .iter()
        .map(|decl| VarDecl {
            init: decl
                .init
                .as_ref()
                .map(|init| lower_byte_buffer_initializer(init, types)),
            ..decl.clone()
        })
        .collect()
}

fn lower_byte_buffer_stmt(stmt: &CStmt, types: &HashMap<String, CType>) -> CStmt {
    match stmt {
        CStmt::Expr(CExpr::Assign(AssignOp::Assign, lhs, rhs)) => {
            if let Some((access_ty, address)) = byte_buffer_scalar_access(lhs, types) {
                return CStmt::Expr(memcpy_store_expr(
                    access_ty,
                    lower_byte_buffer_expr(&address, types),
                    lower_byte_buffer_expr(rhs, types),
                ));
            }
            CStmt::Expr(lower_byte_buffer_expr(
                &CExpr::Assign(AssignOp::Assign, lhs.clone(), rhs.clone()),
                types,
            ))
        }
        CStmt::Expr(expr) => CStmt::Expr(lower_byte_buffer_expr(expr, types)),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(stmt) => CBlockItem::Stmt(lower_byte_buffer_stmt(stmt, types)),
                    CBlockItem::Decl(decls) => {
                        CBlockItem::Decl(lower_byte_buffer_decls(decls, types))
                    }
                })
                .collect(),
        ),
        CStmt::If(cond, yes, no) => CStmt::If(
            lower_byte_buffer_expr(cond, types),
            Box::new(lower_byte_buffer_stmt(yes, types)),
            no.as_ref()
                .map(|stmt| Box::new(lower_byte_buffer_stmt(stmt, types))),
        ),
        CStmt::Switch(expr, body) => CStmt::Switch(
            lower_byte_buffer_expr(expr, types),
            Box::new(lower_byte_buffer_stmt(body, types)),
        ),
        CStmt::While(cond, body) => CStmt::While(
            lower_byte_buffer_expr(cond, types),
            Box::new(lower_byte_buffer_stmt(body, types)),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(lower_byte_buffer_stmt(body, types)),
            lower_byte_buffer_expr(cond, types),
        ),
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.as_ref().map(|init| match init {
                ForInit::Expr(expr) => ForInit::Expr(lower_byte_buffer_expr(expr, types)),
                ForInit::Decl(decls) => ForInit::Decl(lower_byte_buffer_decls(decls, types)),
            }),
            cond.as_ref()
                .map(|expr| lower_byte_buffer_expr(expr, types)),
            update
                .as_ref()
                .map(|expr| lower_byte_buffer_expr(expr, types)),
            Box::new(lower_byte_buffer_stmt(body, types)),
        ),
        CStmt::Return(Some(expr)) => CStmt::Return(Some(lower_byte_buffer_expr(expr, types))),
        CStmt::Labeled(label, body) => {
            CStmt::Labeled(label.clone(), Box::new(lower_byte_buffer_stmt(body, types)))
        }
        CStmt::Effect(label, body) => {
            CStmt::Effect(label.clone(), Box::new(lower_byte_buffer_stmt(body, types)))
        }
        CStmt::Decl(decls) => CStmt::Decl(lower_byte_buffer_decls(decls, types)),
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts
                .iter()
                .map(|stmt| lower_byte_buffer_stmt(stmt, types))
                .collect(),
        ),
        _ => stmt.clone(),
    }
}

fn unsigned_integer_clight_type(ty: &clight::ClightType) -> Option<clight::ClightType> {
    match ty {
        clight::ClightType::Tint(size, _, attr) => Some(clight::ClightType::Tint(
            *size,
            clight::ClightSignedness::Unsigned,
            attr.clone(),
        )),
        clight::ClightType::Tlong(_, attr) => Some(clight::ClightType::Tlong(
            clight::ClightSignedness::Unsigned,
            attr.clone(),
        )),
        clight::ClightType::Tint128(_, attr) => Some(clight::ClightType::Tint128(
            clight::ClightSignedness::Unsigned,
            attr.clone(),
        )),
        _ => None,
    }
}

pub fn convert_expr(expr: &clight::ClightExpr, ctx: &mut ConversionContext) -> CExpr {
    match expr {
        clight::ClightExpr::EconstInt(val, ty) => {
            let unsigned = matches!(ty, clight::ClightType::Tint(clight::ClightIntSize::I32, clight::ClightSignedness::Unsigned, _));
            let literal = if !unsigned && *val == i32::MIN {
                // C parses the minus separately; bare -2147483648 has a
                // wider positive literal and therefore the wrong type.
                CExpr::Binary(BinaryOp::Sub, Box::new(CExpr::int(i32::MIN as i64 + 1)), Box::new(CExpr::int(1)))
            } else { CExpr::IntLit(IntLiteral {
                value: if unsigned { *val as u32 as i128 } else { *val as i128 },
                suffix: if unsigned { IntLiteralSuffix::U } else { IntLiteralSuffix::None },
                base: IntLiteralBase::Decimal,
            }) };
            if matches!(ty, clight::ClightType::Tint(clight::ClightIntSize::I8 | clight::ClightIntSize::I16 | clight::ClightIntSize::IBool, _, _)) {
                // Subword values undergo integer promotion at their use. An
                // unsigned byte is not an unsigned-int literal.
                CExpr::Cast(convert_clight_type(ty, ctx.data_model), Box::new(literal))
            } else { literal }
        }
        clight::ClightExpr::EconstLong(val, ty) => {
            let unsigned = matches!(ty, clight::ClightType::Tlong(clight::ClightSignedness::Unsigned, _));
            let suffix = match (ctx.data_model.long_holds_64bit(), unsigned) {
                (true, false) => IntLiteralSuffix::L,
                (true, true) => IntLiteralSuffix::UL,
                (false, false) => IntLiteralSuffix::LL,
                (false, true) => IntLiteralSuffix::ULL,
            };
            let literal = |value| CExpr::IntLit(IntLiteral { value, suffix, base: IntLiteralBase::Decimal });
            if !unsigned && *val == i64::MIN {
                return CExpr::Binary(BinaryOp::Sub, Box::new(literal(i64::MIN as i128 + 1)), Box::new(literal(1)));
            }
            literal(if unsigned { *val as u64 as i128 } else { *val as i128 })
        }
        clight::ClightExpr::EconstFloat(val, _ty) => CExpr::FloatLit(FloatLiteral {
            value: val.0,
            suffix: FloatLiteralSuffix::None,
        }),
        clight::ClightExpr::EconstSingle(val, _ty) => CExpr::FloatLit(FloatLiteral {
            value: val.0 as f64,
            suffix: FloatLiteralSuffix::F,
        }),
        clight::ClightExpr::Evar(id, ty) => {
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
            if let Some(alias) = ctx.global_lvalue_aliases.get(id) {
                // The owner declaration models storage; the Clight Evar type
                // models this particular machine access.  Keep both.  The
                // typed dereference remains an lvalue for stores and turns
                // `&Evar` into the correctly typed interior pointer, while a
                // signed/extended load does not inherit an arbitrary owner
                // element signedness.
                return match ty {
                    clight::ClightType::Tvoid
                    | clight::ClightType::Tarray(..)
                    | clight::ClightType::Tfunction(..) => alias.clone(),
                    _ => CExpr::Unary(
                        UnaryOp::Deref,
                        Box::new(CExpr::Cast(
                            CType::ptr(convert_clight_type(ty, ctx.data_model)),
                            Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(alias.clone()))),
                        )),
                    ),
                };
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
            let sanitized = sanitize_c_symbol_name(name);
            // Track header-collision renames (local `atexit` definition -> `atexit_local`) so calls and address-of references target the renamed local definition.
            match ctx.func_renames.get(&sanitized) {
                Some(renamed) => CExpr::Var(renamed.clone()),
                None => CExpr::Var(sanitized),
            }
        }
        clight::ClightExpr::Etempvar(id, _ty) => CExpr::Var(ctx.temp_name(*id)),
        clight::ClightExpr::Ederef(inner, ty) => {
            if should_lower_scalar_deref(inner, ty) {
                return memcpy_load_expr(
                    convert_clight_type(ty, ctx.data_model),
                    convert_expr(inner, ctx),
                );
            }
            // Materialize the node's ACCESS type as *(T *)base: always for a bare variable, whose decl may lawfully diverge, and for a composite base unless its annotation already points to the access type.
            let access_castable = matches!(
                ty,
                clight::ClightType::Tint(..)
                    | clight::ClightType::Tlong(..)
                    | clight::ClightType::Tfloat(..)
                    | clight::ClightType::Tpointer(..)
            );
            if access_castable {
                let need_cast = match inner.as_ref() {
                    clight::ClightExpr::Etempvar(..) | clight::ClightExpr::Evar(..) => true,
                    other => !matches!(
                        clight_expr_ctype(other),
                        clight::ClightType::Tpointer(p, _) if p.as_ref() == ty
                    ),
                };
                if need_cast {
                    let cty = CType::ptr(convert_clight_type(ty, ctx.data_model));
                    return CExpr::Unary(
                        UnaryOp::Deref,
                        Box::new(CExpr::Cast(cty, Box::new(convert_expr(inner, ctx)))),
                    );
                }
            }
            CExpr::Unary(UnaryOp::Deref, Box::new(convert_expr(inner, ctx)))
        }
        clight::ClightExpr::Eaddrof(inner, ty) => {
            // Address formation is an lvalue context.  In particular, `&*p`
            // must not perform the memcpy value-load used for an ordinary
            // dereference, nor may `&p->field` return the address of that
            // load's temporary compound literal.  Preserve the original
            // machine byte address and materialize only the selected pointer
            // spelling.
            if let clight::ClightExpr::Ederef(address, _) = inner.as_ref() {
                return CExpr::Cast(
                    convert_clight_type(ty, ctx.data_model),
                    Box::new(convert_expr(address, ctx)),
                );
            }
            if let clight::ClightExpr::Efield(base, field_id, _) = inner.as_ref() {
                if let clight::ClightExpr::Ederef(address, _) = base.as_ref() {
                    return CExpr::Cast(
                        convert_clight_type(ty, ctx.data_model),
                        Box::new(byte_offset_expr(
                            convert_expr(address, ctx),
                            *field_id as i64,
                        )),
                    );
                }
            }
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
            let address = CExpr::Unary(UnaryOp::AddrOf, Box::new(convert_expr(inner, ctx)));
            // An Evar's Clight type describes this particular memory access,
            // while its eventual C declaration can be replaced by a wider
            // byte-buffer owner during exact stack-layout coalescing.  Keep
            // the address node's pointer type explicit before that later
            // rewrite: otherwise `&int_slot + i` can silently become
            // `&*(long *)&buffer[0] + i`, changing the machine stride from
            // four bytes to eight.  Named image globals retain their dedicated
            // byte-coordinate lowering at the surrounding binary operator,
            // and interior-global aliases already carry a typed dereference
            // around their owner coordinate, so neither needs this cast.
            if matches!(ty, clight::ClightType::Tpointer(..))
                && matches!(
                    inner.as_ref(),
                    clight::ClightExpr::Evar(id, _)
                        if !ctx.global_lvalue_aliases.contains_key(id)
                            && !ctx.id_to_name.contains_key(id)
                )
            {
                CExpr::Cast(convert_clight_type(ty, ctx.data_model), Box::new(address))
            } else {
                address
            }
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
            // B2 mis-scaling fix: byte-addressed candidates annotate their base void * without a cast node, so materialize (RT)((char *)v + k) and the C stays byte-correct under any final declaration.
            if matches!(
                op,
                clight::ClightBinaryOp::Oadd | clight::ClightBinaryOp::Osub
            ) {
                let (bare, vt) = match lhs.as_ref() {
                    clight::ClightExpr::Etempvar(_, vt) | clight::ClightExpr::Evar(_, vt) => {
                        (true, vt)
                    }
                    other => (false, clight_expr_ctype(other)),
                };
                // C has no floating-point form of pointer arithmetic, so a float rhs is proof this Oadd/Osub is ordinary arithmetic however the lhs was annotated. Taking the pointer path there emits `char * - double`, which gcc rejects outright and which cost stripped sort its whole relink; the plain form below is `long - double` and is already correct.
                let rhs_is_float = matches!(clight_expr_ctype(rhs), clight::ClightType::Tfloat(..));
                // Addition is commutative, and Cminor offsets are byte units.
                // Handle `integer + pointer` symmetrically with the established
                // pointer-base path.  This matters for Oaddrsymbol(_, 0): its
                // void* annotation is the only byte-stride marker after a
                // recovered global is widened to an array/aggregate owner.
                let lhs_is_integral = matches!(
                    clight_expr_ctype(lhs),
                    clight::ClightType::Tint(..) | clight::ClightType::Tlong(..)
                );
                if matches!(op, clight::ClightBinaryOp::Oadd) && lhs_is_integral {
                    if let clight::ClightType::Tpointer(pointee, _) = clight_expr_ctype(rhs) {
                        let is_void = matches!(pointee.as_ref(), clight::ClightType::Tvoid);
                        let base_cty = if is_void {
                            CType::ptr(CType::char_signed())
                        } else {
                            convert_clight_type(clight_expr_ctype(rhs), ctx.data_model)
                        };
                        let base = CExpr::Cast(base_cty.clone(), Box::new(convert_expr(rhs, ctx)));
                        let offset = convert_expr(lhs, ctx);
                        let sum = CExpr::Binary(BinaryOp::Add, Box::new(base), Box::new(offset));
                        let result_cty = convert_clight_type(_ty, ctx.data_model);
                        return if result_cty == base_cty {
                            sum
                        } else {
                            CExpr::Cast(result_cty, Box::new(CExpr::Paren(Box::new(sum))))
                        };
                    }
                }
                if let (false, clight::ClightType::Tpointer(p, _)) = (rhs_is_float, vt) {
                    // A void pointee means byte-add, so scale through char *; a composite base realizes its own annotation faithfully except void *, which C cannot scale or deref through.
                    let is_void = matches!(p.as_ref(), clight::ClightType::Tvoid);
                    // The OFFSET operand of pointer arithmetic must print as an integer, since a pointer-annotated rhs is a byte count wearing the wrong type; Osub keeps a pointer rhs as legal pointer difference.
                    let rhs_is_ptr =
                        matches!(clight_expr_ctype(rhs), clight::ClightType::Tpointer(..))
                            && matches!(op, clight::ClightBinaryOp::Oadd);
                    let rhs_field_int = matches!(rhs.as_ref(), clight::ClightExpr::Efield(..))
                        && matches!(
                            clight_expr_ctype(rhs),
                            clight::ClightType::Tint(..) | clight::ClightType::Tlong(..)
                        );
                    let rhs_is_ptr = rhs_is_ptr || rhs_field_int;
                    if bare || is_void || rhs_is_ptr {
                        let base_cty = if is_void {
                            CType::ptr(CType::char_signed())
                        } else {
                            convert_clight_type(vt, ctx.data_model)
                        };
                        let base = CExpr::Cast(base_cty.clone(), Box::new(convert_expr(lhs, ctx)));
                        let offset = if rhs_is_ptr {
                            CExpr::Cast(CType::long(), Box::new(convert_expr(rhs, ctx)))
                        } else {
                            convert_expr(rhs, ctx)
                        };
                        let sum =
                            CExpr::Binary(convert_binary_op(op), Box::new(base), Box::new(offset));
                        // In C the sum already has the base cast's type; an outer cast only adds information when the annotated result type differs.
                        let result_cty = convert_clight_type(_ty, ctx.data_model);
                        return if result_cty == base_cty {
                            sum
                        } else {
                            CExpr::Cast(result_cty, Box::new(CExpr::Paren(Box::new(sum))))
                        };
                    }
                }
            }
            // x86 left shifts are fixed-width bitvector operations.  C signed
            // left shift is undefined on overflow or a negative operand, and
            // target-specific shift-count behavior belongs in the earlier
            // machine/IR lowering.  Here we only select the corresponding
            // unsigned carrier, preventing C signed-shift UB without inventing
            // an architecture-independent count mask.
            if matches!(op, clight::ClightBinaryOp::Oshl) {
                if let Some(unsigned_ty) = unsigned_integer_clight_type(_ty) {
                    let unsigned_cty = convert_clight_type(&unsigned_ty, ctx.data_model);
                    let result_cty = convert_clight_type(_ty, ctx.data_model);
                    let unsigned_lhs =
                        CExpr::Cast(unsigned_cty, Box::new(convert_integer_operand(lhs, ctx)));
                    let shifted = CExpr::Binary(
                        BinaryOp::Shl,
                        Box::new(unsigned_lhs),
                        Box::new(convert_integer_operand(rhs, ctx)),
                    );
                    return CExpr::Cast(result_cty, Box::new(CExpr::Paren(Box::new(shifted))));
                }
            }
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
            let lhs_expr = convert_integer_operand(lhs, ctx);
            let rhs_expr = convert_integer_operand(rhs, ctx);
            ctx.suppress_string_literals = prev_suppress;
            CExpr::Binary(
                convert_binary_op(op),
                Box::new(lhs_expr),
                Box::new(rhs_expr),
            )
        }
        clight::ClightExpr::Ecast(inner, ty) => CExpr::Cast(
            convert_clight_type(ty, ctx.data_model),
            Box::new(convert_expr(inner, ctx)),
        ),
        clight::ClightExpr::Efield(inner, field_id, field_ty) => {
            if let clight::ClightExpr::Ederef(address, aggregate_ty) = inner.as_ref() {
                if should_lower_scalar_field(address, aggregate_ty, field_ty) {
                    return memcpy_load_expr(
                        convert_clight_type(field_ty, ctx.data_model),
                        byte_offset_expr(convert_expr(address, ctx), *field_id as i64),
                    );
                }
            }
            let inner_expr = convert_expr(inner, ctx);
            let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_id);
            let inner_ct = clight_expr_to_ctype(inner, ctx.data_model);

            match &inner_expr {
                CExpr::Unary(UnaryOp::Deref, ptr_expr) => {
                    // The field access is well-typed in clight (base derefs to a struct/union), but the emitted C declaration of the base pointer can disagree (type recovery may type it as int*/void*); cast the base to the struct pointer so `->` type-checks.
                    if let Some(aggregate_ty) = aggregate_member_base_type(&inner_ct) {
                        let sptr = CType::Pointer(Box::new(aggregate_ty), TypeQualifiers::none());
                        CExpr::MemberPtr(Box::new(CExpr::Cast(sptr, ptr_expr.clone())), field_name)
                    } else {
                        // The base derefs to a non-aggregate, so lower ->ofs_N to a typed byte-offset deref *(FieldTy *)((char *)base + N); the field ident encodes N and FieldTy is always a concrete scalar.
                        let offset = *field_id as i64;
                        let field_ctype = convert_clight_type(field_ty, ctx.data_model);
                        let char_ptr =
                            CType::Pointer(Box::new(CType::char_signed()), TypeQualifiers::none());
                        let byte_addr = CExpr::Binary(
                            BinaryOp::Add,
                            Box::new(CExpr::Cast(char_ptr, ptr_expr.clone())),
                            Box::new(CExpr::int(offset)),
                        );
                        let field_ptr =
                            CType::Pointer(Box::new(field_ctype), TypeQualifiers::none());
                        CExpr::Unary(
                            UnaryOp::Deref,
                            Box::new(CExpr::Cast(field_ptr, Box::new(byte_addr))),
                        )
                    }
                }
                _ => CExpr::Member(Box::new(inner_expr), field_name),
            }
        }
        clight::ClightExpr::Esizeof(ty, _result_ty) => {
            CExpr::SizeofType(convert_clight_type(ty, ctx.data_model))
        }
        clight::ClightExpr::Ealignof(ty, _result_ty) => {
            CExpr::AlignofType(convert_clight_type(ty, ctx.data_model))
        }
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
                        Some('%') => {
                            chars.next();
                        } // %% is literal
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
            let items: Vec<CBlockItem> =
                stmts.iter().map(|s| CBlockItem::Stmt(s.clone())).collect();
            let pruned = prune_block_items(&items);
            let stmts: Vec<CStmt> = pruned
                .into_iter()
                .filter_map(|item| match item {
                    CBlockItem::Stmt(s) => Some(s),
                    _ => None,
                })
                .collect();
            match stmts.len() {
                0 => CStmt::Empty,
                1 => stmts.into_iter().next().unwrap(),
                _ => CStmt::Sequence(stmts),
            }
        }
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            cond.clone(),
            Box::new(eliminate_dead_code(then_s)),
            else_s.as_ref().map(|e| Box::new(eliminate_dead_code(e))),
        ),
        CStmt::While(cond, body) => CStmt::While(cond.clone(), Box::new(eliminate_dead_code(body))),
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(eliminate_dead_code(body)), cond.clone())
        }
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            update.clone(),
            Box::new(eliminate_dead_code(body)),
        ),
        CStmt::Switch(expr, body) => {
            // Don't prune inside switch bodies (all case/default labels are reachable via dispatch); only recurse into individual case bodies, not the sequential structure.
            CStmt::Switch(expr.clone(), Box::new(eliminate_dead_code_in_switch(body)))
        }
        CStmt::Labeled(label, inner) => {
            CStmt::Labeled(label.clone(), Box::new(eliminate_dead_code(inner)))
        }
        CStmt::Effect(label, inner) => {
            CStmt::Effect(label.clone(), Box::new(eliminate_dead_code(inner)))
        }
        other => other.clone(),
    }
}

/// Recurse into switch body items without pruning between them (all cases are dispatch targets).
fn eliminate_dead_code_in_switch(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Block(items) => {
            let cleaned: Vec<CBlockItem> = items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(eliminate_dead_code(s)),
                    other => other.clone(),
                })
                .collect();
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
        CStmt::While(_, _)
        | CStmt::DoWhile(_, _)
        | CStmt::For(_, _, _, _)
        | CStmt::Switch(_, _) => true,
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => is_control_flow_construct(inner),
        _ => false,
    }
}

/// Returns true if stmt unconditionally exits (return/goto/break/continue).
fn is_unconditional_exit(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) | CStmt::Goto(_) | CStmt::Break | CStmt::Continue => true,
        // Labeled stmt exit status depends on inner stmt (subsequent code still dead if inner exits).
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => is_unconditional_exit(inner),
        CStmt::Block(items) => {
            // A block exits if its last statement exits
            items
                .iter()
                .rev()
                .find_map(|item| match item {
                    CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty) => {
                        Some(is_unconditional_exit(s))
                    }
                    _ => None,
                })
                .unwrap_or(false)
        }
        CStmt::Sequence(stmts) => stmts
            .iter()
            .rev()
            .find_map(|s| {
                if !matches!(s, CStmt::Empty) {
                    Some(is_unconditional_exit(s))
                } else {
                    None
                }
            })
            .unwrap_or(false),
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => contains_goto_target(inner),
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => contains_named_label(inner),
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

pub fn convert_stmt_at(stmt: &clight::ClightStmt, ctx: &mut ConversionContext, node: Node) -> CStmt {
    let converted = convert_stmt(stmt, ctx);
    fn primitive(stmt: &clight::ClightStmt) -> bool {
        match stmt {
            clight::ClightStmt::Sassign(..) | clight::ClightStmt::Sset(..) => true,
            clight::ClightStmt::Ssequence(stmts) if stmts.len() == 1 => primitive(&stmts[0]),
            _ => false,
        }
    }
    // A node may name a structured container. Its provenance does not place
    // an effect after the entire loop/branch. Explicit inner labels rebind
    // origins during recursive conversion instead.
    if primitive(stmt) {
        if let Some(effect) = ctx.source_post_effects.get(&node).cloned() {
            if ctx.applied_source_effects.insert(node) {
                return CStmt::Sequence(vec![converted, effect]);
            }
        }
    }
    converted
}

pub fn convert_stmt(stmt: &clight::ClightStmt, ctx: &mut ConversionContext) -> CStmt {
    match stmt {
        clight::ClightStmt::Seffect(site,body) => CStmt::Effect(*site,Box::new(convert_stmt(body,ctx))),
        clight::ClightStmt::Sskip => CStmt::Empty,

        clight::ClightStmt::Sassign(lhs, rhs) => {
            if let clight::ClightExpr::Efield(inner, field_id, field_ty) = lhs {
                if let clight::ClightExpr::Ederef(address, aggregate_ty) = inner.as_ref() {
                    if should_lower_scalar_field(address, aggregate_ty, field_ty) {
                        return CStmt::Expr(memcpy_store_expr(
                            convert_clight_type(field_ty, ctx.data_model),
                            byte_offset_expr(convert_expr(address, ctx), *field_id as i64),
                            convert_expr(rhs, ctx),
                        ));
                    }
                }
            }
            if let clight::ClightExpr::Ederef(address, access_ty) = lhs {
                if should_lower_scalar_deref(address, access_ty) {
                    return CStmt::Expr(memcpy_store_expr(
                        convert_clight_type(access_ty, ctx.data_model),
                        convert_expr(address, ctx),
                        convert_expr(rhs, ctx),
                    ));
                }
            }
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
            let var_type = clight_expr_to_ctype(expr, ctx.data_model);
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
                // RB-1: len()==1 guard makes next() infallible; both arms push CBlockItem::Stmt so the non-Stmt arm is unreachable.
                match converted.into_iter().next().unwrap() {
                    CBlockItem::Stmt(s) => s,
                    _ => unreachable!("Ssequence conversion pushes only CBlockItem::Stmt"),
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
            let update = if has_update {
                extract_loop_update(&cont_stmt)
            } else {
                None
            };

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
                let switch_expr = convert_integer_operand(expr, ctx);
                let body = convert_switch_cases(cases, ctx);
                CStmt::Switch(switch_expr, Box::new(body))
            }
        }

        clight::ClightStmt::Slabel(label_id, inner) => {
            let label_name = ctx.label_name(*label_id);
            let inner_stmt = convert_stmt_at(inner, ctx, *label_id as Node);
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
        CStmt::Block(items) if items.len() >= 1 => items
            .iter()
            .filter_map(|item| match item {
                CBlockItem::Stmt(s) => Some(s),
                _ => None,
            })
            .collect(),
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

    // RB-1: last() is infallible -- is_empty() and len()==1 returns above guarantee >= 2 elements here.
    if let Some(cond) = extract_condition_break(stmts.last().unwrap()) {
        let rest: Vec<CStmt> = stmts[..stmts.len() - 1]
            .iter()
            .map(|s| (*s).clone())
            .collect();
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
                        // RB-1: reduce(None) only on empty iterator; excluded by the !exprs.is_empty() guard above.
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

    // Collapse maximal runs of consecutive cases sharing an identical non-fall-through body into one stacked-label arm; labels are nested so later cleanup treats each arm as a single unit.
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

/// True if `stmt` ends in an unconditional control transfer, so control never falls off its end. Stacking consecutive same-bodied switch cases under shared labels is sound only when the shared body cannot fall through into the following case.
fn switch_body_exits(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Goto(_) | CStmt::Break | CStmt::Continue | CStmt::Return(_) => true,
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => switch_body_exits(inner),
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

/// Number of disjoint value ranges above which a single-target switch is left as a switch rather than expanded into an `||` chain of range tests (keeps a genuinely sparse set readable as a switch).
const MAX_RANGE_IF_RUNS: usize = 8;

/// Converts a single-target switch (all cases share one non-fall-through body) into a range `if` test. Requires: duplicable scrutinee (evaluated multiple times), non-negative case values (so `>=`/`<=` matches the switch's signedness semantics), and every emitted range covers only real case values.
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

    let scrutinee = convert_integer_operand(expr, ctx);
    let mut condition: Option<CExpr> = None;
    for (lo, hi) in runs {
        let part = if lo == hi {
            CExpr::Binary(
                BinaryOp::Eq,
                Box::new(scrutinee.clone()),
                Box::new(CExpr::int(lo)),
            )
        } else {
            // Wrap each `e>=lo && e<=hi` group in parens so a multi-range condition reads as `(e>=lo && e<=hi) || (e>=lo2 && e<=hi2)` rather than relying on C's &&-over-|| precedence.
            CExpr::Paren(Box::new(CExpr::Binary(
                BinaryOp::And,
                Box::new(CExpr::Binary(
                    BinaryOp::Ge,
                    Box::new(scrutinee.clone()),
                    Box::new(CExpr::int(lo)),
                )),
                Box::new(CExpr::Binary(
                    BinaryOp::Le,
                    Box::new(scrutinee.clone()),
                    Box::new(CExpr::int(hi)),
                )),
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

/// True if expr can be evaluated more than once without changing behavior; excludes memory reads so a range if never duplicates a load that could alias or be volatile.
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

/// True if a Clight statement ends in an unconditional control transfer (mirrors `switch_body_exits` at the Clight level, before conversion to the C AST).
fn clight_stmt_exits(stmt: &clight::ClightStmt) -> bool {
    match stmt {
        clight::ClightStmt::Sgoto(_)
        | clight::ClightStmt::Sbreak
        | clight::ClightStmt::Scontinue
        | clight::ClightStmt::Sreturn(_) => true,
        (clight::ClightStmt::Slabel(_, inner) | clight::ClightStmt::Seffect(_, inner)) => clight_stmt_exits(inner),
        clight::ClightStmt::Ssequence(stmts) => stmts.last().map_or(false, clight_stmt_exits),
        _ => false,
    }
}

fn collect_clight_goto_targets(
    stmt: &clight::ClightStmt,
    targets: &mut HashSet<crate::x86::types::Node>,
) {
    match stmt {
        clight::ClightStmt::Sgoto(target) => {
            targets.insert(*target as crate::x86::types::Node);
        }
        clight::ClightStmt::Ssequence(stmts) => {
            for stmt in stmts {
                collect_clight_goto_targets(stmt, targets);
            }
        }
        clight::ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            collect_clight_goto_targets(then_stmt, targets);
            collect_clight_goto_targets(else_stmt, targets);
        }
        clight::ClightStmt::Sloop(body, incr) => {
            collect_clight_goto_targets(body, targets);
            collect_clight_goto_targets(incr, targets);
        }
        clight::ClightStmt::Sswitch(_, cases) => {
            for (_, stmt) in cases {
                collect_clight_goto_targets(stmt, targets);
            }
        }
        (clight::ClightStmt::Slabel(_, inner) | clight::ClightStmt::Seffect(_, inner)) => {
            collect_clight_goto_targets(inner, targets);
        }
        _ => {}
    }
}

/// Ordering edges carried by the selected statement tree rather than `clight_succ`.
/// Only exact surviving top-level targets matter: absorbed loop/switch members have no
/// independent C statement to order.
fn structured_goto_order_edges(
    statements: &HashMap<crate::x86::types::Node, clight::ClightStmt>,
    surviving_nodes: &HashSet<crate::x86::types::Node>,
) -> Vec<(crate::x86::types::Node, crate::x86::types::Node)> {
    let mut sources: Vec<_> = statements.keys().copied().collect();
    sources.sort_unstable();

    let mut edges = Vec::new();
    for source in sources {
        if !surviving_nodes.contains(&source) {
            continue;
        }
        let mut targets = HashSet::new();
        collect_clight_goto_targets(&statements[&source], &mut targets);
        for target in targets {
            if target != source && surviving_nodes.contains(&target) {
                edges.push((source, target));
            }
        }
    }
    edges.sort_unstable();
    edges.dedup();
    edges
}

fn contains_structured_clight_loop(stmt: &clight::ClightStmt) -> bool {
    match stmt {
        clight::ClightStmt::Sloop(_, _) => true,
        clight::ClightStmt::Ssequence(stmts) => stmts.iter().any(contains_structured_clight_loop),
        clight::ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            contains_structured_clight_loop(then_stmt) || contains_structured_clight_loop(else_stmt)
        }
        clight::ClightStmt::Sswitch(_, cases) => cases
            .iter()
            .any(|(_, stmt)| contains_structured_clight_loop(stmt)),
        (clight::ClightStmt::Slabel(_, inner) | clight::ClightStmt::Seffect(_, inner)) => contains_structured_clight_loop(inner),
        _ => false,
    }
}

/// Reconnect a surviving structured loop header that statement selection detached from
/// its raw CFG entry. A rewrite is allowed only when the header has one raw in-loop
/// successor and every edge reached from the function entry without first entering
/// the natural-loop body enters that same normalized frontier. Later body re-entries
/// are therefore not mistaken for preheaders. This is a structural single-entry
/// check; node order is never consulted.
fn redirect_structured_loop_entry_edges<F>(
    entry: crate::x86::types::Node,
    statements: &HashMap<crate::x86::types::Node, clight::ClightStmt>,
    surviving_nodes: &HashSet<crate::x86::types::Node>,
    edges: &mut Vec<(crate::x86::types::Node, crate::x86::types::Node)>,
    loop_members: &HashMap<crate::x86::types::Node, HashSet<crate::x86::types::Node>>,
    normalize: F,
) where
    F: Fn(crate::x86::types::Node) -> crate::x86::types::Node + Copy,
{
    type Node = crate::x86::types::Node;

    let original_edges = edges.clone();
    let mut adjacency: HashMap<Node, Vec<Node>> = HashMap::new();
    for &(source, target) in &original_edges {
        if source != target {
            adjacency.entry(source).or_default().push(target);
        }
    }
    let mut headers_by_loop: BTreeMap<Node, Vec<Node>> = BTreeMap::new();
    for (&header, stmt) in statements {
        if surviving_nodes.contains(&header) && contains_structured_clight_loop(stmt) {
            headers_by_loop
                .entry(normalize(header))
                .or_default()
                .push(header);
        }
    }

    let mut plans: Vec<(Node, Node, Vec<(Node, Node)>)> = Vec::new();
    for (loop_key, mut headers) in headers_by_loop {
        // Two surviving structured statements for one natural loop are ambiguous.
        if headers.len() != 1 {
            continue;
        }
        let header = headers.pop().unwrap();
        let Some(body) = loop_members.get(&loop_key) else {
            continue;
        };
        if !body.contains(&loop_key) {
            continue;
        }

        // Remove the loop body from an entry walk. Its frontier is exactly the set
        // of outside nodes that can enter the loop before any iteration has run;
        // nodes reached only after a structured exit/goto are later re-entries.
        let reachable_before_loop: HashSet<Node> = {
            let mut reached = HashSet::new();
            let mut stack = vec![entry];
            while let Some(node) = stack.pop() {
                if body.contains(&normalize(node)) || !reached.insert(node) {
                    continue;
                }
                if let Some(successors) = adjacency.get(&node) {
                    stack.extend(successors.iter().copied());
                }
            }
            reached
        };

        let mut header_body_targets: Vec<Node> = original_edges
            .iter()
            .filter_map(|(source, target)| {
                (*source == header && *target != header && body.contains(&normalize(*target)))
                    .then_some(*target)
            })
            .collect();
        header_body_targets.sort_unstable();
        header_body_targets.dedup();
        if header_body_targets.len() != 1 {
            continue;
        }
        let body_frontier = header_body_targets[0];
        let frontier_key = normalize(body_frontier);

        let external_entries: Vec<(Node, Node)> = original_edges
            .iter()
            .copied()
            .filter(|(source, target)| {
                reachable_before_loop.contains(source)
                    && !body.contains(&normalize(*source))
                    && body.contains(&normalize(*target))
            })
            .collect();
        if external_entries.is_empty() {
            continue;
        }
        // A normal (not detached) structured header already owns this frontier.
        if external_entries.iter().any(|(_, target)| *target == header) {
            continue;
        }
        if external_entries
            .iter()
            .any(|(_, target)| normalize(*target) != frontier_key)
        {
            continue;
        }
        plans.push((header, body_frontier, external_entries));
    }

    // An edge claimed by two nested/aliased loop plans is not safe to redirect for either.
    let mut claims: BTreeMap<(Node, Node), Node> = BTreeMap::new();
    let mut conflicted_headers = HashSet::new();
    for (header, _, entries) in &plans {
        for edge in entries {
            if let Some(previous) = claims.insert(*edge, *header) {
                if previous != *header {
                    conflicted_headers.insert(previous);
                    conflicted_headers.insert(*header);
                }
            }
        }
    }

    for (header, body_frontier, entries) in plans {
        if conflicted_headers.contains(&header) {
            continue;
        }
        let entries: HashSet<_> = entries.into_iter().collect();
        for edge in edges.iter_mut() {
            if entries.contains(edge) {
                edge.1 = header;
            }
        }
        // Preserve the selected header's raw-body continuation after redirecting its inputs.
        edges.push((header, body_frontier));
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
        ExternalFunction::EFAnnot(_, n, _) | ExternalFunction::EFAnnotVal(_, n, _) => {
            sanitize_c_symbol_name(n)
        }
        ExternalFunction::EFDebug(_, _, _) => "__builtin_debug".into(),
    }
}

/// Order statement nodes that the entry walk did not reach by traversing their
/// remaining CFG components. Address order is used only to choose between
/// structurally unrelated roots (and as a deterministic SCC seed), never to
/// order two nodes connected by a control-flow path.
fn order_disconnected_cfg_nodes(
    wanted: &HashSet<crate::x86::types::Node>,
    adjacency: &HashMap<crate::x86::types::Node, Vec<crate::x86::types::Node>>,
    blocked: &HashSet<crate::x86::types::Node>,
) -> Vec<crate::x86::types::Node> {
    type Node = crate::x86::types::Node;

    let mut reverse: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&source, targets) in adjacency {
        for &target in targets {
            reverse.entry(target).or_default().push(source);
        }
    }

    // Restrict traversal to the backwards slice feeding a wanted statement.
    // This includes transparent selected-away nodes between statement-bearing
    // nodes without walking unrelated functions or side components.
    let mut relevant: HashSet<Node> = wanted.clone();
    let mut work: Vec<Node> = wanted.iter().copied().collect();
    while let Some(node) = work.pop() {
        if let Some(predecessors) = reverse.get(&node) {
            for &pred in predecessors {
                if !blocked.contains(&pred) && relevant.insert(pred) {
                    work.push(pred);
                }
            }
        }
    }

    let mut roots: Vec<Node> = relevant
        .iter()
        .copied()
        .filter(|node| {
            reverse.get(node).map_or(true, |preds| {
                preds.iter().all(|pred| !relevant.contains(pred))
            })
        })
        .collect();
    roots.sort_by_key(|node| crate::util::exec_order_key(*node));

    enum ComponentAction {
        Visit(Node),
        PostVisit(Node),
    }

    let visit_component = |seed: Node, seen: &mut HashSet<Node>, ordered: &mut Vec<Node>| {
        let mut actions = vec![ComponentAction::Visit(seed)];
        let mut post_order = Vec::new();
        while let Some(action) = actions.pop() {
            match action {
                ComponentAction::Visit(node) => {
                    if !relevant.contains(&node) || !seen.insert(node) {
                        continue;
                    }
                    actions.push(ComponentAction::PostVisit(node));
                    if let Some(successors) = adjacency.get(&node) {
                        for &successor in successors.iter().rev() {
                            if relevant.contains(&successor) && !seen.contains(&successor) {
                                actions.push(ComponentAction::Visit(successor));
                            }
                        }
                    }
                }
                ComponentAction::PostVisit(node) => {
                    if wanted.contains(&node) {
                        post_order.push(node);
                    }
                }
            }
        }
        ordered.extend(post_order.into_iter().rev());
    };

    let mut seen = HashSet::new();
    let mut ordered = Vec::with_capacity(wanted.len());
    for root in roots {
        visit_component(root, &mut seen, &mut ordered);
    }

    // A remaining natural loop/SCC has no zero-indegree root. The seed only
    // chooses a deterministic rotation of that cycle; DFS still determines
    // every reachable ordering relation inside it.
    while seen.len() < relevant.len() {
        let seed = relevant
            .iter()
            .filter(|node| !seen.contains(node))
            .min_by_key(|node| crate::util::exec_order_key(**node))
            .copied()
            .expect("relevant nonempty while disconnected CFG nodes remain");
        visit_component(seed, &mut seen, &mut ordered);
    }

    debug_assert_eq!(ordered.len(), wanted.len());
    ordered
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OrderedFrontier {
    Unique(crate::x86::types::Node),
    Ambiguous,
}

/// For nodes outside the already ordered entry component, compute the unique
/// first ordered node their CFG paths rejoin. The three-point lattice changes
/// at most twice per node (unknown -> unique -> ambiguous), so propagation is
/// linear in the CFG rather than materializing pairwise reachability.
fn ordered_cfg_frontiers(
    adjacency: &HashMap<crate::x86::types::Node, Vec<crate::x86::types::Node>>,
    ordered: &HashSet<crate::x86::types::Node>,
) -> HashMap<crate::x86::types::Node, OrderedFrontier> {
    type Node = crate::x86::types::Node;

    let mut reverse: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&source, targets) in adjacency {
        for &target in targets {
            reverse.entry(target).or_default().push(source);
        }
    }

    let mut state: HashMap<Node, OrderedFrontier> = ordered
        .iter()
        .copied()
        .map(|node| (node, OrderedFrontier::Unique(node)))
        .collect();
    let mut work: Vec<Node> = ordered.iter().copied().collect();
    while let Some(node) = work.pop() {
        let incoming = state[&node];
        let Some(predecessors) = reverse.get(&node) else {
            continue;
        };
        for &pred in predecessors {
            // An already ordered node is itself the first frontier regardless
            // of where its own successors go.
            if ordered.contains(&pred) {
                continue;
            }
            let joined = match (state.get(&pred).copied(), incoming) {
                (None, value) => value,
                (Some(OrderedFrontier::Ambiguous), _) | (_, OrderedFrontier::Ambiguous) => {
                    OrderedFrontier::Ambiguous
                }
                (Some(OrderedFrontier::Unique(left)), OrderedFrontier::Unique(right))
                    if left == right =>
                {
                    OrderedFrontier::Unique(left)
                }
                (Some(OrderedFrontier::Unique(_)), OrderedFrontier::Unique(_)) => {
                    OrderedFrontier::Ambiguous
                }
            };
            if state.get(&pred).copied() != Some(joined) {
                state.insert(pred, joined);
                work.push(pred);
            }
        }
    }
    state
}

fn remap_sseq_edges(
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
    member_to_head: &HashMap<crate::x86::types::Node, crate::x86::types::Node>,
) -> Vec<(crate::x86::types::Node, crate::x86::types::Node)> {
    edges
        .iter()
        .filter_map(|&(src, dst)| {
            let src = member_to_head.get(&src).copied().unwrap_or(src);
            let dst = member_to_head.get(&dst).copied().unwrap_or(dst);
            (src != dst).then_some((src, dst))
        })
        .collect()
}

/// RPO over statement-bearing nodes walking the FULL clight_succ edge set, with loop-structure-aware successor ordering that places a loop body contiguously ahead of its exit.
fn order_nodes_dfs(
    entry: crate::x86::types::Node,
    nodes: &HashSet<crate::x86::types::Node>,
    edges: &[(crate::x86::types::Node, crate::x86::types::Node)],
    is_exit: impl Fn(crate::x86::types::Node) -> bool,
    loop_members: &HashMap<crate::x86::types::Node, HashSet<crate::x86::types::Node>>,
    node_innermost_loop: &HashMap<crate::x86::types::Node, crate::x86::types::Node>,
    normalize: impl Fn(crate::x86::types::Node) -> crate::x86::types::Node,
) -> Vec<crate::x86::types::Node> {
    let mut adjacency: HashMap<crate::x86::types::Node, Vec<crate::x86::types::Node>> =
        HashMap::new();
    for (src, dst) in edges {
        if src != dst {
            adjacency.entry(*src).or_default().push(*dst);
        }
    }

    // Loop-structure-aware successor ordering, inverted because the DFS reverses twice: the body successor must be ordered LAST to emit first. Address ascending remains the tiebreak.
    for (src, succs) in adjacency.iter_mut() {
        let src_norm = normalize(*src);
        // Innermost natural loop containing src (smallest body, ties on header address); None degrades the comparator to pure address order, and it is precomputed for O(1) lookup.
        let inner_body: Option<&HashSet<crate::x86::types::Node>> = node_innermost_loop
            .get(&src_norm)
            .and_then(|header| loop_members.get(header));
        succs.sort_by(|a, b| {
            // 0 = leaves the innermost loop (exit, ordered first); 1 = stays inside it (body, ordered last). Both 0 (loop-free node) preserves the prior ascending-address order.
            let key = |n: &crate::x86::types::Node| -> u8 {
                match inner_body {
                    Some(body) if body.contains(&normalize(*n)) => 1,
                    _ => 0,
                }
            };
            key(a).cmp(&key(b)).then_with(|| a.cmp(b))
        });
        succs.dedup();
    }

    let mut visited = HashSet::new();
    let mut post_order = Vec::new();
    let mut stack = Vec::new();

    enum Action {
        Visit(crate::x86::types::Node),
        PostVisit(crate::x86::types::Node),
    }

    // Always start at the true entry so its successor chain orders every reachable member, even when the entry itself carries no statement.
    stack.push(Action::Visit(entry));

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
                if nodes.contains(&u) {
                    post_order.push(u);
                }
            }
        }
    }

    let mut result: Vec<_> = post_order.into_iter().rev().collect();

    // Disconnected members (edges lost to bundling or genuinely dead) are inserted BEFORE the trailing exit run, not after it -- placing them after would let the consumer's dead-statement trim silently drop them.
    let result_set: HashSet<_> = result.iter().copied().collect();
    let all_remaining: Vec<_> = nodes.difference(&result_set).copied().collect();
    // A disconnected node that is itself a LOOP HEADER is placed right after the reachable node edging into its body, or its Sloop floats to the wrong place and becomes unreachable.
    let mut targeted: Vec<(usize, crate::x86::types::Node)> = Vec::new();
    let mut general_remaining: Vec<crate::x86::types::Node> = Vec::new();
    for &r in &all_remaining {
        let rk = normalize(r);
        let anchor = loop_members
            .get(&rk)
            .and_then(|body| {
                result.iter().position(|&e| {
                    adjacency.get(&e).map_or(false, |succs| {
                        succs.iter().any(|s| body.contains(&normalize(*s)))
                    })
                })
            })
            .or_else(|| {
                // Threaded-entry fallback: anchor to the LAST result node whose forward edge-walk reaches a body member first, the loop's immediate preheader, so preheader init is not emitted after the loop.
                loop_members.get(&rk).and_then(|body| {
                    let result_set: HashSet<crate::x86::types::Node> =
                        result.iter().copied().collect();
                    result.iter().rposition(|&e| {
                        let mut stack: Vec<crate::x86::types::Node> =
                            adjacency.get(&e).map(|s| s.clone()).unwrap_or_default();
                        let mut seen: HashSet<crate::x86::types::Node> = HashSet::new();
                        while let Some(n) = stack.pop() {
                            if !seen.insert(n) {
                                continue;
                            }
                            if body.contains(&normalize(n)) {
                                return true;
                            }
                            // Stop at any other emitted node: control reached a different top-level statement first, so e is not the loop's entry edge.
                            if result_set.contains(&n) {
                                continue;
                            }
                            if let Some(succs) = adjacency.get(&n) {
                                stack.extend(succs.iter().copied());
                            }
                        }
                        false
                    })
                })
            });
        match anchor {
            Some(pos) => targeted.push((pos, r)),
            None => general_remaining.push(r),
        }
    }
    // Apply targeted insertions descending so earlier positions stay valid.
    targeted.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.cmp(&a.1)));
    for (pos, r) in targeted {
        result.insert(pos + 1, r);
    }
    if !general_remaining.is_empty() {
        let wanted: HashSet<_> = general_remaining.into_iter().collect();
        let mut blocked = visited;
        blocked.extend(result.iter().copied());
        let general_remaining = order_disconnected_cfg_nodes(&wanted, &adjacency, &blocked);

        // A disconnected component can still have an exact outgoing CFG path
        // into the entry component. Insert it immediately before that unique
        // frontier; appending all such nodes by address reverses decreasing-
        // address jumps such as a call followed by a shared epilogue.
        let result_set: HashSet<_> = result.iter().copied().collect();
        let result_positions: HashMap<_, _> = result
            .iter()
            .enumerate()
            .map(|(position, node)| (*node, position))
            .collect();
        let frontiers = ordered_cfg_frontiers(&adjacency, &result_set);
        let mut anchored: BTreeMap<usize, Vec<crate::x86::types::Node>> = BTreeMap::new();
        let mut unanchored = Vec::new();
        for node in general_remaining {
            match frontiers.get(&node).copied() {
                Some(OrderedFrontier::Unique(frontier))
                    if result_positions.contains_key(&frontier) =>
                {
                    anchored
                        .entry(result_positions[&frontier])
                        .or_default()
                        .push(node);
                }
                _ => unanchored.push(node),
            }
        }
        for (position, nodes) in anchored.into_iter().rev() {
            result.splice(position..position, nodes);
        }

        let mut insert_at = result.len();
        while insert_at > 0 && is_exit(result[insert_at - 1]) {
            insert_at -= 1;
        }
        result.splice(insert_at..insert_at, unanchored);
    }

    result
}

#[cfg(test)]
mod escaped_stack_array_tests {
    use super::*;

    #[test]
    fn physical_qword_carriers_remain_64_bit_on_every_data_model() {
        use crate::abi::DataModel;
        use crate::decompile::passes::c_pass::types::{IntSize,Signedness};
        for chunk in [MemoryChunk::MInt64,MemoryChunk::MAny64] {
            assert_eq!(ctype_from_memchunk(&chunk,DataModel::Lp64),CType::long());
            for model in [DataModel::Ilp32,DataModel::Llp64] {
                assert_eq!(ctype_from_memchunk(&chunk,model),CType::Int(IntSize::LongLong,Signedness::Signed));
            }
        }
    }
    use crate::decompile::passes::c_pass::types::FloatSize;

    #[test]
    fn aliased_stack_lvalue_uses_narrowest_physical_chunk() {
        let func: Address = 0x5000;
        let local: RTLReg = 0x8100;
        let mut db = DecompileDB::default();
        db.rel_push("stack_var", (func, 0x5010_u64, 7_i64, local));
        db.rel_push("stack_var_chunk", (func, 7_i64, MemoryChunk::MAny64));
        db.rel_push("pmov", (0x5010_u64, "byte_cell", "zero"));
        db.rel_push(
            "op_indirect",
            ("byte_cell", "", "RBP", "NONE", 1_i64, -1_i64, 1_usize),
        );

        let types = stack_local_physical_types(&db, func);
        assert_eq!(
            types.get(&crate::decompile::passes::c_pass::helpers::param_name_for_reg(local)),
            Some(&CType::char_unsigned()),
        );
    }

    #[test]
    fn framed_byte_buffer_owns_raw_negative_stack_cells() {
        let func: Address = 0x6000;
        let setup: Node = 0x6010;
        let base_site: Node = 0x6020;
        let byte0_site: Node = 0x6030;
        let byte1_site: Node = 0x6040;
        let base: RTLReg = 0x8100;
        let byte0: RTLReg = 0x8200;
        let byte1: RTLReg = 0x8300;
        let mut db = DecompileDB::default();
        db.rel_push("instr_in_function", (setup, func));
        db.rel_push("stack_base_move", (setup, "RSP", "RBP"));
        db.rel_push("func_stacksz", (func, 0x6100_u64, "framed", 48_u64));
        db.rel_push("stack_var", (func, base_site, 29_i64, base));
        db.rel_push("stack_var", (func, byte0_site, -19_i64, byte0));
        db.rel_push("stack_var", (func, byte1_site, -18_i64, byte1));
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(base, 3);

        let aliases = derive_stack_buffer_aliases(&db);
        let function_aliases = aliases.get(&func).expect("function aliases");
        assert_eq!(function_aliases.get(&byte0), Some(&(base, 0)));
        assert_eq!(function_aliases.get(&byte1), Some(&(base, 1)));
    }

    #[test]
    fn framed_buffer_layout_requires_exact_frame_and_bp_provenance() {
        let func: Address = 0x6200;
        let setup: Node = 0x6210;
        let access: Node = 0x6220;
        let base: RTLReg = 0x8400;
        let bp: RTLReg = 1;
        let mut db = DecompileDB::default();
        db.rel_push("instr_in_function", (setup, func));
        db.rel_push("instr_in_function", (access, func));
        db.rel_push("stack_base_move", (setup, "RSP", "RBP"));
        db.rel_push("func_stacksz", (func, setup, "framed", 48_u64));
        db.rel_push("stack_var", (func, access, 29_i64, base));
        db.rel_push("reg_rtl", (func, Mreg::BP, bp));
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(base, 3);

        let layouts = derive_raw_frame_buffer_layouts(&db);

        assert_eq!(
            layouts.base_pointer_names.get(&func),
            Some(&HashSet::from([
                crate::decompile::passes::c_pass::helpers::param_name_for_reg(bp),
            ])),
        );
        assert_eq!(
            layouts.regions.get(&func),
            Some(&vec![RawFrameBufferRegion {
                start: -19,
                end: -16,
                backing: crate::decompile::passes::c_pass::helpers::param_name_for_reg(base),
            }]),
        );
    }

    #[test]
    fn raw_bp_interior_address_rewrites_only_inside_one_proven_buffer() {
        let frame = "frame".to_string();
        let regions = vec![RawFrameBufferRegion {
            start: -208,
            end: -57,
            backing: "buffer".to_string(),
        }];
        let raw_address = CExpr::Binary(
            BinaryOp::Add,
            Box::new(CExpr::Cast(
                CType::ptr(CType::char_signed()),
                Box::new(CExpr::Var(frame.clone())),
            )),
            Box::new(CExpr::int(-200)),
        );
        let body = CStmt::Expr(raw_address.clone());

        assert_eq!(
            rewrite_raw_frame_buffer_addresses(&body, &HashSet::from([frame.clone()]), &regions),
            CStmt::Expr(CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(stack_buffer_alias_byte_expr("buffer", 8)),
            )),
        );

        let outside = CStmt::Expr(CExpr::Binary(
            BinaryOp::Add,
            Box::new(CExpr::Var(frame)),
            Box::new(CExpr::int(-56)),
        ));
        assert_eq!(
            rewrite_raw_frame_buffer_addresses(
                &outside,
                &HashSet::from(["frame".to_string()]),
                &regions,
            ),
            outside,
        );
        assert_eq!(
            rewrite_raw_frame_buffer_addresses(
                &body,
                &HashSet::from(["other_base".to_string()]),
                &regions,
            ),
            body,
        );
    }

    #[test]
    fn exact_qword_store_keeps_its_width_inside_a_byte_backing_buffer() {
        let func: Address = 0x6300;
        let node: Node = 0x6310;
        let base_node: Node = 0x6308;
        let backing: RTLReg = 0x8500;
        let destination: RTLReg = 0x8510;
        let source: RTLReg = 0x8520;
        let interior_node: Node = 0x6320;
        let interior_destination: RTLReg = 0x8530;
        let interior_source: RTLReg = 0x8540;
        let mut db = DecompileDB::default();
        db.rel_push(
            "rtl_inst",
            (
                node,
                RTLInst::Iop(Operation::Omove, Arc::new(vec![source]), destination),
            ),
        );
        db.rel_push("stack_var", (func, base_node, 48_i64, backing));
        db.rel_push("stack_var", (func, node, 96_i64, destination));
        db.rel_push(
            "mach_inst",
            (node, MachInst::Msetstack(Mreg::AX, 96, Typ::Tany64)),
        );
        db.rel_push(
            "rtl_inst",
            (
                interior_node,
                RTLInst::Iop(
                    Operation::Omove,
                    Arc::new(vec![interior_source]),
                    interior_destination,
                ),
            ),
        );
        db.rel_push(
            "stack_var",
            (func, interior_node, 52_i64, interior_destination),
        );
        db.rel_push(
            "mach_inst",
            (
                interior_node,
                MachInst::Msetstack(Mreg::X0, 52, Typ::Tany64),
            ),
        );
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(backing, 96);
        let aliases = HashMap::from([(func, HashMap::from([(backing, (backing, 0_usize))]))]);
        let mut escaped_buffers = EscapedStackBufferLayouts::default();
        escaped_buffers
            .buffers
            .entry(func)
            .or_default()
            .insert(backing, 96);
        escaped_buffers
            .members
            .entry(func)
            .or_default()
            .insert(destination, (backing, 48_usize, MemoryChunk::MInt8Unsigned));

        let stores = derive_exact_stack_buffer_stores(&db, &aliases, &escaped_buffers);
        assert_eq!(
            stores
                .get(&func)
                .and_then(|items| items.get(&(destination, source))),
            Some(&(backing, 48, MemoryChunk::MInt64)),
        );
        assert_eq!(
            stores
                .get(&func)
                .and_then(|items| { items.get(&(interior_destination, interior_source)) }),
            Some(&(backing, 4, MemoryChunk::MInt64)),
        );

        let backing_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(backing);
        let mut types = HashMap::from([(backing_name.clone(), CType::int())]);
        apply_stack_struct_buffer_types(&db, func, &mut types);
        assert_eq!(
            types.get(&backing_name),
            Some(&CType::Array(Box::new(CType::char_unsigned()), Some(96),)),
        );

        let destination_name =
            crate::decompile::passes::c_pass::helpers::param_name_for_reg(destination);
        let source_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(source);
        let body = CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var(destination_name)),
            Box::new(CExpr::Var(source_name.clone())),
        ));
        assert_eq!(
            rewrite_exact_stack_buffer_stores(&body, &stores[&func], db.data_model()),
            CStmt::Expr(CExpr::Assign(
                AssignOp::Assign,
                Box::new(stack_buffer_alias_value_expr(
                    &backing_name,
                    48,
                    &CType::long(),
                )),
                Box::new(CExpr::Var(source_name)),
            )),
        );
    }

    #[test]
    fn aliased_register_self_address_does_not_write_backing_bytes() {
        let base: RTLReg = 0x7000;
        let member: RTLReg = 0x7100;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let member_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(member);
        let pointer_ty = CType::ptr(CType::char_unsigned());
        let body = CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var(member_name.clone())),
            Box::new(CExpr::Cast(
                pointer_ty.clone(),
                Box::new(CExpr::Unary(
                    UnaryOp::AddrOf,
                    Box::new(CExpr::Var(base_name)),
                )),
            )),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(member, (base, 0_usize))]),
            &HashMap::from([(member_name, pointer_ty)]),
            &HashSet::new(),
        );

        assert_eq!(rewritten, CStmt::Expr(CExpr::int(0)));
    }

    #[test]
    fn stack_address_alias_uses_the_backing_address_not_stored_bytes() {
        let base: RTLReg = 0x7200;
        let address: RTLReg = 0x7300;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let address_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(address);
        let body = CStmt::Expr(CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(address_name.clone())),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(address, (base, 8_usize))]),
            &HashMap::from([(address_name, CType::ptr(CType::char_unsigned()))]),
            &HashSet::from([address]),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(stack_buffer_alias_byte_expr(&base_name, 8)),
            )),
        );
    }

    #[test]
    fn stack_buffer_alias_rewrites_address_to_exact_backing_offset() {
        let base: RTLReg = 0x7100;
        let member: RTLReg = 0x7200;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let member_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(member);
        let body = CStmt::Expr(CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(member_name.clone())),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(member, (base, 1_usize))]),
            &HashMap::from([(member_name, CType::long())]),
            &HashSet::new(),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(CExpr::Unary(
                    UnaryOp::Deref,
                    Box::new(CExpr::Cast(
                        CType::ptr(CType::long()),
                        Box::new(CExpr::Unary(
                            UnaryOp::AddrOf,
                            Box::new(stack_buffer_alias_byte_expr(&base_name, 1)),
                        )),
                    )),
                )),
            )),
        );
    }

    #[test]
    fn stack_buffer_backing_keeps_offset_zero_scalar_width() {
        let base: RTLReg = 0x7300;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let body = CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var(base_name.clone())),
            Box::new(CExpr::int(-1)),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(base, (base, 0_usize))]),
            &HashMap::from([(base_name, CType::long())]),
            &HashSet::new(),
        );

        let CStmt::Expr(CExpr::Assign(_, lhs, _)) = rewritten else {
            panic!("stack-buffer scalar assignment shape changed")
        };
        assert_eq!(
            *lhs,
            CExpr::Unary(
                UnaryOp::Deref,
                Box::new(CExpr::Cast(
                    CType::ptr(CType::long()),
                    Box::new(CExpr::Unary(
                        UnaryOp::AddrOf,
                        Box::new(stack_buffer_alias_byte_expr(
                            &crate::decompile::passes::c_pass::helpers::param_name_for_reg(base),
                            0,
                        )),
                    )),
                )),
            )
        );
    }

    #[test]
    fn array_backing_under_pointer_cast_uses_its_address_not_first_byte_value() {
        let base: RTLReg = 0x7400;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let target_ty = CType::ptr(CType::long());
        let body = CStmt::Expr(CExpr::Cast(
            target_ty.clone(),
            Box::new(CExpr::Var(base_name.clone())),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(base, (base, 0_usize))]),
            &HashMap::from([(
                base_name.clone(),
                CType::Array(Box::new(CType::char_unsigned()), Some(24)),
            )]),
            &HashSet::new(),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Cast(
                target_ty,
                Box::new(CExpr::Unary(
                    UnaryOp::AddrOf,
                    Box::new(stack_buffer_alias_byte_expr(&base_name, 0)),
                )),
            )),
            "an array alias in pointer context must decay to its backing address",
        );
    }

    #[test]
    fn byte_array_backing_direct_value_keeps_its_physical_access_width() {
        let base: RTLReg = 0x7480;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let body = CStmt::Expr(CExpr::Var(base_name.clone()));
        let array_ty = CType::Array(Box::new(CType::char_unsigned()), Some(8));

        let rewritten = rewrite_stack_buffer_aliases_with_access_types(
            &body,
            &HashMap::from([(base, (base, 0_usize))]),
            &HashMap::from([(base_name.clone(), array_ty)]),
            &HashSet::new(),
            &HashMap::from([(base, CType::int())]),
            &HashSet::from([base]),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(stack_buffer_alias_value_expr(&base_name, 0, &CType::int())),
            "the backing array owns eight bytes, but a direct movl reload reads four",
        );
    }

    #[test]
    fn absorbed_buffer_root_keeps_address_semantics_after_its_declaration_is_removed() {
        let (member, base) = (0x7001, 0x7002);
        let member_name = param_name_for_reg(member);
        let base_name = param_name_for_reg(base);
        let pointer = CType::ptr(CType::char_unsigned());
        let body = CStmt::Expr(CExpr::Cast(
            pointer.clone(),
            Box::new(CExpr::var(&member_name)),
        ));
        let rewritten = rewrite_stack_buffer_aliases_with_access_types(
            &body,
            &HashMap::from([(member, (base, 16))]),
            &HashMap::from([(member_name, CType::long())]),
            &HashSet::new(),
            &HashMap::new(),
            &HashSet::from([member]),
        );
        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Cast(
                pointer,
                Box::new(CExpr::Unary(
                    UnaryOp::AddrOf,
                    Box::new(stack_buffer_alias_byte_expr(&base_name, 16))
                ))
            ))
        );
    }

    #[test]
    fn scalar_backing_under_pointer_cast_keeps_scalar_value_semantics() {
        let base: RTLReg = 0x7500;
        let member: RTLReg = 0x7600;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let member_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(member);
        let target_ty = CType::ptr(CType::char_unsigned());
        let body = CStmt::Expr(CExpr::Cast(
            target_ty.clone(),
            Box::new(CExpr::Var(member_name.clone())),
        ));

        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(member, (base, 8_usize))]),
            &HashMap::from([(member_name, CType::long())]),
            &HashSet::new(),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Cast(
                target_ty,
                Box::new(CExpr::Unary(
                    UnaryOp::Deref,
                    Box::new(CExpr::Cast(
                        CType::ptr(CType::long()),
                        Box::new(CExpr::Unary(
                            UnaryOp::AddrOf,
                            Box::new(stack_buffer_alias_byte_expr(&base_name, 8)),
                        )),
                    )),
                )),
            )),
            "a true scalar-to-pointer cast must still convert the stored value",
        );
    }

    #[test]
    fn named_global_byte_pointer_on_rhs_keeps_byte_stride() {
        let global = 0x4000_usize;
        let index = 0x5000_usize;
        let int_ty = clight::ClightType::Tint(
            clight::ClightIntSize::I32,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        );
        let void_ptr = clight::ClightType::Tpointer(
            Arc::new(clight::ClightType::Tvoid),
            clight::ClightAttr::default(),
        );
        let address = clight::ClightExpr::Ebinop(
            clight::ClightBinaryOp::Oadd,
            Box::new(clight::ClightExpr::Etempvar(index, int_ty.clone())),
            Box::new(clight::ClightExpr::Eaddrof(
                Box::new(clight::ClightExpr::Evar(global, int_ty)),
                void_ptr.clone(),
            )),
            void_ptr,
        );
        let mut ctx = ConversionContext::new(
            HashMap::from([(global, "global_bytes".to_string())]),
            crate::abi::DataModel::Lp64,
        );
        ctx.global_lvalue_aliases.insert(
            global,
            CExpr::Index(
                Box::new(CExpr::Var("global_bytes".to_string())),
                Box::new(CExpr::int(0)),
            ),
        );

        let converted = convert_expr(&address, &mut ctx);
        let CExpr::Cast(CType::Pointer(result, _), sum) = converted else {
            panic!("byte-address result must retain its annotated pointer cast")
        };
        assert!(matches!(result.as_ref(), CType::Void));
        let CExpr::Paren(sum) = sum.as_ref() else {
            panic!("result cast must parenthesize the byte addition")
        };
        let CExpr::Binary(BinaryOp::Add, base, _) = sum.as_ref() else {
            panic!("expected symmetric byte addition")
        };
        assert!(matches!(
            base.as_ref(),
            CExpr::Cast(CType::Pointer(pointee, _), _)
                if matches!(pointee.as_ref(), CType::Int(IntSize::Char, _))
        ));
    }

    #[test]
    fn stack_alias_pointer_arithmetic_keeps_clight_access_stride() {
        let base: RTLReg = 0x7700;
        let member: RTLReg = 0x7800;
        let index: RTLReg = 0x7900;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let member_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(member);
        let index_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(index);
        let int_ty = clight::ClightType::Tint(
            clight::ClightIntSize::I32,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        );
        let int_ptr_ty =
            clight::ClightType::Tpointer(Arc::new(int_ty.clone()), clight::ClightAttr::default());
        let indexed_address = clight::ClightExpr::Ebinop(
            clight::ClightBinaryOp::Oadd,
            Box::new(clight::ClightExpr::Eaddrof(
                Box::new(clight::ClightExpr::Evar(member as Ident, int_ty.clone())),
                int_ptr_ty.clone(),
            )),
            Box::new(clight::ClightExpr::Etempvar(index as Ident, int_ty)),
            int_ptr_ty,
        );
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        let body = CStmt::Expr(convert_expr(&indexed_address, &mut ctx));

        // The final storage declaration can be wider than the particular
        // indexed access.  That must not change the pointer-add stride.
        let rewritten = rewrite_stack_buffer_aliases(
            &body,
            &HashMap::from([(member, (base, 0_usize))]),
            &HashMap::from([(member_name, CType::long())]),
            &HashSet::new(),
        );
        let final_types = HashMap::from([
            (
                base_name,
                CType::Array(Box::new(CType::char_unsigned()), Some(16)),
            ),
            (index_name, CType::int()),
        ]);
        let rewritten = strip_trivial_casts(&rewritten, &final_types);
        let rewritten = repair_arith_stmt(&rewritten, &final_types);

        let CStmt::Expr(CExpr::Binary(BinaryOp::Add, lhs, _)) = rewritten else {
            panic!("indexed stack address lost its additive shape: {rewritten:?}")
        };
        assert!(
            matches!(
                lhs.as_ref(),
                CExpr::Cast(CType::Pointer(pointee, _), _)
                    if pointee.as_ref() == &CType::int()
            ),
            "late storage coalescing changed an int-pointer stride: {lhs:?}",
        );
    }

    #[test]
    fn explicit_typed_pointer_after_byte_rebase_keeps_element_stride() {
        let int_ptr = CType::ptr(CType::int());
        let byte_address = CExpr::Cast(
            int_ptr.clone(),
            Box::new(CExpr::Paren(Box::new(CExpr::Binary(
                BinaryOp::Add,
                Box::new(CExpr::Cast(
                    CType::ptr(CType::char_signed()),
                    Box::new(CExpr::var("base")),
                )),
                Box::new(CExpr::var("byte_offset")),
            )))),
        );
        let expression = CExpr::Binary(
            BinaryOp::Add,
            Box::new(byte_address.clone()),
            Box::new(CExpr::int(1)),
        );
        let types = HashMap::from([
            ("base".to_string(), int_ptr.clone()),
            ("byte_offset".to_string(), CType::long()),
        ]);

        let ordinary = repair_arith_expr(&expression, &types);
        assert!(matches!(ordinary, CExpr::Cast(ty, _) if ty == int_ptr));

        let repaired = repair_arith_expr_context(&expression, &types, true);
        assert!(matches!(
            repaired,
            CExpr::Binary(BinaryOp::Add, lhs, rhs)
                if lhs.as_ref() == &byte_address && rhs.as_ref() == &CExpr::int(1)
        ));

        let store = memcpy_store_expr(CType::int(), expression, CExpr::int(7));
        let repaired_store = repair_arith_expr(&store, &types);
        assert!(matches!(
            repaired_store,
            CExpr::Call(_, args)
                if matches!(
                    args.first(),
                    Some(CExpr::Cast(CType::Pointer(pointee, _), address))
                        if pointee.as_ref() == &CType::Void
                            && matches!(
                                address.as_ref(),
                                CExpr::Binary(BinaryOp::Add, lhs, rhs)
                                    if lhs.as_ref() == &byte_address
                                        && rhs.as_ref() == &CExpr::int(1)
                            )
                )
        ));
    }

    #[test]
    fn exact_interior_global_field_keeps_one_owner_and_relocation_initializer() {
        use crate::decompile::passes::c_pass::types::{Designator, Initializer};

        let owner_id = 0xe090_usize;
        let member_id = owner_id + 8;
        let target_id = 0xe120_usize;
        let mut bytes = vec![0_u8; 16];
        bytes[..8].copy_from_slice(&256_u64.to_le_bytes());
        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        db.rel_push(
            "retained_initialized_data_range",
            (owner_id as Address, Arc::new(bytes)),
        );
        db.rel_push("symbol_size", (member_id as Address, 8_usize, "L_e098"));

        let target_expr = CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(format!("L_{target_id:x}"))),
        );
        let owner_ref_id = owner_id - 16;
        let owner_ref_expr = CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(format!("L_{owner_id:x}"))),
        );
        let globals = vec![
            GlobalData {
                id: owner_ref_id,
                name: format!("L_{owner_ref_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: true,
                scalar_value: None,
                scalar_writable: true,
                pointer_init: vec![owner_ref_expr],
                aggregate_relocation_init: BTreeMap::new(),
            },
            GlobalData {
                id: owner_id,
                name: format!("L_{owner_id:x}"),
                is_string: false,
                content: Vec::new(),
                // Deliberately pointer-shaped evidence: accepted aggregate
                // ownership must override a scalar pointer declaration.
                is_pointer: true,
                scalar_value: None,
                scalar_writable: true,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::new(),
            },
            GlobalData {
                id: member_id,
                name: format!("L_{member_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: true,
                scalar_value: None,
                scalar_writable: true,
                pointer_init: vec![target_expr.clone()],
                aggregate_relocation_init: BTreeMap::new(),
            },
            GlobalData {
                id: target_id,
                name: format!("L_{target_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: false,
                scalar_value: None,
                scalar_writable: true,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::new(),
            },
        ];
        let layouts = HashMap::from([(
            owner_id,
            (
                0x5937_usize,
                vec![
                    (0_i64, 0_usize, MemoryChunk::MAny64),
                    (8_i64, 8_usize, MemoryChunk::MAny64),
                ],
            ),
        )]);

        let coalesced = derive_global_aggregate_coalescing(&db, &globals, &layouts);

        assert!(coalesced.owner_ids.contains(&owner_id));
        assert!(coalesced.member_ids.contains(&member_id));
        let ordered_ids: Vec<_> = order_globals_for_aggregate_initializers(&globals, &coalesced)
            .into_iter()
            .map(|global| global.id)
            .collect();
        assert_eq!(ordered_ids, vec![target_id, owner_id, owner_ref_id]);
        assert_eq!(
            coalesced.member_exprs.get(&format!("L_{member_id:x}")),
            Some(&CExpr::Member(
                Box::new(CExpr::Var(format!("L_{owner_id:x}"))),
                "ofs_8".to_string(),
            )),
        );
        let Some(Initializer::List(items)) = coalesced.owner_initializers.get(&owner_id) else {
            panic!("aggregate owner lost its initialized fields")
        };
        assert!(items.iter().any(|item| {
            item.designator == Some(Designator::Field("ofs_0".to_string()))
                && item.init
                    == Initializer::Expr(CExpr::IntLit(IntLiteral {
                        value: 256,
                        suffix: IntLiteralSuffix::L,
                        base: IntLiteralBase::Decimal,
                    }))
        }));
        assert!(items.iter().any(|item| {
            item.designator == Some(Designator::Field("ofs_8".to_string()))
                && item.init
                    == Initializer::Expr(CExpr::Cast(CType::long(), Box::new(target_expr.clone())))
        }));

        let address_use = CStmt::Expr(CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(format!("L_{member_id:x}"))),
        ));
        let rewritten =
            crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&address_use, &|expr| {
                let CExpr::Var(name) = expr else {
                    return None;
                };
                coalesced.member_exprs.get(name).cloned()
            });
        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(CExpr::Member(
                    Box::new(CExpr::Var(format!("L_{owner_id:x}"))),
                    "ofs_8".to_string(),
                )),
            )),
        );
    }

    #[test]
    fn aggregate_owner_carries_relocation_without_a_synthetic_member_global() {
        use crate::decompile::passes::c_pass::types::{Designator, Initializer};

        let owner_id = 0xe090_usize;
        let target_id = 0xe120_usize;
        let target_expr = CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(format!("L_{target_id:x}"))),
        );
        let mut bytes = vec![0_u8; 16];
        bytes[..8].copy_from_slice(&256_u64.to_le_bytes());
        bytes[8..].copy_from_slice(&(target_id as u64).to_le_bytes());

        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        db.rel_push(
            "retained_initialized_data_range",
            (owner_id as Address, Arc::new(bytes)),
        );
        db.rel_push(
            "pointer_in_data",
            ((owner_id + 8) as Address, target_id as Address),
        );

        let globals = vec![
            GlobalData {
                id: owner_id,
                name: format!("L_{owner_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: false,
                scalar_value: None,
                scalar_writable: false,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::from([(8, target_expr.clone())]),
            },
            GlobalData {
                id: target_id,
                name: format!("L_{target_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: false,
                scalar_value: None,
                scalar_writable: true,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::new(),
            },
        ];
        let layouts = HashMap::from([(
            owner_id,
            (
                0x5937_usize,
                vec![
                    (0_i64, 0_usize, MemoryChunk::MAny64),
                    (8_i64, 8_usize, MemoryChunk::MAny64),
                ],
            ),
        )]);

        let coalesced = derive_global_aggregate_coalescing(&db, &globals, &layouts);

        assert!(coalesced.owner_ids.contains(&owner_id));
        assert!(coalesced.member_ids.is_empty());
        assert_eq!(
            order_globals_for_aggregate_initializers(&globals, &coalesced)
                .into_iter()
                .map(|global| global.id)
                .collect::<Vec<_>>(),
            vec![target_id, owner_id]
        );
        let Some(Initializer::List(items)) = coalesced.owner_initializers.get(&owner_id) else {
            panic!("aggregate owner lost its relocation initializer")
        };
        assert!(items.iter().any(|item| {
            item.designator == Some(Designator::Field("ofs_8".to_string()))
                && item.init
                    == Initializer::Expr(CExpr::Cast(CType::long(), Box::new(target_expr.clone())))
        }));
    }

    #[test]
    fn initialized_aggregate_owner_needs_no_synthetic_member_global() {
        use crate::decompile::passes::c_pass::types::{Designator, Initializer};

        let owner_id = 0xe200_usize;
        let low = (11_u64 << 32) | 7;
        let high = (17_u64 << 32) | 13;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&low.to_le_bytes());
        bytes.extend_from_slice(&high.to_le_bytes());

        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        db.rel_push(
            "retained_initialized_data_range",
            (owner_id as Address, Arc::new(bytes)),
        );

        let globals = vec![GlobalData {
            id: owner_id,
            name: format!("L_{owner_id:x}"),
            is_string: false,
            content: Vec::new(),
            is_pointer: false,
            scalar_value: None,
            scalar_writable: false,
            pointer_init: Vec::new(),
            aggregate_relocation_init: BTreeMap::new(),
        }];
        let layouts = HashMap::from([(
            owner_id,
            (
                0x5938_usize,
                vec![
                    (0_i64, 0_usize, MemoryChunk::MAny64),
                    (8_i64, 8_usize, MemoryChunk::MAny64),
                ],
            ),
        )]);

        let ownership = derive_global_aggregate_coalescing(&db, &globals, &layouts);

        assert!(ownership.owner_ids.contains(&owner_id));
        assert!(ownership.member_ids.is_empty());
        let Some(Initializer::List(items)) = ownership.owner_initializers.get(&owner_id) else {
            panic!("direct aggregate owner lost its initialized image")
        };
        for (field, value) in [("ofs_0", low as i128), ("ofs_8", high as i128)] {
            assert!(items.iter().any(|item| {
                item.designator == Some(Designator::Field(field.to_string()))
                    && item.init
                        == Initializer::Expr(CExpr::IntLit(IntLiteral {
                            value,
                            suffix: IntLiteralSuffix::L,
                            base: IntLiteralBase::Decimal,
                        }))
            }));
        }
    }

    #[test]
    fn relocation_without_a_relocatable_owner_field_rejects_the_whole_image() {
        let owner_id = 0xe090_usize;
        let member_id = owner_id + 8;
        let target_id = 0xe120_usize;
        let mut bytes = vec![0_u8; 16];
        bytes[8..].copy_from_slice(&(target_id as u64).to_le_bytes());

        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        db.rel_push(
            "retained_initialized_data_range",
            (owner_id as Address, Arc::new(bytes)),
        );
        db.rel_push(
            "pointer_in_data",
            (member_id as Address, target_id as Address),
        );
        let globals = vec![
            GlobalData {
                id: owner_id,
                name: format!("L_{owner_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: false,
                scalar_value: None,
                scalar_writable: false,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::new(),
            },
            GlobalData {
                id: member_id,
                name: format!("L_{member_id:x}"),
                is_string: false,
                content: Vec::new(),
                is_pointer: false,
                scalar_value: None,
                scalar_writable: false,
                pointer_init: Vec::new(),
                aggregate_relocation_init: BTreeMap::new(),
            },
        ];
        let layouts = HashMap::from([(
            owner_id,
            (
                0x5937_usize,
                vec![
                    (0_i64, 0_usize, MemoryChunk::MAny64),
                    (8_i64, 8_usize, MemoryChunk::MAny64),
                ],
            ),
        )]);

        let coalesced = derive_global_aggregate_coalescing(&db, &globals, &layouts);
        assert!(!coalesced.owner_ids.contains(&owner_id));
        assert!(coalesced.owner_initializers.get(&owner_id).is_none());
    }

    #[test]
    fn aggregate_global_nonzero_offset_emits_char_pointer_arithmetic() {
        let ident = 0xe090_usize;
        let lowered = crate::decompile::passes::clight_pass::clight_expr_from_csharp(
            &CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, 8)),
            8,
        );
        let mut ctx = ConversionContext::new(
            HashMap::from([(ident, "L_e090".to_string())]),
            crate::abi::DataModel::Lp64,
        );
        // Conversion is intentionally independent of the final declaration:
        // even when L_e090 is emitted as a recovered struct, its machine
        // coordinate must retain the eight-byte displacement.
        let converted = convert_expr(&lowered, &mut ctx);
        let byte_expr = match &converted {
            CExpr::Cast(CType::Pointer(pointee, _), inner)
                if matches!(pointee.as_ref(), CType::Void) =>
            {
                match inner.as_ref() {
                    CExpr::Paren(inner) => inner.as_ref(),
                    inner => inner,
                }
            }
            other => other,
        };

        assert!(matches!(
            byte_expr,
            CExpr::Binary(
                BinaryOp::Add,
                lhs,
                rhs,
            ) if matches!(
                lhs.as_ref(),
                CExpr::Cast(CType::Pointer(pointee, _), inner)
                    if matches!(pointee.as_ref(), CType::Int(IntSize::Char, _))
                        && matches!(inner.as_ref(), CExpr::Unary(UnaryOp::AddrOf, _))
            ) && matches!(rhs.as_ref(), CExpr::IntLit(literal) if literal.value == 8)
        ));
    }

    #[test]
    fn interior_global_alias_keeps_owner_lvalue_and_access_signedness() {
        let interior_id = 0xe131_usize;
        let alias = CExpr::Index(
            Box::new(CExpr::Var("global_bytes".to_string())),
            Box::new(CExpr::int(1)),
        );
        let access_ty = clight::ClightType::Tint(
            clight::ClightIntSize::I8,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        );
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        ctx.global_lvalue_aliases.insert(interior_id, alias.clone());

        let converted = convert_expr(
            &clight::ClightExpr::Evar(interior_id, access_ty.clone()),
            &mut ctx,
        );
        let typed_alias = CExpr::Unary(
            UnaryOp::Deref,
            Box::new(CExpr::Cast(
                CType::ptr(CType::Int(IntSize::Char, Signedness::Signed)),
                Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(alias))),
            )),
        );
        assert_eq!(converted, typed_alias);

        let address = convert_expr(
            &clight::ClightExpr::Eaddrof(
                Box::new(clight::ClightExpr::Evar(interior_id, access_ty)),
                clight::ClightType::Tpointer(
                    Arc::new(clight::ClightType::Tint(
                        clight::ClightIntSize::I8,
                        clight::ClightSignedness::Signed,
                        clight::ClightAttr::default(),
                    )),
                    clight::ClightAttr::default(),
                ),
            ),
            &mut ctx,
        );
        assert_eq!(
            address,
            CExpr::Unary(UnaryOp::AddrOf, Box::new(typed_alias))
        );
    }

    #[test]
    fn aggregate_base_alias_keeps_scalar_access_type() {
        let owner_id = 0x26640_usize;
        let alias = CExpr::Member(
            Box::new(CExpr::Var("L_26640".to_string())),
            "ofs_0".to_string(),
        );
        let access_ty =
            clight::ClightType::Tfloat(clight::ClightFloatSize::F32, clight::ClightAttr::default());
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        ctx.global_lvalue_aliases.insert(owner_id, alias.clone());

        assert_eq!(
            convert_expr(&clight::ClightExpr::Evar(owner_id, access_ty), &mut ctx),
            CExpr::Unary(
                UnaryOp::Deref,
                Box::new(CExpr::Cast(
                    CType::ptr(CType::Float(FloatSize::Float)),
                    Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(alias))),
                )),
            ),
            "an overlapping aggregate field type must not replace the scalar machine-access type",
        );
    }

    #[test]
    fn physical_global_extent_bounds_incompatible_logical_stride() {
        let owner = 0x404030_usize;
        let mut db = DecompileDB::default();
        db.rel_push("is_global_array", (owner, 6_usize, 3_usize));
        db.rel_push("global_storage_extent", (owner, 16_usize));

        assert_eq!(
            recovered_global_array_declarations(&db).get(&owner),
            Some(&(1, 16)),
            "an 18-byte interpretation must not enlarge a 16-byte ELF object",
        );

        let typed_owner = owner + 0x20;
        db.rel_push("is_global_array", (typed_owner, 4_usize, 4_usize));
        db.rel_push("global_storage_extent", (typed_owner, 16_usize));
        assert_eq!(
            recovered_global_array_declarations(&db).get(&typed_owner),
            Some(&(4, 4)),
            "an exact logical layout should retain its element type",
        );
    }

    #[test]
    fn equal_width_global_layouts_keep_the_largest_represented_count() {
        let owner = 0x404080_usize;
        let mut db = DecompileDB::default();
        db.rel_push("is_global_array", (owner, 8_usize, 2_usize));
        db.rel_push("is_global_array", (owner, 8_usize, 2064_usize));

        assert_eq!(
            recovered_global_array_declarations(&db).get(&owner),
            Some(&(8, 2064)),
            "a short relocation prefix must not truncate a larger same-width indexed layout",
        );

        db.rel_push("global_storage_extent", (owner, 16_usize));
        assert_eq!(
            recovered_global_array_declarations(&db).get(&owner),
            Some(&(1, 16)),
            "an exact physical extent must still override a larger logical interpretation",
        );
    }

    #[test]
    fn stack_one_past_address_uses_the_array_owners_byte_coordinate() {
        let base: RTLReg = 0x7700;
        let endpoint: RTLReg = 0x7800;
        let base_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(base);
        let endpoint_name = crate::decompile::passes::c_pass::helpers::param_name_for_reg(endpoint);
        let body = CStmt::Expr(CExpr::Unary(
            UnaryOp::AddrOf,
            Box::new(CExpr::Var(endpoint_name)),
        ));

        let rewritten = rewrite_stack_buffer_end_aliases(
            &body,
            &HashMap::from([(endpoint, (base, 8192_usize))]),
        );

        assert_eq!(
            rewritten,
            CStmt::Expr(CExpr::Binary(
                BinaryOp::Add,
                Box::new(CExpr::Cast(
                    CType::ptr(CType::char_unsigned()),
                    Box::new(CExpr::Var(base_name)),
                )),
                Box::new(CExpr::int(8192)),
            )),
        );
    }

    #[test]
    fn exact_uniform_escaped_region_coalesces_canonical_stack_locals() {
        let mut db = DecompileDB::default();
        let func: Address = 0x9000;
        let base_ofs: i64 = 32;
        let locals: [RTLReg; 3] = [0x7100, 0x7200, 0x7300];
        let late_base_address: RTLReg = 0x7400;

        for (idx, local) in locals.into_iter().enumerate() {
            let field_ofs = idx as i64 * 8;
            db.rel_push(
                "escaped_stack_region_field",
                (func, base_ofs, field_ofs, MemoryChunk::MAny64),
            );
            db.rel_push(
                "stack_var",
                (func, 0x100 + idx as u64, base_ofs + field_ofs, local),
            );
        }
        // A later LEA/reload of element zero gets a distinct SSA name but
        // still denotes the same physical array base.
        db.rel_push("stack_var", (func, 0x180_u64, base_ofs, late_base_address));

        // A sparse region is struct-like and must remain separate locals.
        let sparse_func: Address = 0xa000;
        for (idx, field_ofs) in [0_i64, 16].into_iter().enumerate() {
            db.rel_push(
                "escaped_stack_region_field",
                (sparse_func, -32_i64, field_ofs, MemoryChunk::MAny64),
            );
            db.rel_push(
                "stack_var",
                (
                    sparse_func,
                    0x200 + idx as u64,
                    -32 + field_ofs,
                    0x8100 + idx as u64,
                ),
            );
        }

        let layouts = derive_escaped_stack_array_layouts(&db);
        assert_eq!(
            layouts.arrays.get(&func).and_then(|m| m.get(&locals[0])),
            Some(&(MemoryChunk::MAny64, 3))
        );
        assert_eq!(
            layouts.members.get(&func),
            Some(&HashMap::from([
                (locals[0], (locals[0], 0)),
                (late_base_address, (locals[0], 0)),
                (locals[1], (locals[0], 1)),
                (locals[2], (locals[0], 2)),
            ]))
        );
        assert!(!layouts.arrays.contains_key(&sparse_func));
        assert!(!layouts.members.contains_key(&sparse_func));
    }

    #[test]
    fn exact_mixed_escaped_region_coalesces_into_byte_buffer() {
        let mut db = DecompileDB::default();
        let func: Address = 0xb000;
        let base_ofs: i64 = 16;
        let fields = [
            (0_i64, MemoryChunk::MInt32, 0x7100_u64),
            (4_i64, MemoryChunk::MInt32, 0x7200_u64),
            (8_i64, MemoryChunk::MInt8Unsigned, 0x7300_u64),
            (16_i64, MemoryChunk::MAny64, 0x7400_u64),
            (25_i64, MemoryChunk::MInt8Unsigned, 0x7500_u64),
        ];
        let updated_field4: RTLReg = 0x7600;
        db.rel_push("slot_escaped_canonical", (func, base_ofs, fields[0].2));
        for (field_ofs, chunk, local) in fields {
            db.rel_push(
                "escaped_stack_region_field",
                (func, base_ofs, field_ofs, chunk),
            );
            db.rel_push(
                "slot_escaped_region_canonical",
                (func, base_ofs + field_ofs, local),
            );
        }
        // A callee-only field still extends the object even when the caller
        // has no scalar SSA local at that byte.
        db.rel_push(
            "escaped_stack_region_field",
            (func, base_ofs, 26_i64, MemoryChunk::MInt8Unsigned),
        );
        db.rel_push(
            "stack_var",
            (func, 0xb100_u64, base_ofs + 4, updated_field4),
        );

        let arrays = derive_escaped_stack_array_layouts(&db);
        assert!(!arrays.arrays.contains_key(&func));
        let buffers = derive_escaped_stack_buffer_layouts(&db, &arrays);
        assert_eq!(
            buffers
                .buffers
                .get(&func)
                .and_then(|entries| entries.get(&fields[0].2)),
            Some(&27)
        );
        assert_eq!(
            buffers
                .members
                .get(&func)
                .and_then(|entries| entries.get(&fields[3].2)),
            Some(&(fields[0].2, 16, MemoryChunk::MAny64))
        );
        assert_eq!(
            buffers
                .members
                .get(&func)
                .and_then(|entries| entries.get(&updated_field4)),
            Some(&(fields[0].2, 4, MemoryChunk::MInt32))
        );
        assert_eq!(buffers.members.get(&func).map(HashMap::len), Some(6));
    }

    #[test]
    fn escaped_buffer_membership_does_not_follow_region_span_alone() {
        let mut db = DecompileDB::default();
        let func: Address = 0xb100;
        let base_ofs = 16_i64;
        let base: RTLReg = 0x8100;
        let enclosed_scalar: RTLReg = 0x8200;
        let exact_tail: RTLReg = 0x8300;

        for (index, (field_ofs, local)) in [(0_i64, base), (64_i64, exact_tail)]
            .into_iter()
            .enumerate()
        {
            db.rel_push(
                "escaped_stack_region_field",
                (func, base_ofs, field_ofs, MemoryChunk::MAny64),
            );
            db.rel_push(
                "stack_var",
                (func, 0xb200 + index as u64, base_ofs + field_ofs, local),
            );
        }
        db.rel_push("slot_escaped_canonical", (func, base_ofs, base));
        db.rel_push(
            "stack_var",
            (func, 0xb210_u64, base_ofs + 50, enclosed_scalar),
        );

        let arrays = derive_escaped_stack_array_layouts(&db);
        assert!(!arrays.arrays.contains_key(&func));
        let buffers = derive_escaped_stack_buffer_layouts(&db, &arrays);

        assert_eq!(
            buffers.buffers.get(&func).and_then(|m| m.get(&base)),
            Some(&72),
        );
        assert_eq!(
            buffers.members.get(&func).and_then(|m| m.get(&exact_tail)),
            Some(&(base, 64, MemoryChunk::MAny64)),
        );
        assert!(buffers
            .members
            .get(&func)
            .is_none_or(|members| !members.contains_key(&enclosed_scalar)));
    }

    #[test]
    fn byte_buffer_accepts_nested_access_widths_at_one_offset() {
        let mut db = DecompileDB::default();
        let func: Address = 0xb080;
        let base_ofs = 16_i64;
        let base: RTLReg = 0x8000;
        let packed: RTLReg = 0x8010;
        db.rel_push(
            "escaped_stack_region_field",
            (func, base_ofs, 0_i64, MemoryChunk::MAny64),
        );
        for chunk in [MemoryChunk::MInt8Unsigned, MemoryChunk::MInt16Unsigned] {
            db.rel_push("escaped_stack_region_field", (func, base_ofs, 8_i64, chunk));
        }
        db.rel_push("slot_escaped_canonical", (func, base_ofs, base));
        db.rel_push("stack_var", (func, 0xb081_u64, base_ofs, base));
        db.rel_push("stack_var", (func, 0xb082_u64, base_ofs + 8, packed));

        let arrays = derive_escaped_stack_array_layouts(&db);
        let buffers = derive_escaped_stack_buffer_layouts(&db, &arrays);

        assert_eq!(
            buffers
                .buffers
                .get(&func)
                .and_then(|items| items.get(&base)),
            Some(&10),
        );
        assert_eq!(
            buffers
                .members
                .get(&func)
                .and_then(|items| items.get(&packed)),
            Some(&(base, 8, MemoryChunk::MInt16Unsigned)),
        );
    }

    #[test]
    fn enclosed_escaped_region_extends_its_encloser_to_its_far_end() {
        let mut db = DecompileDB::default();

        // du's filesystem_type shape, scaled down: the outer region's derived
        // span covers the inner region's base, and the inner region carries an
        // ABI extent (fstatfs writes a 120-byte statfs at +16) that nothing
        // else states.  Dropping the inner region under-reserves the buffer
        // and the callee smashes the stack.
        let func: Address = 0xbb30;
        let outer: RTLReg = 0x7100;
        let inner: RTLReg = 0x7200;
        for (field_ofs, chunk) in [
            (0_i64, MemoryChunk::MAny64),
            (16_i64, MemoryChunk::MAny64),
            (64_i64, MemoryChunk::MAny64),
        ] {
            db.rel_push(
                "escaped_stack_region_field",
                (func, 0_i64, field_ofs, chunk),
            );
        }
        db.rel_push(
            "escaped_stack_region_caller_field",
            (func, 16_i64, 0_i64, MemoryChunk::MAny64),
        );
        db.rel_push("escaped_stack_region_extent", (func, 16_i64, 120_i64));
        db.rel_push("slot_escaped_canonical", (func, 0_i64, outer));
        db.rel_push("slot_escaped_canonical", (func, 16_i64, inner));
        for (idx, (ofs, local)) in [(0_i64, outer), (16_i64, inner)].into_iter().enumerate() {
            db.rel_push("stack_var", (func, 0x100 + idx as u64, ofs, local));
        }

        // The same enclosure at a NONZERO outer base: lengths and frame
        // offsets are different coordinates, and a base-0 outer hides any
        // confusion between them.
        let shifted_func: Address = 0xc100;
        let shifted_outer: RTLReg = 0x9100;
        let shifted_inner: RTLReg = 0x9200;
        for (field_ofs, chunk) in [
            (0_i64, MemoryChunk::MAny64),
            (16_i64, MemoryChunk::MAny64),
            (64_i64, MemoryChunk::MAny64),
        ] {
            db.rel_push(
                "escaped_stack_region_field",
                (shifted_func, 32_i64, field_ofs, chunk),
            );
        }
        db.rel_push(
            "escaped_stack_region_caller_field",
            (shifted_func, 48_i64, 0_i64, MemoryChunk::MAny64),
        );
        db.rel_push(
            "escaped_stack_region_extent",
            (shifted_func, 48_i64, 120_i64),
        );
        db.rel_push(
            "slot_escaped_canonical",
            (shifted_func, 32_i64, shifted_outer),
        );
        db.rel_push(
            "slot_escaped_canonical",
            (shifted_func, 48_i64, shifted_inner),
        );
        for (idx, (ofs, local)) in [(32_i64, shifted_outer), (48_i64, shifted_inner)]
            .into_iter()
            .enumerate()
        {
            db.rel_push("stack_var", (shifted_func, 0x300 + idx as u64, ofs, local));
        }

        // A region that merely abuts the previous one's far end is a separate
        // object and must keep its own buffer.
        let adjacent_func: Address = 0xd000;
        let adj_a: RTLReg = 0x8100;
        let adj_b: RTLReg = 0x8200;
        for (base, local) in [(0_i64, adj_a), (16_i64, adj_b)] {
            db.rel_push(
                "escaped_stack_region_caller_field",
                (adjacent_func, base, 0_i64, MemoryChunk::MAny64),
            );
            db.rel_push("escaped_stack_region_extent", (adjacent_func, base, 16_i64));
            db.rel_push("slot_escaped_canonical", (adjacent_func, base, local));
            db.rel_push(
                "stack_var",
                (adjacent_func, 0x200 + base as u64, base, local),
            );
        }

        let arrays = derive_escaped_stack_array_layouts(&db);
        let buffers = derive_escaped_stack_buffer_layouts(&db, &arrays);

        // The outer buffer reaches the enclosed region's far end: 16 + 120.
        assert_eq!(
            buffers.buffers.get(&func).and_then(|m| m.get(&outer)),
            Some(&136)
        );
        // The enclosed region emits no buffer of its own; its base local is a
        // member of the encloser at its absolute offset.
        assert!(!buffers
            .buffers
            .get(&func)
            .is_some_and(|m| m.contains_key(&inner)));
        assert_eq!(
            buffers.members.get(&func).and_then(|m| m.get(&inner)),
            Some(&(outer, 16, MemoryChunk::MAny64))
        );

        // The shifted encloser reaches 48 - 32 + 120 = 136 as well, and the
        // enclosed base becomes its member at frame offset 48 - 32 = 16.
        assert_eq!(
            buffers
                .buffers
                .get(&shifted_func)
                .and_then(|m| m.get(&shifted_outer)),
            Some(&136)
        );
        assert!(!buffers
            .buffers
            .get(&shifted_func)
            .is_some_and(|m| m.contains_key(&shifted_inner)));
        assert_eq!(
            buffers
                .members
                .get(&shifted_func)
                .and_then(|m| m.get(&shifted_inner)),
            Some(&(shifted_outer, 16, MemoryChunk::MAny64))
        );

        // Adjacent regions stay two objects of their own sizes.
        assert_eq!(
            buffers
                .buffers
                .get(&adjacent_func)
                .and_then(|m| m.get(&adj_a)),
            Some(&16)
        );
        assert_eq!(
            buffers
                .buffers
                .get(&adjacent_func)
                .and_then(|m| m.get(&adj_b)),
            Some(&16)
        );
    }

    #[test]
    fn mixed_buffer_owns_overlapping_uniform_subregion() {
        let mut db = DecompileDB::default();
        let func: Address = 0xc000;
        let outer_ofs = -32_i64;
        let inner_ofs = outer_ofs + 8;
        let outer: RTLReg = 0x8100;
        let inner: RTLReg = 0x8200;
        let tail: RTLReg = 0x8300;

        // The outer region is mixed-width and therefore needs a byte buffer.
        for (field_ofs, chunk) in [
            (0_i64, MemoryChunk::MInt32),
            (8_i64, MemoryChunk::MAny64),
            (16_i64, MemoryChunk::MAny64),
        ] {
            db.rel_push(
                "escaped_stack_region_field",
                (func, outer_ofs, field_ofs, chunk),
            );
        }
        // The same physical cells also form a uniform subregion observed
        // through an interior pointer.
        for field_ofs in [0_i64, 8] {
            db.rel_push(
                "escaped_stack_region_field",
                (func, inner_ofs, field_ofs, MemoryChunk::MAny64),
            );
        }
        for (idx, (ofs, local)) in [
            (outer_ofs, outer),
            (inner_ofs, inner),
            (inner_ofs + 8, tail),
        ]
        .into_iter()
        .enumerate()
        {
            db.rel_push("stack_var", (func, 0xc100 + idx as u64, ofs, local));
            db.rel_push("slot_escaped_region_canonical", (func, ofs, local));
        }
        db.rel_push("slot_escaped_canonical", (func, outer_ofs, outer));

        let mut arrays = derive_escaped_stack_array_layouts(&db);
        assert_eq!(
            arrays.arrays.get(&func).and_then(|m| m.get(&inner)),
            Some(&(MemoryChunk::MAny64, 2))
        );
        let buffers = derive_escaped_stack_buffer_layouts(&db, &arrays);
        assert_eq!(
            buffers.members.get(&func).and_then(|m| m.get(&inner)),
            Some(&(outer, 8, MemoryChunk::MAny64))
        );

        remove_buffer_owned_array_layouts(&mut arrays, &buffers);

        assert!(!arrays.arrays.contains_key(&func));
        assert!(!arrays.members.contains_key(&func));
        assert_eq!(
            buffers.buffers.get(&func).and_then(|m| m.get(&outer)),
            Some(&24)
        );
    }
}

#[cfg(test)]
mod ordering_tests {
    use super::*;

    type Node = crate::x86::types::Node;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn tint() -> clight::ClightType {
        clight::ClightType::Tint(
            clight::ClightIntSize::I32,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        )
    }

    fn c32(value: i32) -> clight::ClightExpr {
        clight::ClightExpr::EconstInt(value, tint())
    }

    fn position(nodes: &[Node], needle: Node) -> usize {
        nodes.iter().position(|node| *node == needle).unwrap()
    }

    #[test]
    fn nested_gotos_order_exact_surviving_targets_after_loop() {
        // Targets deliberately sort before the loop key. Their reachability comes
        // from the selected statement tree, never from address magnitude.
        let entry = 0x9000;
        let loop_header = 0xf000;
        let target_low = 0x10;
        let target_high = 0x20;
        let missing_target = 0x30;

        let loop_stmt = clight::ClightStmt::Sloop(
            Box::new(clight::ClightStmt::Sifthenelse(
                c32(1),
                Box::new(clight::ClightStmt::Sgoto(target_low as usize)),
                Box::new(clight::ClightStmt::Sswitch(
                    c32(0),
                    vec![
                        (
                            Some(0),
                            clight::ClightStmt::Slabel(
                                7,
                                Box::new(clight::ClightStmt::Sgoto(target_high as usize)),
                            ),
                        ),
                        (None, clight::ClightStmt::Sgoto(missing_target as usize)),
                    ],
                )),
            )),
            // A self-target is control flow inside this top-level statement.
            Box::new(clight::ClightStmt::Sgoto(loop_header as usize)),
        );
        let statements = HashMap::from([
            (entry, clight::ClightStmt::Sskip),
            (loop_header, loop_stmt),
            (target_low, clight::ClightStmt::Sskip),
            (target_high, clight::ClightStmt::Sskip),
        ]);
        let surviving_nodes: HashSet<_> = statements.keys().copied().collect();
        let raw_edges = vec![(entry, loop_header)];
        let empty_loops = HashMap::new();

        let without_structural_edges = order_nodes_dfs(
            entry,
            &surviving_nodes,
            &raw_edges,
            |node| node == loop_header,
            &empty_loops,
            &HashMap::new(),
            |node| node,
        );
        assert!(
            position(&without_structural_edges, target_low)
                < position(&without_structural_edges, loop_header)
        );

        let goto_edges = structured_goto_order_edges(&statements, &surviving_nodes);
        assert_eq!(
            goto_edges,
            vec![(loop_header, target_low), (loop_header, target_high)]
        );
        let mut ordering_edges = raw_edges;
        ordering_edges.extend(goto_edges);
        let ordered = order_nodes_dfs(
            entry,
            &surviving_nodes,
            &ordering_edges,
            |node| node == loop_header,
            &empty_loops,
            &HashMap::new(),
            |node| node,
        );
        assert_eq!(ordered, vec![entry, loop_header, target_high, target_low]);
    }

    #[test]
    fn detached_loop_redirects_only_initial_frontier_not_later_body_reentry() {
        // The preheader and raw body nodes are absorbed, while the selected
        // Sloop and its external goto targets survive. Generated identifiers
        // make the regression independent of any binary's concrete addresses.
        let [entry, raw_preheader, loop_header, raw_body, reentry_body, external_target_a, external_target_b, later_reentry, post_loop, label] =
            synthetic_ids();

        // This real shape has several nested gotos from the structured loop to
        // surviving external targets, while the raw header itself has exactly
        // one continuation into the natural-loop body.
        let loop_stmt = clight::ClightStmt::Sloop(
            Box::new(clight::ClightStmt::Ssequence(vec![
                clight::ClightStmt::Sgoto(external_target_a as usize),
                clight::ClightStmt::Sswitch(
                    c32(0),
                    vec![(None, clight::ClightStmt::Sgoto(external_target_b as usize))],
                ),
            ])),
            Box::new(clight::ClightStmt::Sskip),
        );
        let reentry_stmt = clight::ClightStmt::Slabel(
            label as usize,
            Box::new(clight::ClightStmt::Sifthenelse(
                c32(1),
                Box::new(clight::ClightStmt::Sgoto(reentry_body as usize)),
                Box::new(clight::ClightStmt::Sset(1, c32(0))),
            )),
        );
        assert!(!clight_stmt_exits(&reentry_stmt));

        let statements = HashMap::from([
            (entry, clight::ClightStmt::Sskip),
            (loop_header, loop_stmt),
            (external_target_a, clight::ClightStmt::Sskip),
            (external_target_b, clight::ClightStmt::Sskip),
            (later_reentry, reentry_stmt),
            (post_loop, clight::ClightStmt::Sreturn(None)),
        ]);
        let surviving_nodes: HashSet<_> = statements.keys().copied().collect();
        let raw_edges = vec![
            (entry, raw_preheader),
            (raw_preheader, raw_body),
            (loop_header, raw_body),
            (raw_body, external_target_a),
            (external_target_a, later_reentry),
            (external_target_b, later_reentry),
            (later_reentry, reentry_body),
            (later_reentry, post_loop),
        ];
        let loop_body = HashSet::from([loop_header, raw_body, reentry_body]);
        let loop_members = HashMap::from([(loop_header, loop_body.clone())]);
        let node_innermost_loop: HashMap<_, _> = loop_body
            .iter()
            .copied()
            .map(|node| (node, loop_header))
            .collect();

        // The old disconnected-header fallback sees only the later surviving
        // re-entry's direct body edge, so it inserts the Sloop after that branch.
        let before = order_nodes_dfs(
            entry,
            &surviving_nodes,
            &raw_edges,
            |node| node == loop_header || node == post_loop,
            &loop_members,
            &node_innermost_loop,
            |node| node,
        );
        assert!(position(&before, later_reentry) < position(&before, loop_header));

        let mut ordering_edges = raw_edges.clone();
        redirect_structured_loop_entry_edges(
            entry,
            &statements,
            &surviving_nodes,
            &mut ordering_edges,
            &loop_members,
            |node| node,
        );
        assert!(ordering_edges.contains(&(raw_preheader, loop_header)));
        assert!(!ordering_edges.contains(&(raw_preheader, raw_body)));
        assert!(ordering_edges.contains(&(loop_header, raw_body)));
        // This source is reachable only after crossing the loop body, so its
        // legitimate body re-entry must not be rewritten as an initial entry.
        assert!(ordering_edges.contains(&(later_reentry, reentry_body)));
        assert!(!ordering_edges.contains(&(later_reentry, loop_header)));

        let goto_edges = structured_goto_order_edges(&statements, &surviving_nodes);
        assert_eq!(
            goto_edges,
            vec![
                (loop_header, external_target_a),
                (loop_header, external_target_b),
            ]
        );
        ordering_edges.extend(goto_edges);
        ordering_edges.sort_unstable();
        ordering_edges.dedup();

        let ordered = order_nodes_dfs(
            entry,
            &surviving_nodes,
            &ordering_edges,
            |node| node == loop_header || node == post_loop,
            &loop_members,
            &node_innermost_loop,
            |node| node,
        );
        assert_eq!(&ordered[..2], &[entry, loop_header]);
        assert!(position(&ordered, loop_header) < position(&ordered, external_target_a));
        assert!(position(&ordered, loop_header) < position(&ordered, external_target_b));
        assert!(position(&ordered, loop_header) < position(&ordered, later_reentry));
    }

    #[test]
    fn loop_frontier_rewrite_rejects_multiple_initial_entry_targets() {
        let entry = 0x9000;
        let preheader_a = 0x10;
        let preheader_b = 0x20;
        let loop_header = 0xf000;
        let body_a = 0x30;
        let body_b = 0x40;
        let statements = HashMap::from([
            (entry, clight::ClightStmt::Sskip),
            (
                loop_header,
                clight::ClightStmt::Sloop(
                    Box::new(clight::ClightStmt::Sskip),
                    Box::new(clight::ClightStmt::Sskip),
                ),
            ),
        ]);
        let surviving_nodes: HashSet<_> = statements.keys().copied().collect();
        let original = vec![
            (entry, preheader_a),
            (entry, preheader_b),
            (preheader_a, body_a),
            (preheader_b, body_b),
            (loop_header, body_a),
        ];
        let loop_members =
            HashMap::from([(loop_header, HashSet::from([loop_header, body_a, body_b]))]);
        let mut ordering_edges = original.clone();
        redirect_structured_loop_entry_edges(
            entry,
            &statements,
            &surviving_nodes,
            &mut ordering_edges,
            &loop_members,
            |node| node,
        );
        assert_eq!(ordering_edges, original);
    }

    #[test]
    fn disconnected_component_order_follows_cfg_not_node_magnitude() {
        let entry = 0x9000;
        let call = 0xf000;
        let transparent_jump = 0x20;
        let return_node = 0x10;
        let nodes = HashSet::from([entry, call, return_node]);
        let edges = vec![(call, transparent_jump), (transparent_jump, return_node)];

        let ordered = order_nodes_dfs(
            entry,
            &nodes,
            &edges,
            |node| node == return_node,
            &HashMap::new(),
            &HashMap::new(),
            |node| node,
        );

        assert_eq!(ordered, vec![entry, call, return_node]);
    }

    #[test]
    fn disconnected_predecessor_anchors_before_reachable_epilogue() {
        let entry = 0x9000;
        let call = 0xf000;
        let transparent_jump = 0x20;
        let epilogue = 0x10;
        let nodes = HashSet::from([entry, call, epilogue]);
        let edges = vec![
            (entry, epilogue),
            (call, transparent_jump),
            (transparent_jump, epilogue),
        ];

        let ordered = order_nodes_dfs(
            entry,
            &nodes,
            &edges,
            |node| node == epilogue,
            &HashMap::new(),
            &HashMap::new(),
            |node| node,
        );

        assert_eq!(ordered, vec![entry, call, epilogue]);
    }

    #[test]
    fn tagged_sseq_member_exit_edge_is_owned_by_live_anchor() {
        let anchor = 0x9000;
        let tagged_store = (1_u64 << 62) | 0x9010;
        let jump = 0x0100;
        let return_node = 0x0200;
        let raw_edges = vec![
            (anchor, tagged_store),
            (tagged_store, jump),
            (jump, return_node),
        ];
        let member_to_head = HashMap::from([(tagged_store, anchor)]);
        let remapped = remap_sseq_edges(&raw_edges, &member_to_head);

        assert!(remapped.contains(&(anchor, jump)));
        assert!(!remapped.iter().any(|(src, _)| *src == tagged_store));

        let nodes = HashSet::from([anchor, jump, return_node]);
        let ordered = order_nodes_dfs(
            anchor,
            &nodes,
            &remapped,
            |node| node == return_node,
            &HashMap::new(),
            &HashMap::new(),
            |node| node,
        );
        assert_eq!(ordered, vec![anchor, jump, return_node]);
    }

    // C has no floating-point pointer arithmetic, so a pointer-annotated operand meeting a
    // float one is not pointer arithmetic; emitting the cast anyway produced
    // `char * - double`, which gcc rejects and which cost stripped sort its whole relink.
    #[test]
    fn a_float_operand_never_takes_the_pointer_arithmetic_form() {
        let dbl =
            clight::ClightType::Tfloat(clight::ClightFloatSize::F64, clight::ClightAttr::default());
        let ptr = clight::ClightType::Tpointer(
            Arc::new(clight::ClightType::Tvoid),
            clight::ClightAttr::default(),
        );
        let expr = clight::ClightExpr::Ebinop(
            clight::ClightBinaryOp::Osub,
            Box::new(clight::ClightExpr::Etempvar(1, ptr)),
            Box::new(clight::ClightExpr::Etempvar(2, dbl.clone())),
            dbl,
        );

        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        let converted = convert_expr(&expr, &mut ctx);

        let lhs_is_pointer_cast = match &converted {
            CExpr::Binary(_, lhs, _) => {
                matches!(lhs.as_ref(), CExpr::Cast(CType::Pointer(..), _))
            }
            _ => false,
        };
        assert!(
            !lhs_is_pointer_cast,
            "a float operand took the pointer-arithmetic form: {converted:?}"
        );
    }

    #[test]
    fn dead_label_cleanup_keeps_structural_fallthrough_section() {
        fn contains_return(stmt: &CStmt) -> bool {
            match stmt {
                CStmt::Return(_) => true,
                CStmt::Block(items) => items.iter().any(|item| match item {
                    CBlockItem::Stmt(stmt) => contains_return(stmt),
                    CBlockItem::Decl(_) => false,
                }),
                CStmt::Sequence(stmts) => stmts.iter().any(contains_return),
                CStmt::If(_, then_stmt, else_stmt) => {
                    contains_return(then_stmt) || else_stmt.as_deref().is_some_and(contains_return)
                }
                CStmt::While(_, body)
                | CStmt::DoWhile(body, _)
                | CStmt::For(_, _, _, body)
                | CStmt::Switch(_, body)
                | (CStmt::Labeled(_, body) | CStmt::Effect(_, body)) => contains_return(body),
                _ => false,
            }
        }

        let body = CStmt::Block(vec![
            CBlockItem::Stmt(CStmt::Goto("other_exit".to_string())),
            CBlockItem::Stmt(CStmt::Labeled(
                Label::Named("fallthrough_epilogue".to_string()),
                Box::new(CStmt::Empty),
            )),
            CBlockItem::Stmt(CStmt::Labeled(
                Label::Named("return_site".to_string()),
                Box::new(CStmt::Return(Some(CExpr::int(7)))),
            )),
        ]);

        let cleaned = eliminate_dead_code_preserving_section_labels(&body);

        assert!(
            contains_return(&cleaned),
            "stripping unreferenced section labels before DCE erased a live CFG return: {cleaned:#?}"
        );
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => simplify_xor_self_in_stmt(inner),
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => strip_dead_expr_stmts(inner),
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
    // RB-1: infallible -- the is_empty() return above guarantees a first char.
    let first = s.chars().next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' {
        return false;
    }
    s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn strip_dead_labels_in_stmt(stmt: &mut CStmt) {
    use crate::decompile::passes::c_pass::helpers::{
        collect_all_labels, collect_goto_targets, strip_dead_labels,
    };

    let goto_targets: HashSet<String> = collect_goto_targets(stmt).into_iter().collect();
    let all_labels: HashSet<String> = collect_all_labels(stmt).into_iter().collect();

    let dead_labels: HashSet<String> = all_labels.difference(&goto_targets).cloned().collect();
    if dead_labels.is_empty() {
        return;
    }

    *stmt = strip_dead_labels(stmt, &dead_labels);
}

/// Dead-code pruning uses labels as structural section boundaries. A selected
/// CFG path can reach a label by fallthrough even when no explicit C goto names
/// it, so stripping labels first can make a second pruning pass erase the live
/// section. Prune while those boundaries are still present, then remove only
/// labels that are unnecessary in the final C syntax.
fn eliminate_dead_code_preserving_section_labels(stmt: &CStmt) -> CStmt {
    let mut cleaned = eliminate_dead_code(stmt);
    strip_dead_labels_in_stmt(&mut cleaned);
    cleaned
}

fn count_leaf_stmts_in_block(items: &[CBlockItem]) -> usize {
    items
        .iter()
        .map(|item| match item {
            CBlockItem::Stmt(s) => count_leaf_stmts(s),
            CBlockItem::Decl(_) => 1,
        })
        .sum()
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => count_leaf_stmts(inner),
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

fn rewrite_tailcall_gotos(
    body_items: &mut Vec<CBlockItem>,
    func_names: &HashMap<String, usize>,
    current_func: &str,
) {
    for item in body_items.iter_mut() {
        if let CBlockItem::Stmt(stmt) = item {
            rewrite_tailcall_gotos_in_stmt(stmt, func_names, current_func);
        }
    }
}

fn rewrite_tailcall_gotos_in_stmt(
    stmt: &mut CStmt,
    func_names: &HashMap<String, usize>,
    current_func: &str,
) {
    match stmt {
        CStmt::Goto(target)
            if func_names.contains_key(target.as_str())
                && target != current_func
                && func_names.get(target.as_str()) == Some(&0) =>
        {
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
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => rewrite_tailcall_gotos_in_stmt(inner, func_names, current_func),
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
            if let Some(e) = else_s {
                collect_called_names_in_stmt(e, names);
            }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_called_names_in_expr(cond, names);
            collect_called_names_in_stmt(body, names);
        }
        CStmt::For(_, cond, update, body) => {
            if let Some(c) = cond {
                collect_called_names_in_expr(c, names);
            }
            if let Some(u) = update {
                collect_called_names_in_expr(u, names);
            }
            collect_called_names_in_stmt(body, names);
        }
        CStmt::Switch(expr, body) => {
            collect_called_names_in_expr(expr, names);
            collect_called_names_in_stmt(body, names);
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_called_names_in_stmt(s, names);
            }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_called_names_in_stmt(s, names);
                }
            }
        }
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_called_names_in_stmt(inner, names),
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
            for arg in args {
                collect_called_names_in_expr(arg, names);
            }
        }
        CExpr::Assign(_, lhs, rhs) => {
            collect_called_names_in_expr(lhs, names);
            collect_called_names_in_expr(rhs, names);
        }
        CExpr::Binary(_, lhs, rhs) => {
            collect_called_names_in_expr(lhs, names);
            collect_called_names_in_expr(rhs, names);
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) => {
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

// IL-1: forward-declaration parameter types from a JOIN over call-site evidence; every site must agree on arity and yield classifiable evidence, else the K&R int f() fallback stands.

/// Per-position evidence as a join-semilattice over (class, width): Int|Int takes max width, Int|Float widens to Float(64), Ptr|Ptr unifies to void* except poisoning fn-ptr mismatches.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq)]
enum ArgEvidence {
    Bottom,
    Int(u8, Signedness),
    Float(u8),
    /// Pointer class; `Some(T)` = exact pointer type evidenced, `None` = unknown pointee (emitted `void *`).
    Ptr(Option<CType>),
    TopIntPtr,
    Poison,
}

#[cfg(test)]
impl ArgEvidence {
    /// Lattice join: commutative, associative, idempotent -- result is independent of call-site arrival order.
    fn join(self, other: ArgEvidence) -> ArgEvidence {
        use ArgEvidence::*;
        match (self, other) {
            (Poison, _) | (_, Poison) => Poison,
            (Bottom, x) | (x, Bottom) => x,
            (Int(w1, s1), Int(w2, s2)) => {
                if w1 == w2 {
                    let s = if s1 == s2 { s1 } else { Signedness::Signed };
                    Int(w1, s)
                } else if w1 > w2 {
                    Int(w1, s1)
                } else {
                    Int(w2, s2)
                }
            }
            (Float(w1), Float(w2)) => Float(w1.max(w2)),
            // Documented: int | float widens to double (see type-level docs).
            (Int(_, _), Float(_)) | (Float(_), Int(_, _)) => Float(64),
            (Ptr(a), Ptr(b)) => {
                if a == b {
                    Ptr(a)
                } else if ctype_opt_involves_function(&a) || ctype_opt_involves_function(&b) {
                    // Differing function-pointer types must not unify to void* (not implicit in strict C).
                    Poison
                } else {
                    Ptr(None)
                }
            }
            // Mixed scalar/pointer classes meet at the int/ptr-safe top.
            (TopIntPtr, _) | (_, TopIntPtr) => TopIntPtr,
            (Int(_, _), Ptr(_)) | (Ptr(_), Int(_, _)) => TopIntPtr,
            (Float(_), Ptr(_)) | (Ptr(_), Float(_)) => TopIntPtr,
        }
    }

    /// The C type to emit for a fully-joined position; `None` only for `Poison`, which forces the whole declaration to the K&R fallback.
    fn to_ctype(&self, model: crate::abi::DataModel) -> Option<CType> {
        use crate::decompile::passes::c_pass::types::{FloatSize, IntSize};
        match self {
            // Bottom = no evidence: conservative default (long accepts both ints and pointers untruncated).
            ArgEvidence::Bottom => Some(CType::long()),
            ArgEvidence::Int(w, s) => {
                // Above 32 bits this is a 64-bit value, so it takes the
                // model's spelling rather than a bare `long`.
                if *w > 32 {
                    return Some(CType::int64(model, *s));
                }
                let sz = match *w {
                    0..=8 => IntSize::Char,
                    9..=16 => IntSize::Short,
                    _ => IntSize::Int,
                };
                Some(CType::Int(sz, *s))
            }
            ArgEvidence::Float(w) => Some(CType::Float(if *w <= 32 {
                FloatSize::Float
            } else {
                FloatSize::Double
            })),
            ArgEvidence::Ptr(Some(ty)) => Some(ty.clone()),
            ArgEvidence::Ptr(None) => Some(CType::ptr(CType::Void)),
            ArgEvidence::TopIntPtr => Some(CType::long()),
            ArgEvidence::Poison => None,
        }
    }
}

fn ctype_involves_function(ty: &CType) -> bool {
    match ty {
        CType::Function(_, _, _, _) => true,
        CType::Pointer(inner, _) | CType::Array(inner, _) | CType::Qualified(inner, _) => {
            ctype_involves_function(inner)
        }
        _ => false,
    }
}

fn ctype_opt_involves_function(ty: &Option<CType>) -> bool {
    ty.as_ref().map_or(false, ctype_involves_function)
}

/// Classify a declared C type as argument evidence.
#[cfg(test)]
fn arg_evidence_of_ctype(ty: &CType) -> ArgEvidence {
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize};
    match ty {
        CType::Int(sz, s) => {
            let w = match sz {
                IntSize::Char => 8,
                IntSize::Short => 16,
                IntSize::Int => 32,
                IntSize::Long | IntSize::LongLong => 64,
                IntSize::Int128 => 128,
            };
            ArgEvidence::Int(w, *s)
        }
        CType::Bool => ArgEvidence::Int(8, Signedness::Unsigned),
        CType::Enum(_) => ArgEvidence::Int(32, Signedness::Signed),
        CType::Float(FloatSize::Float) => ArgEvidence::Float(32),
        CType::Float(_) => ArgEvidence::Float(64),
        CType::Pointer(_, _) => ArgEvidence::Ptr(Some(ty.clone())),
        // Arrays and function designators decay to pointers in argument position.
        CType::Array(inner, _) => ArgEvidence::Ptr(Some(CType::ptr(inner.as_ref().clone()))),
        CType::Function(_, _, _, _) => ArgEvidence::Ptr(Some(CType::ptr(ty.clone()))),
        CType::Qualified(inner, _) => arg_evidence_of_ctype(inner),
        // void/struct/union/typedef: not a scalar class we can safely type a parameter from.
        _ => ArgEvidence::Poison,
    }
}

/// Type environment for classifying call arguments: exactly the declarations the C compiler sees; locals shadow globals.
#[cfg(test)]
struct ArgEvidenceEnv<'a> {
    local_types: HashMap<String, CType>,
    global_types: &'a HashMap<String, CType>,
    callee_ret: &'a HashMap<String, CType>,
}

#[cfg(test)]
impl ArgEvidenceEnv<'_> {
    fn var_type(&self, name: &str) -> Option<&CType> {
        self.local_types
            .get(name)
            .or_else(|| self.global_types.get(name))
    }
}

/// Classify one call-site argument expression; returns `Poison` when the declared type cannot be determined.
#[cfg(test)]
fn arg_evidence_of_expr(expr: &CExpr, env: &ArgEvidenceEnv) -> ArgEvidence {
    use crate::decompile::passes::c_pass::types::UnaryOp;
    match expr {
        CExpr::Cast(ty, _) => arg_evidence_of_ctype(ty),
        CExpr::StringLit(_) => ArgEvidence::Ptr(Some(CType::ptr(CType::char_signed()))),
        // A literal 0 is a valid int, float, and null pointer constant.
        CExpr::IntLit(l) if l.value == 0 => ArgEvidence::Bottom,
        CExpr::IntLit(l) => {
            use crate::decompile::passes::c_pass::types::IntLiteralSuffix as S;
            let (suffix_wide, unsigned) = match l.suffix {
                S::None => (false, false),
                S::U => (false, true),
                S::L | S::LL => (true, false),
                _ => (true, true),
            };
            let fits32 = l.value >= i32::MIN as i128 && l.value <= u32::MAX as i128;
            let w = if suffix_wide || !fits32 { 64 } else { 32 };
            let s = if unsigned {
                Signedness::Unsigned
            } else {
                Signedness::Signed
            };
            ArgEvidence::Int(w, s)
        }
        CExpr::FloatLit(l) => {
            use crate::decompile::passes::c_pass::types::FloatLiteralSuffix as F;
            ArgEvidence::Float(if matches!(l.suffix, F::F) { 32 } else { 64 })
        }
        // A C character literal has type int.
        CExpr::CharLit(_) => ArgEvidence::Int(32, Signedness::Signed),
        CExpr::Var(name) => env
            .var_type(name)
            .map(arg_evidence_of_ctype)
            .unwrap_or(ArgEvidence::Poison),
        CExpr::Paren(inner) => arg_evidence_of_expr(inner, env),
        CExpr::Unary(UnaryOp::AddrOf, _) => ArgEvidence::Ptr(None),
        CExpr::Unary(UnaryOp::Deref, inner) => match arg_evidence_of_expr(inner, env) {
            ArgEvidence::Ptr(Some(CType::Pointer(p, _))) => arg_evidence_of_ctype(&p),
            _ => ArgEvidence::Poison,
        },
        CExpr::Unary(UnaryOp::Not, _) => ArgEvidence::Int(32, Signedness::Signed),
        CExpr::Unary(UnaryOp::Neg | UnaryOp::Plus | UnaryOp::BitNot, inner) => {
            match arg_evidence_of_expr(inner, env) {
                ev @ (ArgEvidence::Int(_, _) | ArgEvidence::Float(_) | ArgEvidence::Bottom) => ev,
                _ => ArgEvidence::Poison,
            }
        }
        CExpr::Unary(_, _) => ArgEvidence::Poison,
        CExpr::Binary(op, l, r) => {
            use crate::decompile::passes::c_pass::types::BinaryOp as B;
            match op {
                // Comparisons and logical connectives have type int.
                B::Eq | B::Ne | B::Lt | B::Le | B::Gt | B::Ge | B::And | B::Or => {
                    ArgEvidence::Int(32, Signedness::Signed)
                }
                B::Shl | B::Shr => match arg_evidence_of_expr(l, env) {
                    ev @ (ArgEvidence::Int(_, _) | ArgEvidence::Bottom) => ev,
                    _ => ArgEvidence::Poison,
                },
                B::Add | B::Sub => {
                    let le = arg_evidence_of_expr(l, env);
                    let re = arg_evidence_of_expr(r, env);
                    match (le, re) {
                        // ptr - ptr is ptrdiff_t; ptr +/- int keeps the pointer type.
                        (ArgEvidence::Ptr(_), ArgEvidence::Ptr(_)) if matches!(op, B::Sub) => {
                            ArgEvidence::Int(64, Signedness::Signed)
                        }
                        (p @ ArgEvidence::Ptr(_), ArgEvidence::Int(_, _) | ArgEvidence::Bottom)
                        | (ArgEvidence::Int(_, _) | ArgEvidence::Bottom, p @ ArgEvidence::Ptr(_)) => {
                            p
                        }
                        (
                            le @ (ArgEvidence::Int(_, _)
                            | ArgEvidence::Float(_)
                            | ArgEvidence::Bottom),
                            re @ (ArgEvidence::Int(_, _)
                            | ArgEvidence::Float(_)
                            | ArgEvidence::Bottom),
                        ) => le.join(re),
                        _ => ArgEvidence::Poison,
                    }
                }
                B::Mul | B::Div | B::Mod | B::BitAnd | B::BitOr | B::BitXor => {
                    let le = arg_evidence_of_expr(l, env);
                    let re = arg_evidence_of_expr(r, env);
                    match (&le, &re) {
                        (
                            ArgEvidence::Int(_, _) | ArgEvidence::Float(_) | ArgEvidence::Bottom,
                            ArgEvidence::Int(_, _) | ArgEvidence::Float(_) | ArgEvidence::Bottom,
                        ) => le.join(re),
                        _ => ArgEvidence::Poison,
                    }
                }
                _ => ArgEvidence::Poison,
            }
        }
        CExpr::Ternary(_, t, e) => {
            let te = arg_evidence_of_expr(t, env);
            let ee = arg_evidence_of_expr(e, env);
            match (&te, &ee) {
                // int/ptr-mixed ternary is not valid C; poison so the callee keeps the K&R decl rather than laundering it through TopIntPtr.
                (ArgEvidence::Ptr(_), ArgEvidence::Int(_, _))
                | (ArgEvidence::Int(_, _), ArgEvidence::Ptr(_)) => ArgEvidence::Poison,
                _ => te.join(ee),
            }
        }
        CExpr::Call(callee, _) => match callee.as_ref() {
            CExpr::Var(name) => env
                .callee_ret
                .get(name)
                .map(arg_evidence_of_ctype)
                .unwrap_or(ArgEvidence::Poison),
            _ => ArgEvidence::Poison,
        },
        CExpr::SizeofType(_) | CExpr::SizeofExpr(_) | CExpr::AlignofType(_) => {
            // size_t.
            ArgEvidence::Int(64, Signedness::Unsigned)
        }
        _ => ArgEvidence::Poison,
    }
}

/// Collect per-call-site argument evidence vectors keyed by callee name (deterministic TU walk order).
#[cfg(test)]
fn collect_call_arg_evidence_in_stmt(
    stmt: &CStmt,
    env: &ArgEvidenceEnv,
    sites: &mut HashMap<String, Vec<Vec<ArgEvidence>>>,
) {
    match stmt {
        CStmt::Expr(expr) => collect_call_arg_evidence_in_expr(expr, env, sites),
        CStmt::Return(Some(expr)) => collect_call_arg_evidence_in_expr(expr, env, sites),
        CStmt::If(cond, then_s, else_s) => {
            collect_call_arg_evidence_in_expr(cond, env, sites);
            collect_call_arg_evidence_in_stmt(then_s, env, sites);
            if let Some(e) = else_s {
                collect_call_arg_evidence_in_stmt(e, env, sites);
            }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_call_arg_evidence_in_expr(cond, env, sites);
            collect_call_arg_evidence_in_stmt(body, env, sites);
        }
        CStmt::For(_, cond, update, body) => {
            if let Some(c) = cond {
                collect_call_arg_evidence_in_expr(c, env, sites);
            }
            if let Some(u) = update {
                collect_call_arg_evidence_in_expr(u, env, sites);
            }
            collect_call_arg_evidence_in_stmt(body, env, sites);
        }
        CStmt::Switch(expr, body) => {
            collect_call_arg_evidence_in_expr(expr, env, sites);
            collect_call_arg_evidence_in_stmt(body, env, sites);
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_call_arg_evidence_in_stmt(s, env, sites);
            }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_call_arg_evidence_in_stmt(s, env, sites);
                }
            }
        }
        (CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)) => collect_call_arg_evidence_in_stmt(inner, env, sites),
        _ => {}
    }
}

#[cfg(test)]
fn collect_call_arg_evidence_in_expr(
    expr: &CExpr,
    env: &ArgEvidenceEnv,
    sites: &mut HashMap<String, Vec<Vec<ArgEvidence>>>,
) {
    match expr {
        CExpr::Call(callee, args) => {
            if let CExpr::Var(name) = callee.as_ref() {
                let evidence: Vec<ArgEvidence> =
                    args.iter().map(|a| arg_evidence_of_expr(a, env)).collect();
                sites.entry(name.clone()).or_default().push(evidence);
            }
            collect_call_arg_evidence_in_expr(callee, env, sites);
            for arg in args {
                collect_call_arg_evidence_in_expr(arg, env, sites);
            }
        }
        CExpr::Assign(_, lhs, rhs) | CExpr::Binary(_, lhs, rhs) => {
            collect_call_arg_evidence_in_expr(lhs, env, sites);
            collect_call_arg_evidence_in_expr(rhs, env, sites);
        }
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner) => {
            collect_call_arg_evidence_in_expr(inner, env, sites);
        }
        CExpr::Index(arr, idx) => {
            collect_call_arg_evidence_in_expr(arr, env, sites);
            collect_call_arg_evidence_in_expr(idx, env, sites);
        }
        CExpr::Ternary(a, b, c) => {
            collect_call_arg_evidence_in_expr(a, env, sites);
            collect_call_arg_evidence_in_expr(b, env, sites);
            collect_call_arg_evidence_in_expr(c, env, sites);
        }
        _ => {}
    }
}

/// Join per-site evidence into a parameter type vector per callee; a callee gets a typed prototype only when arity agrees across all sites and no position joins to Poison.
#[cfg(test)]
fn join_call_site_evidence(
    sites_by_callee: &HashMap<String, Vec<Vec<ArgEvidence>>>,
    model: crate::abi::DataModel,
) -> HashMap<String, Vec<CType>> {
    let mut joined: HashMap<String, Vec<CType>> = HashMap::new();
    for (name, sites) in sites_by_callee {
        let Some(first) = sites.first() else { continue };
        let arity = first.len();
        if sites.iter().any(|s| s.len() != arity) {
            continue; // arity disagreement: variadic-or-noise, keep K&R
        }
        let mut acc: Vec<ArgEvidence> = vec![ArgEvidence::Bottom; arity];
        for site in sites {
            for (slot, ev) in acc.iter_mut().zip(site.iter()) {
                *slot = std::mem::replace(slot, ArgEvidence::Bottom).join(ev.clone());
            }
        }
        let mut param_types = Vec::with_capacity(arity);
        let mut ok = true;
        for ev in &acc {
            match ev.to_ctype(model) {
                Some(t) => param_types.push(t),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if ok {
            joined.insert(name.clone(), param_types);
        }
    }
    joined
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
        CStmt::Effect(_, inner) => count_labels_in_stmt(inner, counts, rename_map),
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
            if let Some(e) = else_s {
                count_labels_in_stmt(e, counts, rename_map);
            }
        }
        CStmt::While(_, body)
        | CStmt::DoWhile(body, _)
        | CStmt::For(_, _, _, body)
        | CStmt::Switch(_, body) => {
            count_labels_in_stmt(body, counts, rename_map);
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                count_labels_in_stmt(s, counts, rename_map);
            }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    count_labels_in_stmt(s, counts, rename_map);
                }
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
                rename_map
                    .get(&(name.clone(), *occ))
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
            let then_s = Box::new(rename_duplicate_labels_in_stmt(
                then_s, rename_map, occurrence,
            ));
            let else_s = else_s
                .as_ref()
                .map(|e| Box::new(rename_duplicate_labels_in_stmt(e, rename_map, occurrence)));
            CStmt::If(cond.clone(), then_s, else_s)
        }
        CStmt::While(cond, body) => CStmt::While(
            cond.clone(),
            Box::new(rename_duplicate_labels_in_stmt(
                body, rename_map, occurrence,
            )),
        ),
        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(rename_duplicate_labels_in_stmt(
                body, rename_map, occurrence,
            )),
            cond.clone(),
        ),
        CStmt::For(i, c, u, body) => CStmt::For(
            i.clone(),
            c.clone(),
            u.clone(),
            Box::new(rename_duplicate_labels_in_stmt(
                body, rename_map, occurrence,
            )),
        ),
        CStmt::Switch(expr, body) => CStmt::Switch(
            expr.clone(),
            Box::new(rename_duplicate_labels_in_stmt(
                body, rename_map, occurrence,
            )),
        ),
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts
                .iter()
                .map(|s| rename_duplicate_labels_in_stmt(s, rename_map, occurrence))
                .collect(),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => {
                        CBlockItem::Stmt(rename_duplicate_labels_in_stmt(s, rename_map, occurrence))
                    }
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::Labeled(label, inner) => CStmt::Labeled(
            label.clone(),
            Box::new(rename_duplicate_labels_in_stmt(
                inner, rename_map, occurrence,
            )),
        ),
        CStmt::Effect(label, inner) => CStmt::Effect(
            label.clone(),
            Box::new(rename_duplicate_labels_in_stmt(
                inner, rename_map, occurrence,
            )),
        ),
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
            else_s
                .as_ref()
                .map(|e| Box::new(remove_gotos_to_missing_labels(e, missing))),
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
            stmts
                .iter()
                .map(|s| remove_gotos_to_missing_labels(s, missing))
                .collect(),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => {
                        CBlockItem::Stmt(remove_gotos_to_missing_labels(s, missing))
                    }
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::Labeled(l, inner) => CStmt::Labeled(
            l.clone(),
            Box::new(remove_gotos_to_missing_labels(inner, missing)),
        ),
        CStmt::Effect(l, inner) => CStmt::Effect(
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
            let items: Vec<CBlockItem> =
                stmts.iter().map(|s| CBlockItem::Stmt(s.clone())).collect();
            let new_items = forward_return_in_block_items(&items);
            let new_stmts: Vec<CStmt> = new_items
                .into_iter()
                .filter_map(|i| match i {
                    CBlockItem::Stmt(s) => Some(s),
                    _ => None,
                })
                .collect();
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
        CStmt::While(cond, body) => {
            CStmt::While(cond.clone(), Box::new(forward_return_value(body)))
        }
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(forward_return_value(body)), cond.clone())
        }
        CStmt::For(init, cond, upd, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            upd.clone(),
            Box::new(forward_return_value(body)),
        ),
        CStmt::Labeled(l, inner) => {
            CStmt::Labeled(l.clone(), Box::new(forward_return_value(inner)))
        }
        CStmt::Effect(l, inner) => {
            CStmt::Effect(l.clone(), Box::new(forward_return_value(inner)))
        }
        _ => stmt.clone(),
    }
}

fn forward_return_in_block_items(items: &[CBlockItem]) -> Vec<CBlockItem> {
    let mut result = items.to_vec();
    // Look for: ..., If(cond, then, else), Return(var) where If assigns var in every branch
    let mut i = 0;
    while i + 1 < result.len() {
        let var_match = match (&result[i], &result[i + 1]) {
            (
                CBlockItem::Stmt(if_stmt @ CStmt::If(_, _, Some(_))),
                CBlockItem::Stmt(CStmt::Return(Some(CExpr::Var(ret_var)))),
            ) => {
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
        CStmt::Block(items) => items
            .iter()
            .rev()
            .find_map(|i| match i {
                CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty) => Some(s),
                _ => None,
            })
            .map_or(false, |s| last_stmt_assigns(s, var)),
        CStmt::Sequence(stmts) => stmts.last().map_or(false, |s| last_stmt_assigns(s, var)),
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
            if let Some(last_stmt_idx) = new_items
                .iter()
                .rposition(|i| matches!(i, CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty)))
            {
                if let CBlockItem::Stmt(s) = &new_items[last_stmt_idx] {
                    new_items[last_stmt_idx] =
                        CBlockItem::Stmt(replace_last_assign_with_return(s, var));
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

#[cfg(test)]
mod arg_evidence_tests {
    use super::*;
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize};

    fn i32_() -> ArgEvidence {
        ArgEvidence::Int(32, Signedness::Signed)
    }
    fn i64_() -> ArgEvidence {
        ArgEvidence::Int(64, Signedness::Signed)
    }
    fn u32_() -> ArgEvidence {
        ArgEvidence::Int(32, Signedness::Unsigned)
    }
    fn f64_() -> ArgEvidence {
        ArgEvidence::Float(64)
    }
    fn ptr_char() -> ArgEvidence {
        ArgEvidence::Ptr(Some(CType::ptr(CType::char_signed())))
    }
    fn ptr_int() -> ArgEvidence {
        ArgEvidence::Ptr(Some(CType::ptr(CType::int())))
    }

    #[test]
    fn join_int_widths() {
        // int32 | int64 -> int64 (the FIXPLAN 5.5 example).
        assert_eq!(i32_().join(i64_()), i64_());
        // equal width, sign disagreement -> signed.
        assert_eq!(u32_().join(i32_()), i32_());
        assert_eq!(
            i32_().join(i64_()).to_ctype(crate::abi::DataModel::Lp64),
            Some(CType::Int(IntSize::Long, Signedness::Signed))
        );
    }

    #[test]
    fn join_int_ptr_is_compilable_top() {
        // int | ptr -> conservative top emitted as long (cast-inserter-safe).
        assert_eq!(i64_().join(ptr_char()), ArgEvidence::TopIntPtr);
        assert_eq!(
            ArgEvidence::TopIntPtr.to_ctype(crate::abi::DataModel::Lp64),
            Some(CType::long())
        );
        // float | ptr must never produce a float param; inserter cannot coerce float<->ptr, so it lands at the int/ptr top.
        assert_eq!(f64_().join(ptr_char()), ArgEvidence::TopIntPtr);
    }

    #[test]
    fn join_float_int_documented_choice() {
        // float | int -> double (documented in the ArgEvidence docs).
        assert_eq!(i64_().join(ArgEvidence::Float(32)), ArgEvidence::Float(64));
        assert_eq!(
            f64_().join(i32_()).to_ctype(crate::abi::DataModel::Lp64),
            Some(CType::Float(FloatSize::Double))
        );
    }

    #[test]
    fn join_pointers() {
        // identical pointer types stay exact; differing ones unify to void*.
        assert_eq!(ptr_char().join(ptr_char()), ptr_char());
        assert_eq!(ptr_char().join(ptr_int()), ArgEvidence::Ptr(None));
        assert_eq!(
            ArgEvidence::Ptr(None).to_ctype(crate::abi::DataModel::Lp64),
            Some(CType::ptr(CType::Void))
        );
        // differing function-pointer types poison (no implicit conversion).
        let fp = ArgEvidence::Ptr(Some(CType::ptr(CType::Function(
            Box::new(CType::Void),
            vec![],
            false,
            false,
        ))));
        assert_eq!(fp.clone().join(ptr_char()), ArgEvidence::Poison);
        assert_eq!(fp.clone().join(fp.clone()), fp);
    }

    #[test]
    fn join_bottom_and_poison() {
        // literal 0 (Bottom) constrains nothing; Poison absorbs everything.
        assert_eq!(ArgEvidence::Bottom.join(ptr_char()), ptr_char());
        assert_eq!(ArgEvidence::Bottom.join(i32_()), i32_());
        assert_eq!(
            ArgEvidence::Bottom.to_ctype(crate::abi::DataModel::Lp64),
            Some(CType::long())
        );
        assert_eq!(ArgEvidence::Poison.join(i64_()), ArgEvidence::Poison);
        assert_eq!(
            ArgEvidence::Poison.to_ctype(crate::abi::DataModel::Lp64),
            None
        );
    }

    #[test]
    fn join_is_commutative_associative_idempotent() {
        let samples = [
            ArgEvidence::Bottom,
            i32_(),
            i64_(),
            u32_(),
            ArgEvidence::Float(32),
            f64_(),
            ptr_char(),
            ptr_int(),
            ArgEvidence::Ptr(None),
            ArgEvidence::TopIntPtr,
            ArgEvidence::Poison,
        ];
        for a in &samples {
            assert_eq!(a.clone().join(a.clone()), *a, "idempotence {:?}", a);
            for b in &samples {
                assert_eq!(
                    a.clone().join(b.clone()),
                    b.clone().join(a.clone()),
                    "commutativity {:?} {:?}",
                    a,
                    b
                );
                for c in &samples {
                    let ab_c = a.clone().join(b.clone()).join(c.clone());
                    let a_bc = a.clone().join(b.clone().join(c.clone()));
                    assert_eq!(ab_c, a_bc, "associativity {:?} {:?} {:?}", a, b, c);
                }
            }
        }
    }

    #[test]
    fn join_sites_requires_arity_agreement() {
        let mut sites: HashMap<String, Vec<Vec<ArgEvidence>>> = HashMap::new();
        sites.insert("f".to_string(), vec![vec![i32_()], vec![i64_()]]);
        sites.insert("g".to_string(), vec![vec![i32_()], vec![i32_(), i32_()]]);
        sites.insert("h".to_string(), vec![vec![ArgEvidence::Poison]]);
        sites.insert("z".to_string(), vec![vec![], vec![]]);
        let joined = join_call_site_evidence(&sites, crate::abi::DataModel::Lp64);
        assert_eq!(
            joined.get("f"),
            Some(&vec![CType::Int(IntSize::Long, Signedness::Signed)])
        );
        assert!(
            !joined.contains_key("g"),
            "arity mismatch must fall back to K&R"
        );
        assert!(!joined.contains_key("h"), "poison must fall back to K&R");
        assert_eq!(
            joined.get("z"),
            Some(&vec![]),
            "consistent zero-arity -> (void)"
        );
    }
}

#[cfg(test)]
mod ptr_float_operand_tests {
    use super::*;
    use crate::decompile::passes::c_pass::types::FloatSize;

    // The printer only exposes whole statements, so render the expression as one and drop the punctuation.
    fn print_expr(e: &CExpr) -> String {
        crate::decompile::passes::c_pass::print::print_stmt(&CStmt::Expr(e.clone()))
            .trim()
            .trim_end_matches(';')
            .to_string()
    }

    fn types() -> HashMap<String, CType> {
        let mut t = HashMap::new();
        t.insert("dbl".to_string(), CType::Float(FloatSize::Double));
        t.insert("ptr".to_string(), CType::ptr(CType::Void));
        t.insert("num".to_string(), CType::long());
        t
    }

    fn var(n: &str) -> CExpr {
        CExpr::Var(n.to_string())
    }

    fn to_long(e: CExpr) -> CExpr {
        CExpr::Cast(CType::long(), Box::new(e))
    }

    // The df shape: clight hands the emitter Oeq(Etempvar(a, Tfloat), Ecast(Etempvar(b, Tint), Tlong)),
    // i.e. `double == long`, which is ordinary C. b's recovered DECLARATION is `void *`, so dropping the
    // (long) re-types the comparison into `double == void *` -- "invalid operands to binary ==", and
    // stripped df stopped relinking on it. The cast converts here, it does not rename, so it stays.
    #[test]
    fn long_cast_on_a_pointer_operand_is_not_trivial() {
        let t = types();
        let cmp = CExpr::Binary(
            BinaryOp::Eq,
            Box::new(var("dbl")),
            Box::new(to_long(var("ptr"))),
        );
        assert_eq!(
            print_expr(&strip_trivial_casts_expr(&cmp, &t)),
            "dbl == (long)ptr"
        );
    }

    // The complement: on a genuinely integral operand the same cast only re-spells the type the
    // variable already has, so stripping it is the simplification it was written to be.
    #[test]
    fn long_cast_on_an_integer_operand_stays_trivial() {
        let t = types();
        let cmp = CExpr::Binary(
            BinaryOp::Eq,
            Box::new(var("dbl")),
            Box::new(to_long(var("num"))),
        );
        assert_eq!(
            print_expr(&strip_trivial_casts_expr(&cmp, &t)),
            "dbl == num"
        );
    }

    // JA/JB and the other unsigned machine comparisons are represented by
    // explicit unsigned operand casts.  A signed declaration does not make
    // those casts cosmetic: the all-ones sentinel must compare as UINT64_MAX,
    // not as signed -1.
    #[test]
    fn unsigned_long_cast_on_signed_operands_is_not_trivial() {
        let mut t = types();
        t.insert("narrow".to_string(), CType::int());
        let cmp = CExpr::Binary(
            BinaryOp::Gt,
            Box::new(CExpr::Cast(CType::ulong(), Box::new(var("num")))),
            Box::new(CExpr::Cast(CType::ulong(), Box::new(var("narrow")))),
        );
        assert_eq!(
            print_expr(&strip_trivial_casts_expr(&cmp, &t)),
            "(unsigned long)num > (unsigned long)narrow"
        );
    }

    // One RTL value web can cover several non-overlapping lifetimes of the
    // same machine register.  Its declaration therefore need not have the
    // signedness/width selected for an individual operation.  The Clight
    // operand annotation is the operation's semantics and must become a cast
    // until the final declaration proves it redundant.
    #[test]
    fn signed_comparison_keeps_temp_annotation_across_unsigned_web_decl() {
        let int_ty = clight::ClightType::Tint(
            clight::ClightIntSize::I32,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        );
        let cmp = clight::ClightExpr::Ebinop(
            clight::ClightBinaryOp::Ogt,
            Box::new(clight::ClightExpr::Etempvar(7, int_ty.clone())),
            Box::new(clight::ClightExpr::EconstInt(128, int_ty.clone())),
            int_ty,
        );
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        let converted = convert_expr(&cmp, &mut ctx);

        let unsigned_decl = HashMap::from([("var_7".to_string(), CType::ulong())]);
        assert_eq!(
            print_expr(&strip_trivial_casts_expr(&converted, &unsigned_decl)),
            "(int)var_7 > 128"
        );

        let exact_decl = HashMap::from([("var_7".to_string(), CType::int())]);
        assert_eq!(
            print_expr(&strip_trivial_casts_expr(&converted, &exact_decl)),
            "var_7 > 128"
        );
    }

    #[test]
    fn switch_keeps_temp_width_across_wider_web_decl() {
        let int_ty = clight::ClightType::Tint(
            clight::ClightIntSize::I32,
            clight::ClightSignedness::Signed,
            clight::ClightAttr::default(),
        );
        let switch = clight::ClightStmt::Sswitch(
            clight::ClightExpr::Etempvar(7, int_ty),
            vec![
                (Some(4_294_967_165), clight::ClightStmt::Sbreak),
                (None, clight::ClightStmt::Sskip),
            ],
        );
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        let converted = convert_stmt(&switch, &mut ctx);
        let unsigned_decl = HashMap::from([("var_7".to_string(), CType::ulong())]);
        let converted = strip_trivial_casts(&converted, &unsigned_decl);

        let CStmt::Switch(scrutinee, _) = converted else {
            panic!("multi-target Clight switch was not preserved")
        };
        assert_eq!(print_expr(&scrutinee), "(int)var_7");
    }

    // A string literal is a char *, so subtracting one from an integer is the same
    // "int - ptr" the repair already integerizes for a pointer variable. Keeping the (long) on a
    // pointer operand made this shape reachable in dircolors, dir, ls and vdir, where it printed
    // `(long)var - "# Configuration file ..."` and gcc rejected the whole file.
    #[test]
    fn integer_minus_a_string_literal_is_integerized() {
        let t = types();
        let e = CExpr::Binary(
            BinaryOp::Sub,
            Box::new(to_long(var("ptr"))),
            Box::new(CExpr::StringLit(StringLiteral {
                value: "abc".to_string(),
                is_wide: false,
            })),
        );
        assert_eq!(
            print_expr(&repair_arith_expr(&e, &t)),
            "(long)ptr - (long)\"abc\""
        );
    }

    // The net: whichever layer produces the pair, no operator may print a pointer operand beside a
    // floating one. Every binary operator is checked because ctyping rejects the pair for all of
    // them (classify_add/sub/cmp have no such case; binarith rejects pointers), so one operator
    // escaping the repair is an emitted program gcc refuses.
    #[test]
    fn no_operator_emits_a_pointer_beside_a_float() {
        let t = types();
        let ops = [
            BinaryOp::Add,
            BinaryOp::Sub,
            BinaryOp::Mul,
            BinaryOp::Div,
            BinaryOp::Mod,
            BinaryOp::BitAnd,
            BinaryOp::BitOr,
            BinaryOp::BitXor,
            BinaryOp::Shl,
            BinaryOp::Shr,
            BinaryOp::Eq,
            BinaryOp::Ne,
            BinaryOp::Lt,
            BinaryOp::Gt,
            BinaryOp::Le,
            BinaryOp::Ge,
        ];
        for op in ops {
            for (l, r) in [("dbl", "ptr"), ("ptr", "dbl")] {
                let e = CExpr::Binary(op, Box::new(var(l)), Box::new(var(r)));
                let repaired = repair_arith_expr(&e, &t);
                let CExpr::Binary(_, rl, rr) = &repaired else {
                    panic!("repair dropped the binary node for {:?}", op);
                };
                assert!(
                    !(cexpr_is_pointer(rl, &t) && cexpr_is_float(rr, &t))
                        && !(cexpr_is_float(rl, &t) && cexpr_is_pointer(rr, &t)),
                    "{:?} still prints a pointer beside a float: {}",
                    op,
                    print_expr(&repaired)
                );
            }
        }
    }
}
