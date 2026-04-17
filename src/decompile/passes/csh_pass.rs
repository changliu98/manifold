

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use crate::decompile::passes::cminor_pass::*;
use crate::x86::op::Addressing;
use crate::x86::types::*;
use ascent::ascent_par;
use log::warn;


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct CshPassProgram;

    relation emit_function(Address, Symbol, Node);
    relation instr_in_function(Node, Address);


    relation func_stacksz(Address, Address, Symbol, u64);
    relation rtl_inst(Node, RTLInst);
    relation call_return_reg(Node, RTLReg);
    relation cminorsel_stmt(Node, CminorStmt);
    relation plt_entry(Address, Symbol);
    relation plt_block(Address, Symbol);
    relation block_boundaries(Address, Address, Address);
    relation msg(u64);

    relation addr_to_func_ident(Address, Ident);
    relation ident_to_symbol(Ident, Symbol);
    relation block_span(Node, Node);
    relation base_ident_to_symbol(Ident, Symbol);
    relation base_addr_usage(Node, RTLReg, i64);


    block_span(head, tail) <--
        block_boundaries(func, head, tail),
        instr_in_function(head, func),
        instr_in_function(tail, func);

    addr_to_func_ident(addr, ident) <--
        emit_function(addr, _, _),
        let ident = *addr as Ident;

    addr_to_func_ident(addr, ident) <--
        plt_entry(addr, _),
        let ident = *addr as Ident;

    addr_to_func_ident(addr, ident) <--
        plt_block(addr, _),
        let ident = *addr as Ident;

    ident_to_symbol(ident, *name) <-- base_ident_to_symbol(ident, name);

    base_ident_to_symbol(ident, clean_name) <--
        addr_to_func_ident(addr, ident),
        plt_entry(addr, sym),
        let clean_name = strip_version_suffix(sym);

    base_ident_to_symbol(ident, clean_name) <--
        addr_to_func_ident(addr, ident),
        plt_block(addr, sym),
        let clean_name = strip_version_suffix(sym);

    ident_to_symbol(ident, name) <--
        addr_to_func_ident(addr, ident),
        func_stacksz(start, end, name, _),
        if addr >= start && addr < end;

    base_addr_usage(node, *reg, 0) <--
        cminorsel_stmt(node, ?CminorStmt::Sassign(_, expr)),
        if let CminorExpr::Eload(_, addr, args) = expr,
        if !matches!(addr, Addressing::Aglobal(_, _)),
        if let Some(reg) = args.first();

    base_addr_usage(node, *reg, 0) <--
        cminorsel_stmt(node, ?CminorStmt::Sstore(_, addr, args, _)),
        if !matches!(addr, Addressing::Aglobal(_, _)),
        if let Some(reg) = args.first();
}

pub struct CshPass;

impl IRPass for CshPass {
    fn name(&self) -> &'static str { "csh" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, CshPassProgram);
    }

    declare_io_from!(CshPassProgram);
}


pub fn make_field_ident(offset: i64, _chunk: MemoryChunk) -> Ident {
    offset.max(0) as Ident
}

pub fn field_ident_to_name(ident: Ident) -> String {
    format!("ofs_{}", ident)
}

pub fn is_function_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tfunction(_, _, _))
}

pub fn is_function_pointer_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tpointer(inner, _) if is_function_type(inner.as_ref()))
}

pub fn is_pointer_like_type(ty: &ClightType) -> bool {
    matches!(
        ty,
        ClightType::Tpointer(_, _) | ClightType::Tarray(_, _, _) | ClightType::Tfunction(_, _, _)
    )
}

pub fn is_pointer_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tpointer(_, _))
}

pub fn is_integral_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tint(_, _, _) | ClightType::Tlong(_, _))
}

pub fn is_basic_type(ty: &ClightType) -> bool {
    matches!(
        ty,
        ClightType::Tint(_, _, _)
            | ClightType::Tlong(_, _)
            | ClightType::Tfloat(_, _)
            | ClightType::Tvoid
    )
}

pub fn default_attr() -> ClightAttr {
    ClightAttr::default()
}

pub fn default_int_type() -> ClightType {
    ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, default_attr())
}

pub fn default_uint_type() -> ClightType {
    ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, default_attr())
}

pub fn default_long_type() -> ClightType {
    ClightType::Tlong(ClightSignedness::Signed, default_attr())
}

pub fn default_ulong_type() -> ClightType {
    ClightType::Tlong(ClightSignedness::Unsigned, default_attr())
}

pub fn default_single_type() -> ClightType {
    ClightType::Tfloat(ClightFloatSize::F32, default_attr())
}

pub fn default_float_type() -> ClightType {
    ClightType::Tfloat(ClightFloatSize::F64, default_attr())
}

pub fn default_bool_type() -> ClightType {
    ClightType::Tint(
        ClightIntSize::IBool,
        ClightSignedness::Unsigned,
        default_attr(),
    )
}

pub fn default_expr_for_type(ty: &ClightType) -> ClightExpr {
    match ty {
        ClightType::Tint(_, _, _) => ClightExpr::EconstInt(0, ty.clone()),
        ClightType::Tlong(_, _) => ClightExpr::EconstLong(0, ty.clone()),
        ClightType::Tfloat(ClightFloatSize::F64, _) => {
            ClightExpr::EconstFloat(ClightFloat64(0.0), ty.clone())
        }
        ClightType::Tfloat(ClightFloatSize::F32, _) => {
            ClightExpr::EconstSingle(ClightFloat32(0.0), ty.clone())
        }
        ClightType::Tpointer(_, _) | ClightType::Tarray(_, _, _) => {
            ClightExpr::EconstInt(0, ty.clone())
        }
        _ => ClightExpr::EconstInt(0, default_int_type()),
    }
}


pub fn simplify_type(ty: ClightType) -> ClightType {
    match ty {
        ClightType::Tpointer(inner, attr) => {
            if let ClightType::Tpointer(ref inner2, _) = *inner {
                if is_basic_type(inner2) {
                    return ClightType::Tpointer(inner2.clone(), attr);
                }
            }
            ClightType::Tpointer(inner, attr)
        }
        _ => ty,
    }
}

pub fn pointer_to(inner: ClightType) -> ClightType {
    let ptr = ClightType::Tpointer(Arc::new(inner), default_attr());
    simplify_type(ptr)
}


pub fn clight_type_from_chunk(chunk: &MemoryChunk) -> ClightType {
    match chunk {
        MemoryChunk::MBool => default_bool_type(),
        MemoryChunk::MInt8Signed => {
            ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, default_attr())
        }
        MemoryChunk::MInt8Unsigned => ClightType::Tint(
            ClightIntSize::I8,
            ClightSignedness::Unsigned,
            default_attr(),
        ),
        MemoryChunk::MInt16Signed => {
            ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, default_attr())
        }
        MemoryChunk::MInt16Unsigned => ClightType::Tint(
            ClightIntSize::I16,
            ClightSignedness::Unsigned,
            default_attr(),
        ),
        MemoryChunk::MInt32 | MemoryChunk::MAny32 | MemoryChunk::Unknown => default_int_type(),
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => default_long_type(),
        MemoryChunk::MFloat32 => default_single_type(),
        MemoryChunk::MFloat64 => default_float_type(),
    }
}

pub fn clight_type_from_xtype(xtype: &XType) -> ClightType {
    match xtype {
        XType::Xbool => default_bool_type(),
        XType::Xint8signed => {
            ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, default_attr())
        }
        XType::Xint8unsigned => ClightType::Tint(
            ClightIntSize::I8,
            ClightSignedness::Unsigned,
            default_attr(),
        ),
        XType::Xint16signed => {
            ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, default_attr())
        }
        XType::Xint16unsigned => ClightType::Tint(
            ClightIntSize::I16,
            ClightSignedness::Unsigned,
            default_attr(),
        ),
        XType::Xint | XType::Xany32 => default_int_type(),
        XType::Xintunsigned => ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Unsigned,
            default_attr(),
        ),
        XType::Xfloat => default_float_type(),
        XType::Xlong | XType::Xany64 => default_long_type(),
        XType::Xlongunsigned => ClightType::Tlong(ClightSignedness::Unsigned, default_attr()),
        XType::Xsingle => default_single_type(),
        XType::Xptr => pointer_to(ClightType::Tvoid),
        XType::Xintptr => pointer_to(default_int_type()),
        XType::Xfloatptr => pointer_to(default_float_type()),
        XType::Xsingleptr => pointer_to(default_single_type()),
        XType::Xfuncptr => pointer_to(ClightType::Tfunction(
            Arc::new(Vec::new()),
            Arc::new(ClightType::Tvoid),
            CallConv::default(),
        )),
        XType::Xcharptr => pointer_to(ClightType::Tint(
            ClightIntSize::I8,
            ClightSignedness::Signed,
            default_attr(),
        )),
        XType::Xcharptrptr => pointer_to(pointer_to(ClightType::Tint(
            ClightIntSize::I8,
            ClightSignedness::Signed,
            default_attr(),
        ))),
        XType::Xvoid => ClightType::Tvoid,
        XType::XstructPtr(struct_id) => ClightType::Tpointer(
            Arc::new(ClightType::Tstruct(*struct_id, default_attr())),
            default_attr(),
        ),
    }
}

pub fn clight_function_pointer_type(sig: &Signature) -> ClightType {
    let arg_types: Vec<ClightType> = sig.sig_args.iter().map(clight_type_from_xtype).collect();
    let ret_type = clight_type_from_xtype(&sig.sig_res);
    pointer_to(ClightType::Tfunction(Arc::new(arg_types), Arc::new(ret_type), sig.sig_cc))
}

pub fn default_function_signature() -> Signature {
    Signature {
        sig_args: Arc::new(Vec::new()),
        sig_res: XType::Xint,
        sig_cc: CallConv::default(),
    }
}

pub fn resolve_signature(sig_opt: &Option<Signature>) -> Signature {
    sig_opt.clone().unwrap_or_else(default_function_signature)
}


pub fn clight_cast_supported(from: &ClightType, to: &ClightType) -> bool {
    use ClightFloatSize::*;
    use ClightType::*;
    match (to, from) {
        (Tvoid, _) => true,
        (Tint(_, _, _), Tint(_, _, _)) => true,
        (Tint(_, _, _), Tlong(_, _)) => true,
        (Tint(_, _, _), Tfloat(F64, _)) => true,
        (Tint(_, _, _), Tfloat(F32, _)) => true,
        (Tint(_, _, _), src) if is_pointer_like_type(src) => true,
        (Tlong(_, _), Tlong(_, _)) => true,
        (Tlong(_, _), Tint(_, _, _)) => true,
        (Tlong(_, _), Tfloat(F64, _)) => true,
        (Tlong(_, _), Tfloat(F32, _)) => true,
        (Tlong(_, _), src) if is_pointer_like_type(src) => true,
        (Tfloat(F64, _), Tint(_, _, _)) => true,
        (Tfloat(F32, _), Tint(_, _, _)) => true,
        (Tfloat(F64, _), Tlong(_, _)) => true,
        (Tfloat(F32, _), Tlong(_, _)) => true,
        (Tfloat(F64, _), Tfloat(F64, _)) => true,
        (Tfloat(F32, _), Tfloat(F32, _)) => true,
        (Tfloat(F64, _), Tfloat(F32, _)) => true,
        (Tfloat(F32, _), Tfloat(F64, _)) => true,
        (Tpointer(_, _), Tint(_, _, _)) => true,
        (Tpointer(_, _), Tlong(_, _)) => true,
        (Tpointer(_, _), src) if is_pointer_like_type(src) => true,
        (Tstruct(_, _), Tstruct(_, _)) => true,
        (Tunion(_, _), Tunion(_, _)) => true,
        _ => false,
    }
}

pub fn merge_clight_types(existing: &ClightType, candidate: &ClightType) -> ClightType {
    use ClightType::*;

    /// Specificity rank for ClightType (lower = more specific = wins in merge), aligned with xtype_priority ordering from type_pass.
    fn specificity(ty: &ClightType) -> u8 {
        use ClightType::*;
        match ty {
            Tpointer(_, _) => 0,
            Tstruct(_, _) => 1,
            Tunion(_, _) => 2,
            Tarray(_, _, _) => 3,
            Tfunction(_, _, _) => 4,
            Tfloat(ClightFloatSize::F64, _) => 5,
            Tfloat(ClightFloatSize::F32, _) => 6,
            Tint(ClightIntSize::I8, ClightSignedness::Signed, _) => 7,
            Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _) => 8,
            Tint(ClightIntSize::I16, ClightSignedness::Signed, _) => 9,
            Tint(ClightIntSize::I16, ClightSignedness::Unsigned, _) => 10,
            Tint(ClightIntSize::IBool, _, _) => 11,
            Tlong(ClightSignedness::Unsigned, _) => 12,
            Tlong(ClightSignedness::Signed, _) => 13,
            Tint(ClightIntSize::I32, ClightSignedness::Unsigned, _) => 14,
            Tint(ClightIntSize::I32, ClightSignedness::Signed, _) => 15,
            Tvoid => 16,
        }
    }

    if existing == candidate {
        return existing.clone();
    }

    // Pointer always wins
    match (existing, candidate) {
        (Tpointer(_, _), _) => return existing.clone(),
        (_, Tpointer(_, _)) => return candidate.clone(),
        _ => {}
    }

    match (existing, candidate) {
        (Tint(s1, sg1, _), Tint(s2, _sg2, _)) => {
            if s1 == s2 {
                // Same size: signed wins
                if *sg1 == ClightSignedness::Signed {
                    return existing.clone();
                } else {
                    return candidate.clone();
                }
            }
            // Different sizes: more specific (smaller) wins
            let e_spec = specificity(existing);
            let c_spec = specificity(candidate);
            if e_spec <= c_spec {
                return existing.clone();
            } else {
                return candidate.clone();
            }
        }

        (Tlong(_, _), Tint(_, _, _)) => {
            return candidate.clone();
        }
        (Tint(_, _, _), Tlong(_, _)) => {
            return existing.clone();
        }

        (Tfloat(ClightFloatSize::F64, _), Tfloat(ClightFloatSize::F32, _)) => {
            return existing.clone();
        }
        (Tfloat(ClightFloatSize::F32, _), Tfloat(ClightFloatSize::F64, _)) => {
            return candidate.clone();
        }

        (Tfloat(_, _), Tint(_, _, _)) | (Tfloat(_, _), Tlong(_, _)) => {
            return existing.clone();
        }
        (Tint(_, _, _), Tfloat(_, _)) | (Tlong(_, _), Tfloat(_, _)) => {
            return candidate.clone();
        }

        _ => {}
    }

    // Fallback: more specific (lower specificity rank) wins for deterministic ordering
    let e_spec = specificity(existing);
    let c_spec = specificity(candidate);
    if e_spec <= c_spec {
        existing.clone()
    } else {
        candidate.clone()
    }
}

pub fn clight_expr_type(expr: &ClightExpr) -> ClightType {
    match expr {
        ClightExpr::EconstInt(_, ty)
        | ClightExpr::EconstFloat(_, ty)
        | ClightExpr::EconstSingle(_, ty)
        | ClightExpr::EconstLong(_, ty)
        | ClightExpr::Evar(_, ty)
        | ClightExpr::EvarSymbol(_, ty)
        | ClightExpr::Etempvar(_, ty)
        | ClightExpr::Ederef(_, ty)
        | ClightExpr::Eaddrof(_, ty)
        | ClightExpr::Eunop(_, _, ty)
        | ClightExpr::Ebinop(_, _, _, ty)
        | ClightExpr::Ecast(_, ty)
        | ClightExpr::Efield(_, _, ty)
        | ClightExpr::Esizeof(_, ty)
        | ClightExpr::Ealignof(_, ty)
        | ClightExpr::Econdition(_, _, _, ty) => ty.clone(),
    }
}

pub fn clight_unop_from_cminor(op: &CminorUnop) -> Option<ClightUnaryOp> {
    match op {
        CminorUnop::Onegint | CminorUnop::Onegl | CminorUnop::Onegf | CminorUnop::Onegfs => {
            Some(ClightUnaryOp::Oneg)
        }
        CminorUnop::Onotint | CminorUnop::Onotl => Some(ClightUnaryOp::Onotint),
        CminorUnop::Oabsf | CminorUnop::Oabsfs => Some(ClightUnaryOp::Oabsfloat),
        _ => None,
    }
}


pub fn types_equal_ignoring_attr(t1: &ClightType, t2: &ClightType) -> bool {
    match (t1, t2) {
        (ClightType::Tint(s1, sn1, _), ClightType::Tint(s2, sn2, _)) => s1 == s2 && sn1 == sn2,
        (ClightType::Tlong(sn1, _), ClightType::Tlong(sn2, _)) => sn1 == sn2,
        (ClightType::Tfloat(s1, _), ClightType::Tfloat(s2, _)) => s1 == s2,
        (ClightType::Tpointer(i1, _), ClightType::Tpointer(i2, _)) => {
            types_equal_ignoring_attr(i1, i2)
        }
        (ClightType::Tarray(i1, l1, _), ClightType::Tarray(i2, l2, _)) => {
            l1 == l2 && types_equal_ignoring_attr(i1, i2)
        }
        (ClightType::Tfunction(a1, r1, c1), ClightType::Tfunction(a2, r2, c2)) => {
            c1 == c2
                && a1.len() == a2.len()
                && types_equal_ignoring_attr(r1, r2)
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| types_equal_ignoring_attr(x, y))
        }
        (ClightType::Tstruct(id1, _), ClightType::Tstruct(id2, _)) => id1 == id2,
        (ClightType::Tunion(id1, _), ClightType::Tunion(id2, _)) => id1 == id2,
        (ClightType::Tvoid, ClightType::Tvoid) => true,
        _ => false,
    }
}

pub fn cast_expr_to_type(expr: ClightExpr, target_ty: ClightType) -> ClightExpr {
    let expr_ty = clight_expr_type(&expr);

    if expr_ty == target_ty || types_equal_ignoring_attr(&expr_ty, &target_ty) {
        return expr;
    }

    // Narrowing integer cast check (inlined)
    if matches!(expr_ty, ClightType::Tlong(_, _)) && matches!(target_ty, ClightType::Tint(_, _, _)) {
        return expr;
    }
    if let (
        ClightType::Tint(ClightIntSize::I32, _, _),
        ClightType::Tint(to_size, _, _),
    ) = (&expr_ty, &target_ty)
    {
        if matches!(to_size, ClightIntSize::I8 | ClightIntSize::I16) {
            return expr;
        }
    }

    if is_pointer_type(&target_ty) {
        if matches!(
            expr,
            ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)
        ) {
            return expr;
        }
    }

    match &expr {
        ClightExpr::EconstInt(v, _) => {
            if let ClightType::Tint(_, _, _) = &target_ty {
                return ClightExpr::EconstInt(*v, target_ty);
            } else if let ClightType::Tlong(_, _) = &target_ty {
                return ClightExpr::EconstLong(*v as i64, target_ty);
            }
        }
        ClightExpr::EconstLong(v, _) => {
            if let ClightType::Tlong(_, _) = &target_ty {
                return ClightExpr::EconstLong(*v, target_ty);
            } else if let ClightType::Tint(_, _, _) = &target_ty {
                return ClightExpr::EconstInt(*v as i32, target_ty);
            }
        }
        _ => {}
    }

    if is_function_pointer_type(&target_ty) {
        warn!(
            "Skipping invalid cast to function pointer type from {:?}",
            expr_ty
        );
        expr
    } else if is_function_pointer_type(&expr_ty) {
        warn!(
            "Skipping invalid cast from function pointer type to {:?}",
            target_ty
        );
        expr
    } else if is_function_type(&target_ty) || is_function_type(&expr_ty) {
        warn!(
            "Skipping cast involving function type: from {:?} to {:?}",
            expr_ty,
            target_ty
        );
        expr
    } else if !clight_cast_supported(&expr_ty, &target_ty) {
        warn!(
            "Unsupported cast from {:?} to {:?} - leaving expression unchanged",
            expr_ty,
            target_ty
        );
        expr
    } else {
        ClightExpr::Ecast(Box::new(expr), target_ty)
    }
}

pub fn rewrite_expr_as_pointer(expr: ClightExpr, target_ptr_ty: ClightType) -> ClightExpr {
    if !is_pointer_type(&target_ptr_ty) {
        return expr;
    }

    match expr {
        ClightExpr::Etempvar(_, ref old_ty) | ClightExpr::Evar(_, ref old_ty) => {
            if old_ty == &target_ptr_ty {
                expr
            } else {
                cast_expr_to_type(expr, target_ptr_ty)
            }
        }

        ClightExpr::Ebinop(op, lhs, rhs, _old_ty)
            if matches!(op, ClightBinaryOp::Oadd | ClightBinaryOp::Osub) =>
        {
            let lhs_ty = clight_expr_type(&lhs);
            let rhs_ty = clight_expr_type(&rhs);

            if is_integral_type(&rhs_ty) && !is_pointer_type(&lhs_ty) {
                let new_lhs = rewrite_expr_as_pointer(*lhs, target_ptr_ty.clone());
                ClightExpr::Ebinop(op, Box::new(new_lhs), rhs, target_ptr_ty)
            } else if is_integral_type(&lhs_ty) && !is_pointer_type(&rhs_ty) {
                let new_rhs = rewrite_expr_as_pointer(*rhs, target_ptr_ty.clone());
                ClightExpr::Ebinop(op, lhs, Box::new(new_rhs), target_ptr_ty)
            } else {
                ClightExpr::Ebinop(op, lhs, rhs, target_ptr_ty)
            }
        }

        ClightExpr::Ecast(inner, _old_ty) => {
            let new_inner = rewrite_expr_as_pointer(*inner, target_ptr_ty.clone());
            ClightExpr::Ecast(Box::new(new_inner), target_ptr_ty)
        }

        _ => cast_expr_to_type(expr, target_ptr_ty),
    }
}

pub fn rewrite_deref_for_pointer_dest(expr: ClightExpr, target_ptr_ty: ClightType) -> ClightExpr {
    match &expr {
        ClightExpr::Ederef(_, elem_ty) => {
            if elem_ty == &target_ptr_ty {
                return expr;
            }
            if is_pointer_type(elem_ty) && is_pointer_type(&target_ptr_ty) {
                return expr;
            }
            cast_expr_to_type(expr, target_ptr_ty)
        }
        _ => {
            let expr_ty = clight_expr_type(&expr);
            if is_pointer_type(&expr_ty) && is_pointer_type(&target_ptr_ty) {
                return expr;
            }
            cast_expr_to_type(expr, target_ptr_ty)
        }
    }
}

pub fn normalize_const_expr(expr: ClightExpr) -> ClightExpr {
    match expr {
        ClightExpr::EconstLong(v, ty) => {
            if !matches!(ty, ClightType::Tlong(_, _)) {
                warn!(
                    "normalize_const_expr: EconstLong had non-long type {:?}, fixing to Tlong",
                    ty
                );
                ClightExpr::EconstLong(v, default_long_type())
            } else {
                ClightExpr::EconstLong(v, ty)
            }
        }
        ClightExpr::EconstInt(v, ty) => {
            if matches!(ty, ClightType::Tlong(_, _)) {
                warn!(
                    "normalize_const_expr: EconstInt had Tlong type, fixing to Tint"
                );
                ClightExpr::EconstInt(v, default_int_type())
            } else {
                ClightExpr::EconstInt(v, ty)
            }
        }
        other => other,
    }
}


pub fn ident_from_reg(reg: RTLReg) -> Ident {
    match usize::try_from(reg) {
        Ok(v) => v,
        Err(_) => crate::util::DEFAULT_VAR as Ident,
    }
}

pub fn ident_from_node(node: Node) -> Ident {
    usize::try_from(node).unwrap_or(usize::MAX)
}

pub fn expr_has_bad_binop(expr: &ClightExpr) -> bool {
    match expr {
        ClightExpr::Ebinop(op, lhs, rhs, _result_ty) => {
            let lhs_ty = clight_expr_type(lhs);
            let rhs_ty = clight_expr_type(rhs);

            let calls_make_binarith_strict = matches!(
                op,
                ClightBinaryOp::Omul
                    | ClightBinaryOp::Odiv
                    | ClightBinaryOp::Omod
                    | ClightBinaryOp::Oand
                    | ClightBinaryOp::Oor
                    | ClightBinaryOp::Oxor
                    | ClightBinaryOp::Oshl
                    | ClightBinaryOp::Oshr
                    | ClightBinaryOp::Oeq
                    | ClightBinaryOp::One
                    | ClightBinaryOp::Olt
                    | ClightBinaryOp::Ogt
                    | ClightBinaryOp::Ole
                    | ClightBinaryOp::Oge
            );

            if calls_make_binarith_strict {
                let lhs_is_int = matches!(lhs_ty, ClightType::Tint(_, _, _));
                let lhs_is_ptr = is_pointer_type(&lhs_ty);
                let rhs_is_int = matches!(rhs_ty, ClightType::Tint(_, _, _));
                let rhs_is_ptr = is_pointer_type(&rhs_ty);

                let has_int_ptr_mismatch = (lhs_is_int && rhs_is_ptr)
                    || (lhs_is_ptr && rhs_is_int);

                if has_int_ptr_mismatch {
                    return true;
                }
            }

            expr_has_bad_binop(lhs) || expr_has_bad_binop(rhs)
        }
        ClightExpr::Ecast(inner, _) => expr_has_bad_binop(inner),
        ClightExpr::Eunop(_, inner, _) => expr_has_bad_binop(inner),
        ClightExpr::Ederef(inner, _) => expr_has_bad_binop(inner),
        ClightExpr::Eaddrof(inner, _) => expr_has_bad_binop(inner),
        ClightExpr::Efield(inner, _, _) => expr_has_bad_binop(inner),
        _ => false,
    }
}

pub fn make_binarith_check(lhs_ty: &ClightType, rhs_ty: &ClightType) -> bool {
    use ClightType::*;

    match (lhs_ty, rhs_ty) {
        (Tint(_, _, _), rhs) if is_pointer_like_type(rhs) => false,
        (Tlong(_, _), rhs) if is_pointer_like_type(rhs) => true,
        (lhs, Tint(_, _, _)) if is_pointer_like_type(lhs) => true,
        (lhs, Tlong(_, _)) if is_pointer_like_type(lhs) => true,
        (lhs, rhs) if is_pointer_like_type(lhs) && is_pointer_like_type(rhs) => true,
        (Tint(_, _, _), Tint(_, _, _)) => true,
        (Tlong(_, _), Tlong(_, _)) => true,
        (Tlong(_, _), Tint(_, _, _)) => true,
        (Tint(_, _, _), Tlong(_, _)) => true,
        (Tfloat(_, _), Tfloat(_, _)) => true,
        (Tfloat(_, _), Tint(_, _, _)) => true,
        (Tfloat(_, _), Tlong(_, _)) => true,
        (Tint(_, _, _), Tfloat(_, _)) => true,
        (Tlong(_, _), Tfloat(_, _)) => true,
        (Tvoid, _) | (_, Tvoid) => true,
        (Tstruct(id1, _), Tstruct(id2, _)) if id1 == id2 => true,
        (Tunion(id1, _), Tunion(id2, _)) if id1 == id2 => true,
        _ => false,
    }
}


