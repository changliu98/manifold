//! Finite C word-view candidates for machine-defined frame read results.
//!
//! Datalog proposes an unsigned 32-bit view; the ordinary selection-owned
//! value/definedness checker decides whether it preserves the decoded result.
//! Original candidates and structural-world membership remain available. This
//! is neither a post-emission cast repair nor an assertion that every proposal
//! is correct. Integer casts/read effects are the only grammar terminals here.

use crate::decompile::passes::clight_select::query::FunctionData;
use crate::x86::types::*;
use ascent::ascent;
use ascent::lattice::set::Set;
use std::collections::BTreeSet;

fn integer(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tint(_, _, a) | ClightType::Tlong(_, a) if !a.attr_volatile)
}

fn read_cast_chain(expr: &ClightExpr, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }
    match expr {
        ClightExpr::Ederef(_, ty) | ClightExpr::Efield(_, _, ty) => integer(ty),
        ClightExpr::Ecast(inner, ty) if integer(ty) => read_cast_chain(inner, fuel - 1),
        _ => false,
    }
}

fn word_view(stmt: &ClightStmt, destination: RTLReg, fuel: usize) -> Option<ClightStmt> {
    if fuel == 0 {
        return None;
    }
    match stmt {
        ClightStmt::Sset(id, rhs) if *id as RTLReg == destination && read_cast_chain(rhs, fuel) => {
            if matches!(
                rhs,
                ClightExpr::Ecast(
                    _,
                    ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, _)
                )
            ) {
                return None;
            }
            Some(ClightStmt::Sset(
                *id,
                ClightExpr::Ecast(
                    Box::new(rhs.clone()),
                    ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Unsigned,
                        ClightAttr::default(),
                    ),
                ),
            ))
        }
        ClightStmt::Slabel(label, inner) => Some(ClightStmt::Slabel(
            *label,
            Box::new(word_view(inner, destination, fuel - 1)?),
        )),
        ClightStmt::Ssequence(items) if items.len() == 1 => {
            Some(ClightStmt::Ssequence(vec![word_view(
                &items[0],
                destination,
                fuel - 1,
            )?]))
        }
        _ => None,
    }
}

fn input_view_expr(expr: &ClightExpr, words: &Set<RTLReg>, fuel: usize) -> Option<ClightExpr> {
    if fuel == 0 {
        return None;
    }
    let unsigned = || {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Unsigned,
            ClightAttr::default(),
        )
    };
    Some(match expr {
        ClightExpr::Etempvar(id, _) if words.contains(&(*id as RTLReg)) => {
            ClightExpr::Ecast(Box::new(expr.clone()), unsigned())
        }
        ClightExpr::Etempvar(..) | ClightExpr::EconstInt(..) | ClightExpr::EconstLong(..) => {
            expr.clone()
        }
        ClightExpr::Ecast(
            inner,
            ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, _),
        ) if matches!(inner.as_ref(), ClightExpr::Etempvar(id, _) if words.contains(&(*id as RTLReg))) => {
            expr.clone()
        }
        ClightExpr::Ecast(inner, ty) => ClightExpr::Ecast(
            Box::new(input_view_expr(inner, words, fuel - 1)?),
            ty.clone(),
        ),
        ClightExpr::Eunop(op, inner, ty) => ClightExpr::Eunop(
            *op,
            Box::new(input_view_expr(inner, words, fuel - 1)?),
            ty.clone(),
        ),
        ClightExpr::Ebinop(op, left, right, ty) => ClightExpr::Ebinop(
            *op,
            Box::new(input_view_expr(left, words, fuel - 1)?),
            Box::new(input_view_expr(right, words, fuel - 1)?),
            ty.clone(),
        ),
        _ => return None, // No rewriting of memory addresses, calls, or compound effects.
    })
}

fn input_view(stmt: &ClightStmt, words: &Set<RTLReg>, fuel: usize) -> Option<ClightStmt> {
    if fuel == 0 {
        return None;
    }
    let result = match stmt {
        ClightStmt::Sset(id, rhs) => ClightStmt::Sset(*id, input_view_expr(rhs, words, fuel - 1)?),
        ClightStmt::Slabel(label, inner) => {
            ClightStmt::Slabel(*label, Box::new(input_view(inner, words, fuel - 1)?))
        }
        ClightStmt::Ssequence(items) if items.len() == 1 => {
            ClightStmt::Ssequence(vec![input_view(&items[0], words, fuel - 1)?])
        }
        _ => return None,
    };
    (result != *stmt).then_some(result)
}

ascent! {
    struct WordViews;
    relation source(Node, usize, ClightStmt);
    relation word32(Node, RTLReg);
    relation input_words(Node, Set<RTLReg>);
    relation candidate(Node, usize, ClightStmt);
    candidate(*node, *parent, view) <--
        source(node, parent, stmt), word32(node, destination),
        if let Some(view) = word_view(stmt, *destination, 96);
    candidate(*node, *parent, view) <-- source(node, parent, stmt), input_words(node, words),
        if let Some(view) = input_view(stmt, words, 96);
}

pub(crate) fn extend_candidates(function: &mut FunctionData) {
    if !function.ptr64 {
        return;
    }
    let mut grammar = WordViews::default();
    for read in &function.storage_reads {
        if read.write_bits != Some(32)
            || !matches!(
                read.chunk,
                MemoryChunk::MInt8Signed
                    | MemoryChunk::MInt8Unsigned
                    | MemoryChunk::MInt16Signed
                    | MemoryChunk::MInt16Unsigned
                    | MemoryChunk::MInt32
                    | MemoryChunk::MAny32
            )
        {
            continue;
        }
        grammar.word32.push((read.node, read.destination));
        for (index, stmt) in function
            .node_statements
            .get(&read.node)
            .into_iter()
            .flatten()
            .enumerate()
        {
            grammar.source.push((read.node, index, stmt.clone()));
        }
    }
    for (&node, words) in &function.word_inputs {
        grammar.input_words.push((node, Set(words.clone())));
        for (index, stmt) in function
            .node_statements
            .get(&node)
            .into_iter()
            .flatten()
            .enumerate()
        {
            grammar.source.push((node, index, stmt.clone()));
        }
    }
    grammar.run();
    crate::decompile::passes::clight_select::syntax::candidates::inherit(function, grammar.candidate.into_iter().collect());
}
