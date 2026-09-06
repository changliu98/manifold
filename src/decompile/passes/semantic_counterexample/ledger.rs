//! Persistent, stage-specific obligations for constructed representations.
//!
//! A record certifies a named property under its storage model; it never means
//! that the complete function or callee summary has been proved equivalent.
//! Keeping immutable events distinguishes discovery, refutation, construction,
//! successful epoch materialization and downstream discharge.

use crate::decompile::elevator::DecompileDB;
use crate::x86::types::{Address, Node};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectId {
    pub function: Address,
    pub base: i64,
}

/// A declaration can back several machine views after safe coalescing. This
/// metadata is independent of its printable name and survives AST rewrites.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ObjectView {
    pub object: ObjectId,
    pub offset: usize,
    pub extent: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stage {
    Anchor,
    Representation,
    Rtl,
    Projection,
    Selection,
    Emission,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Outcome {
    Pending,
    Refuted,
    Proven,
    Unsupported,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Event {
    pub object: ObjectId,
    pub anchor: Node,
    pub call: Node,
    pub stage: Stage,
    pub outcome: Outcome,
    pub extent: i64,
    pub reason: &'static str,
}

impl Event {
    pub(super) fn new(function: Address, anchor: Node, base: i64) -> Self {
        Self {
            object: ObjectId { function, base },
            anchor,
            call: 0,
            stage: Stage::Anchor,
            outcome: Outcome::Pending,
            extent: 0,
            reason: "machine address requires a storage interpretation",
        }
    }
    pub(crate) fn at(&self, stage: Stage, outcome: Outcome, reason: &'static str) -> Self {
        Self {
            stage,
            outcome,
            reason,
            ..self.clone()
        }
    }
}

pub(crate) fn append(db: &mut DecompileDB, events: impl IntoIterator<Item = Event>) {
    for event in events {
        if !db
            .rel_iter::<Event>("semantic_storage_obligation")
            .any(|existing| existing == &event)
        {
            db.rel_push("semantic_storage_obligation", event);
        }
    }
}

/// Downstream consumers inherit only committed representation contracts. A
/// refuted/unknown/discarded proposal cannot authorize a source transformation.
pub(crate) fn committed(db: &DecompileDB) -> Vec<Event> {
    let mut objects = std::collections::BTreeMap::new();
    for event in db
        .rel_iter::<Event>("semantic_storage_obligation")
        .filter(|e| e.stage == Stage::Rtl && e.outcome == Outcome::Proven)
    {
        objects
            .entry(event.object)
            .and_modify(|old: &mut Event| {
                if (event.anchor, event.call) < (old.anchor, old.call) {
                    *old = event.clone();
                }
            })
            .or_insert_with(|| event.clone());
    }
    objects.into_values().collect()
}

/// Selection may move a store into a structured sequence but may not erase
/// its exact-width obligation. Use selected-candidate provenance, not source
/// location ordering or equality with a statement at another instruction.
pub(crate) fn check_selection(db: &mut DecompileDB) {
    let contracts = committed(db);
    let mut events = Vec::new();
    for event in contracts {
        let projected = db
            .rel_iter::<Event>("semantic_storage_obligation")
            .any(|e| {
                e.object == event.object
                    && e.stage == Stage::Projection
                    && e.outcome == Outcome::Proven
            });
        let selected = db
            .clight_selected_functions
            .iter()
            .find(|f| f.address == event.object.function);
        let root = db
            .rel_iter::<(Address, i64, u64)>("slot_escaped_canonical")
            .find(|r| (r.0, r.1) == (event.object.function, event.object.base))
            .map(|r| r.2);
        let exact = selected.is_some_and(|function| {
            db.rel_iter::<(Address, Node, u64, i64, usize)>("semantic_storage_projection")
                .filter(|r| r.0 == event.object.function && Some(r.2) == root)
                .all(|r| {
                    function.selected_write_bytes.get(&r.1).copied() == Some(r.4)
                        && db
                            .rel_iter::<(Address, Node, ObjectId, i64, usize)>(
                                "semantic_storage_selected_target",
                            )
                            .any(|target| {
                                (target.0, target.1, target.2, target.3, target.4)
                                    == (r.0, r.1, event.object, r.3, r.4)
                            })
                })
        });
        events.push(event.at(
            Stage::Selection,
            if projected && exact {
                Outcome::Proven
            } else {
                Outcome::Unknown
            },
            if projected && exact {
                "selected Clight targets retain machine object, byte offset and write width"
            } else {
                "selected write coverage is not established"
            },
        ));
    }
    append(db, events);
}

fn covers(variable: &crate::decompile::passes::c_pass::types::VarDecl, view: &ObjectView) -> bool {
    use crate::decompile::passes::c_pass::types::{CType, IntSize};
    matches!(&variable.ty, CType::Array(element, Some(size))
        if matches!(element.as_ref(), CType::Int(IntSize::Char, _))
            && view.offset.checked_add(view.extent).is_some_and(|end| end <= *size))
        && variable.init.is_none()
}

pub(crate) fn check_emission(db: &mut DecompileDB) {
    use crate::decompile::passes::c_pass::types::TopLevelDecl;
    let contracts = committed(db);
    if contracts.is_empty() {
        return;
    }
    let mut views = Vec::new();
    if let Some(tu) = db.cast_optimized_translation_unit.as_ref() {
        for declaration in &tu.decls {
            if let TopLevelDecl::FuncDef(function) = declaration {
                for variable in &function.local_vars {
                    for view in &variable.storage_views {
                        views.push((view.object, covers(variable, view)));
                    }
                }
            }
        }
    }
    let events: Vec<_> = contracts
        .into_iter()
        .map(|event| {
            let declaration = views
                .iter()
                .any(|&(object, valid)| object == event.object && valid);
            event.at(
                Stage::Emission,
                if declaration {
                    Outcome::Proven
                } else {
                    Outcome::Unknown
                },
                if declaration {
                    "emitted byte object covers its views without inventing initial bytes"
                } else {
                    "emitted object extent or initial-state correspondence is not established"
                },
            )
        })
        .collect();
    if !events.is_empty() {
        eprintln!(
            "[storage-obligations] emitted-objects={} checked={} unresolved={}",
            events.len(),
            events
                .iter()
                .filter(|e| e.outcome == Outcome::Proven)
                .count(),
            events
                .iter()
                .filter(|e| e.outcome != Outcome::Proven)
                .count()
        );
    }
    append(db, events);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::c_pass::types::*;

    #[test]
    fn emitted_layout_requires_extent_and_no_invented_initialization() {
        let mut variable = VarDecl::new(
            "bytes",
            CType::Array(Box::new(CType::char_unsigned()), Some(8)),
        );
        let view = ObjectView {
            object: ObjectId {
                function: 1,
                base: 16,
            },
            offset: 0,
            extent: 8,
        };
        assert!(covers(&variable, &view));
        variable.ty = CType::Array(Box::new(CType::char_unsigned()), Some(4));
        assert!(!covers(&variable, &view));
        variable.ty = CType::Array(Box::new(CType::char_unsigned()), Some(8));
        variable.init = Some(Initializer::Expr(CExpr::int(0)));
        assert!(!covers(&variable, &view));
    }
}
