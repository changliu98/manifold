//! Machine-rooted effect contracts. Accounting and semantic validation are
//! distinct: an opaque carrier accounts for an effect but cannot certify C.
pub(crate) mod c;
pub(crate) mod capture;
pub(crate) mod contracts;
pub(crate) mod flags;
pub(crate) mod flow;
#[cfg(test)]
mod tests;

use crate::x86::types::Node;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EffectId {
    pub instruction: Node,
    pub slot: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Stage {
    Machine,
    #[allow(dead_code)]
    Rtl,
    Selection,
    Emission,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ArtifactId {
    pub epoch: u32,
    pub stage: Stage,
    pub node: Node,
    pub alternative: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Outcome {
    Carried,
    Opaque,
    Missing,
    Refuted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EffectSite {
    pub function: u64,
    pub node: u64,
    pub epoch: u32,
    pub alternative: usize,
}

/// Immutable receipts identify the precise representation and the property
/// checked. They are not whole-function equivalence certificates.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Receipt {
    pub effect: EffectId,
    pub artifact: ArtifactId,
    pub outcome: Outcome,
    pub reason: &'static str,
}

pub(crate) fn opaque_name(id: EffectId) -> String {
    format!(
        "__manifold_unresolved_effect_{:x}_{}",
        id.instruction, id.slot
    )
}

pub(crate) fn is_opaque(name: &str) -> bool {
    name.starts_with("__manifold_unresolved_effect_")
}

pub(crate) fn builtin_inputs<'a>(
    rows: impl Iterator<Item = (&'a usize, &'a u64)>,
) -> impl Iterator<Item = Vec<crate::x86::types::BuiltinArg<u64>>> {
    let mut values: Vec<_> = rows.map(|(&position, &value)| (position, value)).collect();
    values.sort_unstable();
    std::iter::once(
        values
            .into_iter()
            .map(|(_, value)| crate::x86::types::BuiltinArg::BA(value))
            .collect(),
    )
}

/// Final admission sees actual occurrence identities, including no-model
/// defaults and postselection output. A scope failure never emits fake C.
pub(crate) fn finalize(db: &mut crate::decompile::elevator::DecompileDB) {
    crate::decompile::passes::clight_select::syntax::Stack::production().audit_emission(db);
    if db.unresolved_effect_count() > 0 {
        // Keep IR diagnostics, but never advertise unresolved output as
        // executable C. Each analysis owns its own admission obligations.
        db.cast_optimized_translation_unit = None;
        db.cast_raw_translation_unit = None;
    }
}
