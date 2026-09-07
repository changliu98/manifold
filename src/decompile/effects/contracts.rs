//! Small structural contract kernel. A decomposition requires all members;
//! source tags alone do not discharge it. Semantic checks remain selection-owned.
use super::{ArtifactId, EffectId, Outcome};
use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Transfer {
    pub effect: EffectId,
    pub inputs: Vec<ArtifactId>,
    pub outputs: Vec<ArtifactId>,
}

pub(crate) fn check_transfer(
    transfer: &Transfer,
    available: &BTreeSet<ArtifactId>,
    selected: &BTreeSet<ArtifactId>,
    epoch: u32,
) -> Outcome {
    if transfer.inputs.is_empty()
        || transfer.outputs.is_empty()
        || transfer
            .inputs
            .iter()
            .chain(&transfer.outputs)
            .any(|a| a.epoch != epoch)
        || transfer.inputs.iter().any(|a| !available.contains(a))
        || transfer.outputs.iter().any(|a| !selected.contains(a))
    {
        return Outcome::Missing;
    }
    if transfer.outputs.iter().collect::<BTreeSet<_>>().len() != transfer.outputs.len() {
        return Outcome::Refuted;
    }
    Outcome::Carried
}
