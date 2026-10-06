pub mod adequacy;
pub(crate) mod analysis;
pub mod branch_theory;
pub mod candtype;
pub mod type_graph;
pub mod class_theory;
pub mod ctyping;
pub mod decl_solve;
pub mod flow;
pub mod flow_theory;
pub mod interface_solve;
pub mod integer_semantics;
pub mod propagator;
pub mod query;
pub mod select;
pub mod solve;
pub(crate) mod storage_theory;
pub(crate) mod memory_theory;
pub(crate) mod obligations;
pub(crate) mod producer_values;
pub(crate) mod word_views;
pub(crate) mod word_inputs;
pub mod wt_audit;

pub fn derive_canonical_path(path_str: &str) -> String {
    use std::path::PathBuf;

    let path = PathBuf::from(path_str);
    let filename = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(path_str);

    if filename.ends_with(".light.c") {
        path_str.to_string()
    } else if path.extension().is_some() {
        let stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("output");
        path.with_file_name(format!("{}.light.c", stem))
            .to_str()
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("{}.light.c", path_str))
    } else {
        format!("{}.light.c", path_str)
    }
}

pub fn derive_optimized_c_path(base_path: &str) -> String {
    derive_with_suffix(base_path, ".optimized.c")
}

pub fn derive_with_suffix(base_path: &str, suffix: &str) -> String {
    use std::path::PathBuf;

    let path = PathBuf::from(base_path);
    let filename = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(base_path);
    let stem = if filename.ends_with(".light.c") {
        filename.trim_end_matches(".light.c").to_string()
    } else if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
        stem.to_string()
    } else {
        filename.to_string()
    };

    let new_name = format!("{}{}", stem, suffix);
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => {
            parent.join(new_name).to_string_lossy().into_owned()
        }
        _ => new_name,
    }
}
