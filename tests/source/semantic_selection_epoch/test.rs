#[test]
fn final_selection_requests_and_materializes_a_frame_object() {
    // Extent is physical geometry (callee end 33 + index bound 7), not
    // instruction-order evidence. Metadata requires an actual committed epoch.
    let main = OUTPUT.tu.decls.iter().find_map(|declaration| match declaration {
        TopLevelDecl::FuncDef(function) if function.name == "main" => Some(function),
        _ => None,
    }).expect("main was emitted");
    assert!(main.local_vars.iter().any(|local|
        local.storage_views.iter().any(|view| view.extent == 40)
            && matches!(&local.ty, CType::Array(_, Some(extent)) if *extent >= 40)),
        "selector feedback did not reach emitted C: {}", OUTPUT.text);
}
