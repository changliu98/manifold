pub mod aarch64;
pub mod arm32;
pub mod block;
pub mod branch;
pub mod cfg;
pub mod function;
pub mod instruction;
pub mod operand;
pub mod pe;
pub mod symbol;

use std::collections::HashMap;
use std::path::Path;

use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;

/// Build a map from operand ID to immediate value from the op_immediate relation.
pub fn build_op_imm_map<'a>(db: &'a DecompileDB) -> HashMap<&'a str, i64> {
    let mut op_imm_map = HashMap::new();
    for (id, val, _) in db.rel_iter::<(Symbol, i64, usize)>("op_immediate") {
        op_imm_map.insert(*id, *val);
    }
    op_imm_map
}

// Top-level entry point: disassemble and analyze a binary, populating all DB relations.
pub fn load_from_binary(db: &mut DecompileDB, binary_path: &Path) {
    let bin_data = std::fs::read(binary_path)
        .unwrap_or_else(|e| panic!("Failed to read binary {:?}: {}", binary_path, e));
    let obj = object::File::parse(&*bin_data)
        .unwrap_or_else(|e| panic!("Failed to parse binary {:?}: {}", binary_path, e));

    // Detect ABI from binary headers
    let abi = crate::abi::detect_abi(&obj)
        .unwrap_or_else(|e| panic!("Unsupported binary {:?}: {}", binary_path, e));
    log::info!(
        "Detected ABI: {:?} / {:?} ({}bit, ptr={}B)",
        abi.format,
        abi.arch,
        if abi.is_64bit() { 64 } else { 32 },
        abi.pointer_size
    );
    db.target_abi = Some(abi);

    pe::validate_native_pe(&obj)
        .unwrap_or_else(|e| panic!("Unsupported PE binary {:?}: {}", binary_path, e));

    symbol::load_symbols(db, &obj);
    symbol::load_eh_frame_ranges(db, &obj);
    let pe_function_leaders = pe::load_metadata(db, &obj)
        .unwrap_or_else(|e| panic!("Failed to load PE metadata from {:?}: {}", binary_path, e));

    let insns = instruction::disassemble_sections(db, &obj);

    // Jump table analysis must run before block building to provide extra leaders
    let jump_table_targets = cfg::analyze_jump_tables(db, &insns, &obj);
    let mut extra_leaders: Vec<u64> = jump_table_targets
        .values()
        .flat_map(|info| info.ordered_targets.iter().copied())
        .collect();
    extra_leaders.extend(pe_function_leaders);

    let prologue_entries = function::detect_prologue_entries(&insns);
    extra_leaders.extend(prologue_entries.iter());

    // Make data code pointers (vtable/fn-ptr tables, PIE addends) block leaders so infer_functions can seed and carve their bodies; build_blocks keeps only real instruction starts.
    let jump_table_dsts: std::collections::HashSet<u64> = jump_table_targets
        .values()
        .flat_map(|info| info.ordered_targets.iter().copied())
        .collect();
    let code_pointer_targets: Vec<u64> = db
        .rel_iter::<(Address, Address)>("code_pointer_in_data")
        .map(|(_, target)| *target)
        .filter(|t| !jump_table_dsts.contains(t))
        .collect();
    extra_leaders.extend(code_pointer_targets.iter());

    // Recover main from __libc_start_main pattern for stripped binaries; must precede build_blocks so main becomes a block leader.
    if db.abi().format == crate::abi::BinaryFormat::Elf {
        if let Some(main_addr) = function::detect_main_via_libc_start_main(db, &insns) {
            extra_leaders.push(main_addr);
            function::publish_recovered_main(db, main_addr);
            log::debug!(
                "Recovered main from __libc_start_main pattern: {:x}",
                main_addr
            );
        }
    }

    log::debug!(
        "Extra block leaders: {} jump table targets + {} prologue entries",
        extra_leaders.len() - prologue_entries.len(),
        prologue_entries.len()
    );

    block::build_blocks(db, &insns, &extra_leaders);

    cfg::build_cfg(db, &insns, &obj, jump_table_targets);

    // Detect clang-style data lookup tables (value tables, not code address tables)
    let data_lookup_tables = cfg::analyze_data_lookup_tables(db, &insns, &obj);
    if !data_lookup_tables.is_empty() {
        log::info!("Detected {} data lookup table(s)", data_lookup_tables.len());
    }
    for info in &data_lookup_tables {
        let reg_str: &'static str = match &info.index_reg {
            Some(r) => Box::leak(r.clone().into_boxed_str()),
            None => "",
        };
        db.rel_push(
            "data_lookup_table",
            (
                info.mov_addr,
                info.table_base,
                info.entry_count,
                info.entry_scale,
                reg_str,
            ),
        );
        for (idx, &val) in info.values.iter().enumerate() {
            db.rel_push("data_lookup_table_value", (info.mov_addr, idx, val));
        }
    }

    db.rel_set(
        "function_call",
        db.rel_iter::<(Address, Address)>("direct_call")
            .cloned()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    function::infer_functions(db, &insns);

    // BR/BX are shared by indirect tail calls and computed jump dispatchers.
    // Classify them only after function ownership and jump-table facts exist;
    // the classifier follows CFG reaching definitions and publishes only the
    // positive stable-function-pointer family.
    cfg::classify_indirect_tailcalls(db, &insns);

    symbol::load_strings(db, &obj);

    symbol::compute_labeled_addresses(db, &obj);

    load_static_csv(db);

    db.compute_mach_func_from_function_inference();

    // DecompileDB is type-erased, so rel_set cannot infer this tuple's type
    // from the relation declaration.  Keep it explicitly i64: every Ascent
    // consumer declares arch_bit(i64), and inserting the default i32 literal
    // makes the downcast fail and presents an empty relation to every pass.
    let bits: i64 = if db.abi().is_64bit() { 64 } else { 32 };
    db.rel_set(
        "arch_bit",
        vec![(bits,)]
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
}

// Load extern function signatures (call after load_from_binary).
pub fn load_preset(db: &mut DecompileDB) {
    db.load_preset_functions();
}

// Load the builtin-function table, embedded at compile time via include_str!.
fn load_static_csv(db: &mut DecompileDB) {
    use crate::util::parse_csv_str;

    db.rel_set(
        "builtins",
        parse_csv_str::<String>(include_str!("../../data/csv/builtins.csv"), b'\t')
            .into_iter()
            .map(|s| (Box::leak(s.into_boxed_str()) as &'static str,))
            .collect::<ascent::boxcar::Vec<_>>(),
    );
}
