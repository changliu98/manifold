
pub mod instruction;
pub mod operand;
pub mod symbol;
pub mod block;
pub mod cfg;
pub mod function;

use std::path::Path;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::linear_pass::init_op_immediate_map;
use crate::x86::types::*;

// Top-level entry point: disassemble and analyze a binary, populating all DB relations.
pub fn load_from_binary(db: &mut DecompileDB, binary_path: &Path) {
    let bin_data = std::fs::read(binary_path)
        .unwrap_or_else(|e| panic!("Failed to read binary {:?}: {}", binary_path, e));
    let obj = object::File::parse(&*bin_data)
        .unwrap_or_else(|e| panic!("Failed to parse binary {:?}: {}", binary_path, e));

    // Detect ABI from binary headers
    let abi = crate::x86::abi::detect_abi(&obj);
    log::info!("Detected ABI: {:?} / {:?} ({}bit, ptr={}B)",
              abi.format, abi.arch,
              if abi.is_64bit() { 64 } else { 32 },
              abi.pointer_size);
    if !crate::x86::abi::abi_config_initialized() {
        crate::x86::abi::init_abi_config(abi);
    }

    symbol::load_symbols(db, &obj);

    let insns = instruction::disassemble_sections(db, &obj);

    // Jump table analysis must run before block building to provide extra leaders
    let jump_table_targets = cfg::analyze_jump_tables(db, &insns, &obj);
    let mut extra_leaders: Vec<u64> = jump_table_targets.values()
        .flat_map(|info| info.ordered_targets.iter().copied())
        .collect();

    let prologue_entries = function::detect_prologue_entries(&insns);
    extra_leaders.extend(prologue_entries.iter());
    log::debug!("Extra block leaders: {} jump table targets + {} prologue entries",
              extra_leaders.len() - prologue_entries.len(), prologue_entries.len());

    block::build_blocks(db, &insns, &extra_leaders);

    cfg::build_cfg(db, &insns, &obj, jump_table_targets);

    db.rel_set("function_call", db.rel_iter::<(Address, Address)>("direct_call").cloned().collect::<ascent::boxcar::Vec<_>>());

    function::infer_functions(db, &insns);

    symbol::load_strings(db, &obj);


    symbol::compute_labeled_addresses(db, &obj);

    // Initialize op_immediate map with both operand immediates and symbol addresses
    let mut combined: Vec<_> = db.rel_iter::<(Symbol, i64, usize)>("op_immediate").cloned().collect();
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        combined.push((*name, *addr as i64, 0));
    }
    init_op_immediate_map(&combined);

    load_static_csv(db);

    db.compute_mach_func_from_function_inference();

    let bits = if crate::x86::abi::abi_config().is_64bit() { 64 } else { 32 };
    db.rel_set("arch_bit", vec![(bits,)].into_iter().collect::<ascent::boxcar::Vec<_>>());

}

// Load extern function signatures (call after load_from_binary).
pub fn load_preset(db: &mut DecompileDB) {
    db.load_preset_functions();
}

// Load project-local static CSV data (registers, jump instructions, builtins, mnemonics), embedded at compile time via include_str!.
fn load_static_csv(db: &mut DecompileDB) {
    use crate::util::{leak, parse_csv_str};

    db.rel_set("reg_x64", parse_csv_str::<String>(
        include_str!("../../data/csv/reg_x64.csv"), b'\t')
        .into_iter()
        .map(|reg| (Box::leak(reg.into_boxed_str()) as &'static str,))
        .collect::<ascent::boxcar::Vec<_>>());

    db.rel_set("jump_instr", parse_csv_str::<String>(
        include_str!("../../data/csv/jump_instr.csv"), b'\t')
        .into_iter()
        .map(|s| (Box::leak(s.into_boxed_str()) as &'static str,))
        .collect::<ascent::boxcar::Vec<_>>());

    db.rel_set("printasm_mnemonic", parse_csv_str::<(String, String)>(
        include_str!("../../data/csv/bindmnemonic.csv"), b',')
        .into_iter()
        .map(|(x, y)| (leak::<String, str>(x), leak::<String, str>(y)))
        .collect::<ascent::boxcar::Vec<_>>());

    db.rel_set("builtins", parse_csv_str::<String>(
        include_str!("../../data/csv/builtins.csv"), b'\t')
        .into_iter()
        .map(|s| (Box::leak(s.into_boxed_str()) as &'static str,))
        .collect::<ascent::boxcar::Vec<_>>());
}
