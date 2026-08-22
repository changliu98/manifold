//! Native x86 PE metadata ingestion, PE32 and PE32+ alike: IAT slot names, exports, MSVC name decorations and (PE32+ only) exception-directory extents, at preferred virtual addresses.

use std::mem;

use object::read::pe::{ImageNtHeaders, ImageOptionalHeader, PeFile};
use object::{LittleEndian as LE, Object, ObjectSection};

use crate::abi::parse_decorated_name;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::{Address, Symbol};

const UNW_FLAG_CHAININFO: u8 = 0x4;

fn leak(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

/// Reject PE variants the current x86 pipeline does not model; non-PE inputs are a no-op.
pub fn validate_native_pe(obj: &object::File<'_>) -> Result<(), String> {
    let managed = match obj {
        object::File::Pe64(pe) => pe
            .data_directory(object::pe::IMAGE_DIRECTORY_ENTRY_COM_DESCRIPTOR)
            .is_some(),
        object::File::Pe32(pe) => pe
            .data_directory(object::pe::IMAGE_DIRECTORY_ENTRY_COM_DESCRIPTOR)
            .is_some(),
        _ => return Ok(()),
    };
    if managed {
        return Err("managed CLR images are not native x86 PE binaries".to_string());
    }
    Ok(())
}

/// Load PE-only metadata and return block leaders contributed by it.
pub fn load_metadata(db: &mut DecompileDB, obj: &object::File<'_>) -> Result<Vec<Address>, String> {
    // MSVC's `_foo@12` / `@foo@8` C decoration exists ONLY on x86-32; x64 has a single convention and no decoration, so a leading underscore there is part of the identifier.
    let decorated = matches!(obj, object::File::Pe32(_));
    let mut leaders = match obj {
        object::File::Pe64(pe) => load_pe_directories(db, pe, decorated)?,
        object::File::Pe32(pe) => load_pe_directories(db, pe, decorated)?,
        _ => return Ok(Vec::new()),
    };

    let code_ranges: Vec<(u64, u64)> = obj
        .sections()
        .filter(|s| s.kind() == object::SectionKind::Text)
        .map(|s| (s.address(), s.address().saturating_add(s.size())))
        .collect();

    for export in obj
        .exports()
        .map_err(|e| format!("invalid PE export table: {e}"))?
    {
        let addr = export.address();
        if !code_ranges
            .iter()
            .any(|(start, end)| addr >= *start && addr < *end)
        {
            continue;
        }
        let raw_name = String::from_utf8_lossy(export.name()).into_owned();
        if raw_name.is_empty() {
            continue;
        }
        let name: Symbol = record_decoration(db, &raw_name, Some(addr), decorated);
        db.rel_push("symbols", (addr, name, "Beg"));
        db.rel_push(
            "symbol_table",
            (
                addr, 0usize, "FUNC", "GLOBAL", "DEFAULT", 0usize, "", 0usize, name,
            ),
        );
        db.rel_push("known_function_entry", (addr,));
        leaders.push(addr);
    }

    // A PE with no entry yields the image base (the DOS header, not code), so text-section membership is the only sound test.
    let entry = obj.entry();
    if code_ranges
        .iter()
        .any(|(start, end)| entry >= *start && entry < *end)
    {
        db.rel_push("known_function_entry", (entry,));
        leaders.push(entry);
    }

    leaders.sort_unstable();
    leaders.dedup();
    Ok(leaders)
}

/// Directory-driven metadata shared by both PE widths; the IAT thunk width is the only real difference.
fn load_pe_directories<Pe: ImageNtHeaders>(
    db: &mut DecompileDB,
    pe: &PeFile<'_, Pe>,
    decorated: bool,
) -> Result<Vec<Address>, String> {
    let image_base = pe.nt_headers().optional_header().image_base();
    let leaders = load_runtime_functions(db, pe, image_base)?;
    load_imports(db, pe, image_base, decorated)?;
    Ok(leaders)
}

/// Record what an MSVC name decoration proves about a function's calling convention and return the UNDECORATED identifier, which is the name the rest of the pipeline (and known_extern_signature) matches on.
fn record_decoration(
    db: &mut DecompileDB,
    raw: &str,
    address: Option<Address>,
    decoration_applies: bool,
) -> Symbol {
    if !decoration_applies {
        return leak(raw.to_string());
    }
    let Some(decorated) = parse_decorated_name(raw) else {
        return leak(raw.to_string());
    };
    let reg_args = decorated.conv.register_arg_count();
    let name: Symbol = leak(decorated.undecorated);
    // Only a callee-cleanup decoration carries a byte count, and it counts ALL arguments including ECX/EDX.
    if let Some(bytes) = decorated.arg_bytes {
        match address {
            Some(addr) => db.rel_push("func_decorated_arg_bytes", (addr, bytes as i64)),
            None => db.rel_push("extern_decorated_arg_bytes", (name, bytes as i64)),
        }
    }
    if reg_args > 0 {
        match address {
            Some(addr) => db.rel_push("func_decorated_reg_args", (addr, reg_args)),
            None => db.rel_push("extern_decorated_reg_args", (name, reg_args)),
        }
    }
    name
}

/// x86-32 PE has NO exception directory of RUNTIME_FUNCTION records (its SEH is FS:[0]-chained), so there are no function extents to read and discovery falls back to symbols, exports, call-graph seeding and prologue detection.
fn load_runtime_functions<Pe: ImageNtHeaders>(
    db: &mut DecompileDB,
    pe: &PeFile<'_, Pe>,
    image_base: u64,
) -> Result<Vec<Address>, String> {
    if !pe.nt_headers().is_type_64() {
        return Ok(Vec::new());
    }
    let directory = match pe.data_directory(object::pe::IMAGE_DIRECTORY_ENTRY_EXCEPTION) {
        Some(d) => d,
        None => return Ok(Vec::new()),
    };
    let data = directory
        .data(pe.data(), &pe.section_table())
        .map_err(|e| format!("invalid PE exception directory: {e}"))?;
    let entry_size = mem::size_of::<object::pe::ImageRuntimeFunctionEntry>();
    if data.len() % entry_size != 0 {
        return Err(format!(
            "exception directory size {} is not a multiple of RUNTIME_FUNCTION size {}",
            data.len(),
            entry_size
        ));
    }

    let sections = pe.section_table();
    let mut leaders = Vec::new();
    for raw in data.chunks_exact(entry_size) {
        let begin_rva = u32::from_le_bytes(raw[0..4].try_into().unwrap());
        let end_rva = u32::from_le_bytes(raw[4..8].try_into().unwrap());
        let unwind_rva = u32::from_le_bytes(raw[8..12].try_into().unwrap()) & !0x3;
        if begin_rva == 0 || begin_rva >= end_rva {
            continue;
        }

        let begin = image_base
            .checked_add(u64::from(begin_rva))
            .ok_or_else(|| format!("PE runtime-function start RVA {begin_rva:#x} overflows"))?;
        let end = image_base
            .checked_add(u64::from(end_rva))
            .ok_or_else(|| format!("PE runtime-function end RVA {end_rva:#x} overflows"))?;
        db.rel_push("known_function_range", (begin, end));
        // Every fragment boundary helps the block builder, but only primary entries seed functions; CHAININFO fragments point back to the primary.
        leaders.push(begin);
        let chained = sections
            .pe_data_at(pe.data(), unwind_rva)
            .and_then(|bytes| bytes.first().copied())
            .map(|version_and_flags| ((version_and_flags >> 3) & 0x1f) & UNW_FLAG_CHAININFO != 0)
            .unwrap_or(false);
        if !chained {
            db.rel_push("known_function_entry", (begin,));
        }
    }

    log::debug!(
        "PE exception directory: {} runtime-function records",
        data.len() / entry_size
    );
    Ok(leaders)
}

fn load_imports<Pe: ImageNtHeaders>(
    db: &mut DecompileDB,
    pe: &PeFile<'_, Pe>,
    image_base: u64,
    decorated: bool,
) -> Result<(), String> {
    let table = match pe
        .import_table()
        .map_err(|e| format!("invalid PE import table: {e}"))?
    {
        Some(t) => t,
        None => return Ok(()),
    };
    let mut descriptors = table
        .descriptors()
        .map_err(|e| format!("invalid PE import descriptors: {e}"))?;
    // PE32 walks the IAT in ImageThunkData32 steps, PE32+ in ImageThunkData64 steps.
    let thunk_size = mem::size_of::<Pe::ImageThunkData>() as u64;
    let mut count = 0usize;

    while let Some(desc) = descriptors
        .next()
        .map_err(|e| format!("invalid PE import descriptor: {e}"))?
    {
        let library = table
            .name(desc.name.get(LE))
            .map_err(|e| format!("invalid PE import library name: {e}"))?;
        let library = String::from_utf8_lossy(library);
        let mut lookup_rva = desc.original_first_thunk.get(LE);
        if lookup_rva == 0 {
            lookup_rva = desc.first_thunk.get(LE);
        }
        let mut thunks = table
            .thunks(lookup_rva)
            .map_err(|e| format!("invalid PE import thunk list: {e}"))?;
        let first_thunk = u64::from(desc.first_thunk.get(LE));
        let mut index = 0u64;
        while let Some(thunk) = thunks
            .next::<Pe>()
            .map_err(|e| format!("invalid PE import thunk: {e}"))?
        {
            let name = match table
                .import::<Pe>(thunk)
                .map_err(|e| format!("invalid PE import name: {e}"))?
            {
                object::read::pe::Import::Name(_, bytes) => {
                    record_decoration(db, &String::from_utf8_lossy(bytes), None, decorated)
                }
                object::read::pe::Import::Ordinal(ordinal) => {
                    leak(format!("{}_ordinal_{}", library.replace('.', "_"), ordinal))
                }
            };
            let thunk_offset = index
                .checked_mul(thunk_size)
                .and_then(|offset| first_thunk.checked_add(offset))
                .and_then(|rva| image_base.checked_add(rva))
                .ok_or_else(|| format!("PE IAT slot {index} address overflows"))?;
            let slot = thunk_offset;
            db.rel_push("pointer_to_external_symbol", (slot, name));
            count += 1;
            index += 1;
        }
    }

    log::debug!("PE imports: {} IAT slots", count);
    Ok(())
}
