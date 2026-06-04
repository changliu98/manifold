
use std::collections::{BTreeSet, HashMap, HashSet};
use object::{Object, ObjectSection, ObjectSymbol, ObjectSymbolTable, SectionKind, SymbolKind};
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;

// Strip GCC/Clang optimizer suffixes (.constprop, .isra, .cold, etc.) into valid C identifiers.
fn sanitize_symbol_name(name: &str) -> String {
    // Find earliest position of ANY recognized optimizer suffix (handles chained suffixes like compare.part.0.isra.0 -> compare_part_0_isra_0).
    let positions = [
        name.find(".constprop."),
        name.find(".isra."),
        name.find(".cold"),
        name.find(".part."),
        name.find(".lto_priv."),
        name.find(".localalias"),
    ];
    if let Some(min_pos) = positions.iter().flatten().min() {
        let pos = *min_pos;
        return name[..pos].to_string() + &name[pos..].replace('.', "_");
    }
    name.to_string()
}

// Fixed byte width of a DWARF pointer encoding's format nibble (0 = variable/unsupported here).
fn eh_enc_fixed_size(enc: u8) -> usize {
    match enc & 0x0f {
        0x02 | 0x0a => 2,
        0x03 | 0x0b => 4,
        0x04 | 0x0c => 8,
        _ => 0,
    }
}

// Recover authoritative function-start addresses from the .eh_frame_hdr sorted FDE search table (real functions have an FDE; landing pads/post-ret tails do not); degrades to empty on any unhandled pointer encoding so the downstream guard is a no-op rather than a wrong range.
fn parse_eh_frame_hdr_starts(obj: &object::File) -> Vec<u64> {
    let sec = match obj.section_by_name(".eh_frame_hdr") { Some(s) => s, None => return Vec::new() };
    let vaddr = sec.address();
    let data = match sec.data() { Ok(d) => d, Err(_) => return Vec::new() };
    if data.len() < 12 || data[0] != 1 { return Vec::new(); }
    let (eh_frame_ptr_enc, fde_count_enc, table_enc) = (data[1], data[2], data[3]);
    let mut off = 4usize;
    let p1 = eh_enc_fixed_size(eh_frame_ptr_enc);
    if p1 == 0 || off + p1 > data.len() { return Vec::new(); }
    off += p1;
    let cs = eh_enc_fixed_size(fde_count_enc);
    if cs == 0 || off + cs > data.len() { return Vec::new(); }
    let fde_count: u64 = match cs {
        2 => u16::from_le_bytes([data[off], data[off + 1]]) as u64,
        4 => u32::from_le_bytes([data[off], data[off + 1], data[off + 2], data[off + 3]]) as u64,
        8 => u64::from_le_bytes(data[off..off + 8].try_into().unwrap()),
        _ => return Vec::new(),
    };
    off += cs;
    let es = eh_enc_fixed_size(table_enc);
    if es == 0 { return Vec::new(); }
    let app = table_enc & 0x70;
    let entry = es * 2;
    let mut starts: Vec<u64> = Vec::new();
    for i in 0..fde_count {
        let p = off + (i as usize) * entry;
        if p + es > data.len() { break; }
        let rel: i64 = match es {
            2 => i16::from_le_bytes([data[p], data[p + 1]]) as i64,
            4 => i32::from_le_bytes([data[p], data[p + 1], data[p + 2], data[p + 3]]) as i64,
            8 => i64::from_le_bytes(data[p..p + 8].try_into().unwrap()),
            _ => return Vec::new(),
        };
        let loc = match app {
            0x00 => rel as u64,
            0x10 => (vaddr + p as u64).wrapping_add(rel as u64),
            0x30 => vaddr.wrapping_add(rel as u64),
            _ => return Vec::new(),
        };
        starts.push(loc);
    }
    starts.sort_unstable();
    starts.dedup();
    starts
}

// Push eh_frame_func_range(start, next_start) bracket ranges from the FDE starts so function inference treats a no-predecessor block strictly inside a range as a mid-body block (landing pad/tail), not a spurious entry; real functions sit ON a boundary so the strict-inequality guard preserves them.
pub fn load_eh_frame_ranges(db: &mut DecompileDB, obj: &object::File) {
    let starts = parse_eh_frame_hdr_starts(obj);
    for w in starts.windows(2) {
        db.rel_push("eh_frame_func_range", (w[0] as Address, w[1] as Address));
    }
    if starts.len() >= 2 {
        log::debug!("eh_frame_hdr: {} FDE starts -> {} bracket ranges", starts.len(), starts.len() - 1);
    }
}

// Populate symbol_table, symbols, symbol_size, PLT, main_function, and data pointer relations.
pub fn load_symbols(db: &mut DecompileDB, obj: &object::File) {
    let mut symbols_vec: Vec<(u64, usize, &'static str, &'static str,
                               &'static str, usize, &'static str, usize, &'static str)> = Vec::new();
    let mut best_sym: Vec<(u64, &'static str, &'static str)> = Vec::new();

    let leak_str = |s: String| -> &'static str {
        Box::leak(s.into_boxed_str())
    };

    for sym in obj.symbols().chain(obj.dynamic_symbols()) {
        let addr = sym.address();
        let size = sym.size() as usize;
        let name_raw = sym.name().unwrap_or("");
        if name_raw.is_empty() { continue; }
        let name: &'static str = leak_str(sanitize_symbol_name(name_raw));

        let sym_type: &'static str = match sym.kind() {
            SymbolKind::Text => "FUNC",
            SymbolKind::Data => "OBJECT",
            SymbolKind::Section => "SECTION",
            SymbolKind::File => "FILE",
            SymbolKind::Tls => "TLS",
            _ => "NOTYPE",
        };

        let binding: &'static str = if sym.is_global() {
            "GLOBAL"
        } else if sym.is_local() {
            "LOCAL"
        } else {
            "WEAK"
        };

        let (section_type, section_idx, section_name): (&str, usize, &str) =
            match sym.section() {
                object::SymbolSection::Section(idx) => {
                    if let Some(sec) = obj.section_by_index(idx).ok() {
                        let sname = sec.name().unwrap_or("");
                        ("DEFAULT", idx.0, sname)
                    } else {
                        ("DEFAULT", idx.0, "")
                    }
                }
                object::SymbolSection::Undefined => ("UNDEF", 0, ""),
                object::SymbolSection::Absolute => ("ABS", 0, ""),
                _ => ("UNKNOWN", 0, ""),
            };

        let sect_type_s: &'static str = leak_str(section_type.to_string());
        let sect_name_s: &'static str = leak_str(section_name.to_string());

        symbols_vec.push((addr, size, sym_type, binding, sect_type_s,
                          section_idx, sect_name_s, 0, name));

        if section_type != "UNDEF" {
            best_sym.push((addr, name, "Beg"));
        }
    }

    db.rel_set("symbol_table", symbols_vec.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("symbols", best_sym.into_iter().collect::<ascent::boxcar::Vec<_>>());

    db.rel_set("symbol_size", db.rel_iter::<(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol)>("symbol_table")
        .filter(|(_, size, sym_type, ..)| *size > 0 && *sym_type == "OBJECT")
        .map(|(addr, size, _, _, _, _, _, _, name)| (*addr, *size, *name))
        .collect::<ascent::boxcar::Vec<_>>());

    load_plt(db, obj);

    detect_main(db, obj);

    load_data_pointers(db, obj);

    load_data_section_ranges(db, obj);
}

// Push [start, end) ranges for allocated non-code data sections; a no-base absolute or scaled-index displacement is a genuine data/table address only when it lands in one, else a scaled-index lea displacement (e.g. `lea 0x8(,%rsi,8)`) is mistaken for a table base and synthesized into a bogus global.
fn load_data_section_ranges(db: &mut DecompileDB, obj: &object::File) {
    for section in obj.sections() {
        if !section_is_allocated_elf(&section) {
            continue;
        }
        match section.kind() {
            SectionKind::Text => continue,
            _ => {}
        }
        let addr = section.address();
        let size = section.size();
        if addr == 0 || size == 0 {
            continue;
        }
        db.rel_push("data_section_range", (addr, addr + size));
    }
}

// True when an ELF section is loaded at runtime (SHF_ALLOC); non-allocated metadata sections (.comment, .note.*, .debug_*) sit at sh_addr=0 and never hold runtime data.
fn section_is_allocated_elf(section: &object::Section) -> bool {
    match section.flags() {
        object::SectionFlags::Elf { sh_flags } => {
            sh_flags & u64::from(object::elf::SHF_ALLOC) != 0
        }
        _ => section.address() != 0,
    }
}

// Parse PLT stubs (.plt, .plt.sec, .plt.got) to populate plt_entry and plt_block relations.
fn load_plt(db: &mut DecompileDB, obj: &object::File) {
    use capstone::prelude::*;

    let leak = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };

    // Build GOT-slot to symbol-name map from dynamic relocations (.rela.dyn and .rela.plt JUMP_SLOT entries).
    let mut got_to_name: std::collections::HashMap<u64, &'static str> =
        std::collections::HashMap::new();

    // Build relocation-index to name map for CET .plt entries (PUSH idx style)
    let mut rela_plt_names: Vec<&'static str> = Vec::new();

    if let Some(dyn_symtab) = obj.dynamic_symbol_table() {
        // .rela.dyn entries (GLOB_DAT, etc.)
        if let Some(dyn_relocs) = obj.dynamic_relocations() {
            for (offset, reloc) in dyn_relocs {
                if let object::RelocationTarget::Symbol(sym_idx) = reloc.target() {
                    if let Ok(sym) = dyn_symtab.symbol_by_index(sym_idx) {
                        let sym_name = sym.name().unwrap_or("");
                        if !sym_name.is_empty() {
                            let clean_name = sym_name.split('@').next().unwrap_or(sym_name);
                            got_to_name.insert(offset, leak(clean_name.to_string()));
                        }
                    }
                }
            }
        }
        // .rela.plt entries (JUMP_SLOT for PLT stubs, not in dynamic_relocations()); also builds rela_plt_names for CET .plt entries in one pass.
        for section in obj.sections() {
            if section.name().unwrap_or("") == ".rela.plt" {
                if let Ok(data) = section.data() {
                    let entry_size = 24usize;
                    let mut off = 0;
                    while off + entry_size <= data.len() {
                        let got_offset = u64::from_le_bytes(
                            data[off..off + 8].try_into().unwrap_or([0; 8]),
                        );
                        let info = u64::from_le_bytes(
                            data[off + 8..off + 16].try_into().unwrap_or([0; 8]),
                        );
                        let sym_idx = object::SymbolIndex((info >> 32) as usize);
                        if let Ok(sym) = dyn_symtab.symbol_by_index(sym_idx) {
                            let sym_name = sym.name().unwrap_or("");
                            if !sym_name.is_empty() {
                                let clean_name = sym_name.split('@').next().unwrap_or(sym_name);
                                got_to_name.insert(got_offset, leak(clean_name.to_string()));
                            }
                        }
                        // Build rela_plt_names: look up the got_offset we just potentially inserted
                        if let Some(&name) = got_to_name.get(&got_offset) {
                            rela_plt_names.push(name);
                        } else {
                            rela_plt_names.push("");
                        }
                        off += entry_size;
                    }
                }
                break;
            }
        }
    }

    if got_to_name.is_empty() {
        return;
    }

    let cs = match capstone::Capstone::new()
        .x86()
        .mode(arch::x86::ArchMode::Mode64)
        .syntax(arch::x86::ArchSyntax::Intel)
        .detail(true)
        .build()
    {
        Ok(cs) => cs,
        Err(_) => return,
    };

    // Iterate PLT sections and resolve each stub's symbol via GOT slot
    for section in obj.sections() {
        let sec_name = section.name().unwrap_or("");
        if !sec_name.starts_with(".plt") {
            continue;
        }
        let data = match section.data() {
            Ok(d) => d,
            Err(_) => continue,
        };
        let base = section.address();

        // Record the full PLT-section span so function inference keeps PLT-internal addresses out of tail-call entry seeding.
        db.rel_push("plt_section_range", (base, base + data.len() as u64));

        let entry_size: usize = 16;

        let start_offset: usize = if sec_name == ".plt" { entry_size } else { 0 };

        let mut offset = start_offset;
        while offset + entry_size <= data.len() {
            let entry_addr = base + offset as u64;
            let entry_data = &data[offset..offset + entry_size];

            if let Ok(insns) = cs.disasm_all(entry_data, entry_addr) {
                let mut found = false;
                for insn in insns.as_ref() {
                    let mnem = insn.mnemonic().unwrap_or("");
                    if mnem != "jmp" && mnem != "bnd jmp" {
                        continue;
                    }
                    let detail = match cs.insn_detail(insn) {
                        Ok(d) => d,
                        Err(_) => continue,
                    };
                    let arch = detail.arch_detail();
                    let x86 = match arch.x86() {
                        Some(x) => x,
                        None => continue,
                    };
                    for op in x86.operands() {
                        if let capstone::arch::x86::X86OperandType::Mem(mem) = op.op_type {
                            if mem.base().0 == 0 { continue; }
                            let base_name = cs.reg_name(mem.base())
                                .unwrap_or_default().to_ascii_uppercase();
                            if base_name != "RIP" { continue; }

                            let got_addr = (insn.address() + insn.len() as u64)
                                .wrapping_add(mem.disp() as u64);
                            if let Some(&name) = got_to_name.get(&got_addr) {
                                db.rel_push("plt_block", (entry_addr, name));
                                let jmp_addr = insn.address();
                                db.rel_push("plt_entry", (jmp_addr, name));
                                db.rel_push("plt_entry", (jmp_addr + 1, name));
                                // Register the PLT stub as a named symbol so symbol_resolved_addr maps the extern name to this stub's address (direct CALL imm uses named-call form).
                                db.rel_push("symbols", (entry_addr, name, "Beg"));
                                found = true;
                            }
                        }
                    }
                }
                // Fallback for CET .plt stubs: match PUSH idx to .rela.plt index
                if !found && sec_name == ".plt" && !rela_plt_names.is_empty() {
                    for insn in insns.as_ref() {
                        if insn.mnemonic().unwrap_or("") != "push" { continue; }
                        let detail = match cs.insn_detail(insn) {
                            Ok(d) => d,
                            Err(_) => continue,
                        };
                        let arch = detail.arch_detail();
                        let x86 = match arch.x86() {
                            Some(x) => x,
                            None => continue,
                        };
                        for op in x86.operands() {
                            if let capstone::arch::x86::X86OperandType::Imm(idx) = op.op_type {
                                let idx = idx as usize;
                                if idx < rela_plt_names.len() && !rela_plt_names[idx].is_empty() {
                                    let name = rela_plt_names[idx];
                                    db.rel_push("plt_block", (entry_addr, name));
                                    db.rel_push("plt_entry", (entry_addr, name));
                                    // Register the stub as a named symbol so CALL imm operands resolve to named-call form.
                                    db.rel_push("symbols", (entry_addr, name, "Beg"));
                                }
                            }
                        }
                    }
                }
            }
            offset += entry_size;
        }
    }
}

// Detect the main function address from symbols, falling back to ELF entry point.
fn detect_main(db: &mut DecompileDB, obj: &object::File) {
    for sym in obj.symbols().chain(obj.dynamic_symbols()) {
        if sym.name().unwrap_or("") == "main" && sym.address() > 0 {
            db.rel_set("main_function", vec![(sym.address(),)].into_iter().collect::<ascent::boxcar::Vec<_>>());
            return;
        }
    }

    let entry = obj.entry();
    if entry > 0 {
        db.rel_set("main_function", vec![(entry,)].into_iter().collect::<ascent::boxcar::Vec<_>>());
    }
}

// Scan data sections for code pointers and GOT relocations for external symbol references.
fn load_data_pointers(db: &mut DecompileDB, obj: &object::File) {
    // Exclude PLT stub sections from code ranges: they hold only linkage thunks, so a data slot pointing into a PLT stub is a linker artifact, not a function pointer.
    let code_ranges: Vec<(u64, u64)> = obj.sections()
        .filter(|s| s.kind() == SectionKind::Text)
        .filter(|s| {
            let n = s.name().unwrap_or("");
            n != ".plt" && n != ".plt.sec" && n != ".plt.got"
        })
        .filter_map(|s| Some((s.address(), s.address() + s.size())))
        .collect();

    let is_code_addr = |addr: u64| -> bool {
        code_ranges.iter().any(|(start, end)| addr >= *start && addr < *end)
    };

    // Scan data/rodata for 8-byte values pointing into code; skip GOT sections (.got, .got.plt) since their dynamic-linker pointers (e.g. lazy PLT resolver fallbacks) are not function entries.
    for section in obj.sections() {
        match section.kind() {
            SectionKind::Data | SectionKind::ReadOnlyData | SectionKind::ReadOnlyDataWithRel => {}
            _ => continue,
        }
        let sec_name = section.name().unwrap_or("");
        if sec_name == ".got" || sec_name == ".got.plt" {
            continue;
        }
        let data = match section.data() {
            Ok(d) => d,
            Err(_) => continue,
        };
        let base = section.address();

        for offset in (0..data.len()).step_by(8) {
            if offset + 8 > data.len() { break; }
            let val = u64::from_le_bytes(data[offset..offset+8].try_into().unwrap());
            if is_code_addr(val) {
                db.rel_push("code_pointer_in_data", (base + offset as u64, val));
            }
        }
    }

    // In PIE binaries data code pointers are zero in section bytes (real target is the R_X86_64_RELATIVE addend applied at load), so recover them from the relocation addend here.
    if let Some(dyn_relocs) = obj.dynamic_relocations() {
        for (offset, reloc) in dyn_relocs {
            let is_relative = matches!(
                reloc.flags(),
                object::RelocationFlags::Elf { r_type }
                    if r_type == object::elf::R_X86_64_RELATIVE
                        || r_type == object::elf::R_X86_64_RELATIVE64
            );
            if !is_relative {
                continue;
            }
            let target = reloc.addend() as u64;
            if is_code_addr(target) {
                db.rel_push("code_pointer_in_data", (offset, target));
            }
        }
    }

    // Map GOT relocations to external symbol names
    if let Some(dyn_symtab) = obj.dynamic_symbol_table() {
        if let Some(dyn_relocs) = obj.dynamic_relocations() {
            let got_ranges: Vec<(u64, u64)> = obj.sections()
                .filter(|s| {
                    let name = s.name().unwrap_or("");
                    name == ".got" || name == ".got.plt"
                })
                .map(|s| (s.address(), s.address() + s.size()))
                .collect();

            for (offset, reloc) in dyn_relocs {
                if !got_ranges.iter().any(|(start, end)| offset >= *start && offset < *end) {
                    continue;
                }
                if let object::RelocationTarget::Symbol(sym_idx) = reloc.target() {
                    if let Ok(sym) = dyn_symtab.symbol_by_index(sym_idx) {
                        let sym_name = sym.name().unwrap_or("");
                        if !sym_name.is_empty() {
                            let clean_name = sym_name.split('@').next().unwrap_or(sym_name);
                            let leaked: &'static str = Box::leak(clean_name.to_string().into_boxed_str());
                            db.rel_push("pointer_to_external_symbol", (offset, leaked));
                        }
                    }
                }
            }
        }
    }

}

// Scan .rodata sections for null-terminated ASCII strings.
pub fn load_strings(db: &mut DecompileDB, obj: &object::File) {
    for section in obj.sections() {
        match section.kind() {
            SectionKind::ReadOnlyData | SectionKind::ReadOnlyString => {}
            _ => continue,
        }
        let data = match section.data() {
            Ok(d) => d,
            Err(_) => continue,
        };
        let base = section.address();

        let mut i = 0;
        while i < data.len() {
            if !data[i].is_ascii_graphic() && data[i] != b' ' && data[i] != b'\t' {
                i += 1;
                continue;
            }

            let start = i;
            while i < data.len() && data[i] != 0 {
                i += 1;
            }

            if i < data.len() && data[i] == 0 {
                let str_bytes = &data[start..i];
                if !str_bytes.is_empty() && str_bytes.iter().all(|b| b.is_ascii()) {
                    let content = String::from_utf8_lossy(str_bytes).to_string();
                    let label = format!("L_{:x}", base + start as u64);
                    let size = str_bytes.len();
                    db.rel_push("string_data", (label, content, size));
                }
                i += 1;
            }
        }
    }
}

// Add .L_ symbol entries for referenced addresses that lack ELF symbols.
pub fn compute_labeled_addresses(db: &mut DecompileDB, obj: &object::File) {
    let leak = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };

    let existing: HashSet<u64> = db.rel_iter::<(Address, Symbol, Symbol)>("symbols").map(|(a, _, _)| *a).collect();

    // PLT stub addresses must never receive L_xxxx labels: their name comes from the linker via plt_entry/plt_block.
    let plt_addrs: HashSet<u64> = db
        .rel_iter::<(Address, Symbol)>("plt_entry")
        .map(|(a, _)| *a)
        .chain(db.rel_iter::<(Address, Symbol)>("plt_block").map(|(a, _)| *a))
        .collect();

    // Build sorted symbol ranges from symbol_size so addresses inside a known symbol's range don't get separate L_ entries.
    let mut symbol_ranges: Vec<(u64, u64)> = db
        .rel_iter::<(Address, usize, Symbol)>("symbol_size")
        .filter(|(_, size, _)| *size > 1)
        .map(|(addr, size, _)| (*addr, *addr + *size as u64))
        .collect();
    symbol_ranges.sort_by_key(|(start, _)| *start);
    let inside_existing_symbol = |addr: u64| -> bool {
        let idx = symbol_ranges.partition_point(|(start, _)| *start <= addr);
        idx > 0 && addr < symbol_ranges[idx - 1].1
    };

    // Build loadable address ranges from non-code ELF sections
    let data_ranges: Vec<(u64, u64)> = obj
        .sections()
        .filter_map(|s| {
            let addr = s.address();
            let size = s.size();
            if size == 0 || addr == 0 {
                return None;
            }
            let kind = s.kind();
            match kind {
                SectionKind::Text => return None,
                _ => {}
            }
            let sec_name = s.name().unwrap_or("");
            if sec_name.starts_with(".plt") || sec_name == ".init" || sec_name == ".fini" {
                return None;
            }
            Some((addr, addr + size))
        })
        .collect();

    let in_data_section = |addr: u64| -> bool {
        data_ranges.iter().any(|(start, end)| addr >= *start && addr < *end)
    };

    // Collect all referenced addresses from RIP-relative operands, relocations, and CFG edges
    let mut labeled: BTreeSet<u64> = BTreeSet::new();

    let mut rip_ops: HashSet<&'static str> = HashSet::new();
    let mut rip_op_disp: Vec<(&'static str, i64)> = Vec::new();
    let mut abs_ops: HashSet<&'static str> = HashSet::new();
    let mut abs_op_disp: Vec<(&'static str, i64)> = Vec::new();
    for (id, _seg, base, index, _scale, disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
        if base.ends_with("IP") {
            rip_ops.insert(*id);
            rip_op_disp.push((*id, *disp));
        } else if (*base == "NONE" || base.is_empty()) && (*index == "NONE" || index.is_empty()) && *disp > 0 {
            // Absolute addressing (clang -fno-pie): displacement is the address itself
            abs_ops.insert(*id);
            abs_op_disp.push((*id, *disp));
        } else if (*base == "NONE" || base.is_empty()) && *index != "NONE" && !index.is_empty() && *disp > 0 {
            // Scaled-index absolute addressing: mov dst, [reg*scale + const_addr] (clang const-table loads); the displacement is the table base address.
            abs_ops.insert(*id);
            abs_op_disp.push((*id, *disp));
        }
    }

    for (addr, size, _pfx, _mnem, op1, op2, op3, op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        for op_id in [op1, op2, op3, op4] {
            if *op_id == "0" { continue; }
            if rip_ops.contains(op_id) {
                for (rid, disp) in &rip_op_disp {
                    if *rid == *op_id {
                        let target = (*addr as i64 + *size as i64 + *disp) as u64;
                        if target > 0 && in_data_section(target) {
                            labeled.insert(target);
                        }
                        break;
                    }
                }
            }
            if abs_ops.contains(op_id) {
                for (rid, disp) in &abs_op_disp {
                    if *rid == *op_id {
                        // For absolute addressing, the displacement IS the target address
                        let target = *disp as u64;
                        if target > 0 && in_data_section(target) {
                            labeled.insert(target);
                        }
                        break;
                    }
                }
            }
        }
    }

    if let Some(dyn_relocs) = obj.dynamic_relocations() {
        for (offset, _reloc) in dyn_relocs {
            if offset > 0 && in_data_section(offset) {
                labeled.insert(offset);
            }
        }
    }

    let code_addrs: HashSet<u64> = db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction")
        .map(|(addr, ..)| *addr)
        .collect();

    for (_, target) in db.rel_iter::<(Address, Address)>("direct_jump") {
        if *target > 0 && code_addrs.contains(target) {
            labeled.insert(*target);
        }
    }
    for (_, target) in db.rel_iter::<(Address, Address)>("direct_call") {
        if *target > 0 && code_addrs.contains(target) {
            labeled.insert(*target);
        }
    }
    for (_, target, edge_type) in db.rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge") {
        if *edge_type == "branch" && *target > 0 && code_addrs.contains(target) {
            labeled.insert(*target);
        }
    }

    for (label, _content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        if let Some(hex) = label.strip_prefix("L_").or_else(|| label.strip_prefix(".L_")) {
            if let Ok(addr) = u64::from_str_radix(hex, 16) {
                if addr > 0 {
                    labeled.insert(addr);
                }
            }
        }
    }

    // Create .L_ entries for addresses without existing symbols
    let mut new_symbols: Vec<(u64, &'static str, &'static str)> = Vec::new();

    let existing_names: HashSet<u64> = db.rel_iter::<(Address, Symbol, Symbol)>("symbols").map(|(a, _, _)| *a).collect();
    for (name, addr) in db.rel_iter::<(Symbol, Address)>("func_entry") {
        if !existing_names.contains(addr) && name.starts_with("FUN_") {
            new_symbols.push((*addr, *name, "Beg"));
        }
    }

    for addr in &labeled {
        if !existing.contains(addr)
            && !plt_addrs.contains(addr)
            && !inside_existing_symbol(*addr)
            && !new_symbols.iter().any(|(a, _, _)| a == addr)
        {
            let name = leak(format!("L_{:x}", addr));
            new_symbols.push((*addr, name, "Beg"));
        }
    }

    let count = new_symbols.len();
    for entry in new_symbols {
        db.rel_push("symbols", entry);
    }

    log::info!("Labeled addresses: {} new symbols ({} total)",
             count, db.rel_iter::<(Address, Symbol, Symbol)>("symbols").count());

    // Build symbol_resolved_addr: maps symbol names to addresses (symbols override op_immediate, last-write-wins).
    let mut resolved_map: std::collections::BTreeMap<Symbol, Address> = std::collections::BTreeMap::new();
    for (sym, addr, _) in db.rel_iter::<(Symbol, i64, usize)>("op_immediate") {
        if *addr >= 0 {
            resolved_map.insert(*sym, *addr as Address);
        }
    }
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        resolved_map.insert(*name, *addr);
    }
    for (sym, addr) in &resolved_map {
        db.rel_push("symbol_resolved_addr", (*sym, *addr));
    }
}
