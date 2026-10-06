//! Immutable machine storage anchors, independent of recovered C objects.
//!
//! This pass deliberately does not infer escape or allocation. A decoded
//! frame-relative address exists even when raising later fails to give it a
//! representation. The refinement driver must account for these anchors;
//! absence of an escape candidate cannot erase the obligation.

use ascent::ascent_par;

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::mreg::Mreg;
use crate::x86::types::{Address, Node, Symbol};
use crate::{declare_io_from, run_pass};

pub(crate) fn register_bits(name: &str) -> Option<u32> {
    match name {
        "RAX" | "RBX" | "RCX" | "RDX" | "RSI" | "RDI" | "RBP" | "RSP" | "R8" | "R9" | "R10"
        | "R11" | "R12" | "R13" | "R14" | "R15" => Some(64),
        "EAX" | "EBX" | "ECX" | "EDX" | "ESI" | "EDI" | "EBP" | "ESP" | "R8D" | "R9D" | "R10D"
        | "R11D" | "R12D" | "R13D" | "R14D" | "R15D" => Some(32),
        "AX" | "BX" | "CX" | "DX" | "SI" | "DI" | "BP" | "SP" | "R8W" | "R9W" | "R10W" | "R11W"
        | "R12W" | "R13W" | "R14W" | "R15W" => Some(16),
        "AL" | "BL" | "CL" | "DL" | "AH" | "BH" | "CH" | "DH" | "SIL" | "DIL" | "BPL" | "SPL"
        | "R8B" | "R9B" | "R10B" | "R11B" | "R12B" | "R13B" | "R14B" | "R15B" => Some(8),
        _ => None,
    }
}

ascent_par! {
    #![measure_rule_times]
    #[swap_db]
    pub struct MachineStorageProgram;

    relation plea(Node, Symbol, Symbol);
    relation pmov(Node, Symbol, Symbol);
    relation padd(Node, Symbol, Symbol);
    relation op_register(Symbol, &'static str);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation instruction(Node, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation instr_in_function(Node, Address);

    // (function, anchor, raw SP displacement, scale, index, result, width).
    // Ownership/coordinate conflicts remain candidates here and are rejected
    // by the checker, not hidden by a high-recall producer.
    relation machine_frame_anchor(Address, Node, i64, i64, Option<Mreg>, Mreg, u32);
    machine_frame_anchor(*func, *node, *offset, *scale, Some(index), result, bits) <--
        plea(node, destination, memory),
        op_register(destination, result_name),
        if let Some(bits) = register_bits(result_name),
        let result = Mreg::x86(*result_name),
        op_indirect(memory, _, base, index_name, scale, offset, _),
        if *base == "RSP",
        if let Some(index_bits) = register_bits(index_name),
        if index_bits == 64,
        let index = Mreg::x86(*index_name),
        instr_in_function(node, func);

    machine_frame_anchor(*func, *node, *offset, 1, None, Mreg::x86(*result_name), bits) <--
        plea(node, destination, memory), op_register(destination, result_name),
        if let Some(bits) = register_bits(result_name),
        op_indirect(memory, _, base, index, _, offset, _),
        if *base == "RSP" && (index.is_empty() || *index == "NONE"),
        instr_in_function(node, func);

    machine_frame_anchor(*func, *node, 0, 1, None, Mreg::x86(*result_name), bits) <--
        pmov(node, destination, source), op_register(destination, result_name),
        if let Some(bits) = register_bits(result_name),
        op_register(source, source_name), if *source_name == "RSP",
        if Mreg::x86(*result_name) != Mreg::SP,
        instr_in_function(node, func);

    machine_frame_anchor(*func, *node, 0, 1, Some(result), result, bits) <--
        padd(node, destination, source), op_register(destination, result_name),
        if let Some(bits) = register_bits(result_name),
        let result = Mreg::x86(*result_name), if result != Mreg::SP,
        op_register(source, source_name), if *source_name == "RSP",
        instr_in_function(node, func);

    // Decoder destination views are separate from operation/value types.
    // In particular MOV eax,edi is not a 64-bit identity transfer.
    relation machine_register_write_view(Node, Mreg, u32);
    machine_register_write_view(*node, reg, bits) <--
        instruction(node, _, _, _, _, destination, _, _, _, _),
        op_register(destination, name),
        if let Some(bits) = register_bits(name),
        let reg = Mreg::x86(*name);

    // Physical comparison width is not CompCert's promoted Condition width.
    // In the normalized operand order, the destination is the CMP left side;
    // an immediate's encoding width never determines the compared bit-vector.
    #[local] relation machine_operand_bits(Symbol, u32);
    #[local] relation machine_high_byte_operand(Symbol);
    machine_high_byte_operand(*operand) <-- op_register(operand, name),
        if crate::decompile::passes::asm_pass::is_reg_high8(name);
    machine_operand_bits(*operand, bits) <-- op_register(operand, name),
        if let Some(bits) = register_bits(name);
    machine_operand_bits(*operand, (*bytes * 8) as u32) <--
        op_indirect(operand, _, _, _, _, _, bytes),
        if matches!(*bytes, 1 | 2 | 4 | 8);
    relation machine_comparison_view(Node, u32);
    machine_comparison_view(*node, *bits) <--
        instruction(node, _, _, "CMP", right, left, _, _, _, _),
        machine_operand_bits(left, bits),
        // This contract describes low bits. High-byte lanes need an explicit
        // lane mapping through normalized RTL registers, not just their width.
        !machine_high_byte_operand(left), !machine_high_byte_operand(right);

    // Storage width and register extension are separate machine facts. A
    // promoted Lgetstack(Tint) or an unsigned byte storage view says nothing
    // about whether the actual load sign-extends.
    relation machine_load_extension(Node, u32, u32, bool);
    machine_load_extension(*node, (*bytes * 8) as u32, output, signed) <--
        instruction(node, _, _, mnemonic, source, destination, _, _, _, _),
        op_indirect(source, _, _, _, _, _, bytes),
        if matches!(*bytes, 1 | 2 | 4 | 8),
        op_register(destination, name),
        if !crate::decompile::passes::asm_pass::is_reg_high8(name),
        if let Some(output) = register_bits(name),
        if let Some(signed) = match *mnemonic {
            "MOVSX" | "MOVSXD" if (*bytes * 8) < output as usize => Some(true),
            "MOVZX" if (*bytes * 8) < output as usize => Some(false),
            "MOV" if (*bytes * 8) == output as usize => Some(false),
            _ => None,
        };
}

pub struct MachineStoragePass;
impl IRPass for MachineStoragePass {
    fn name(&self) -> &'static str {
        "machine_storage_anchors"
    }
    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, MachineStorageProgram);
    }
    declare_io_from!(MachineStorageProgram);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comparison_and_load_views_come_from_encoded_operands() {
        let mut p = MachineStorageProgram::default();
        p.op_register
            .extend([("eax", "EAX"), ("rax", "RAX"), ("al", "AL"), ("ah", "AH")]);
        p.op_indirect.push(("byte", "", "RBP", "NONE", 0, -1, 1));
        for (node, mnemonic, source, destination) in [
            (10, "MOVSX", "byte", "eax"),
            (20, "MOVZX", "byte", "eax"),
            (30, "MOVSX", "byte", "rax"),
            (40, "MOV", "byte", "al"),
            (50, "CMP", "immediate", "byte"),
            (60, "CMP", "byte", "al"),
            (70, "CMP", "immediate", "rax"),
            (80, "CMP", "immediate", "ah"),
            (90, "CMP", "ah", "byte"),
            (100, "MOV", "byte", "ah"),
        ] {
            p.instruction
                .push((node, 3, "", mnemonic, source, destination, "", "", 0, 0));
        }
        p.run();
        let loads: std::collections::BTreeSet<_> = p.machine_load_extension.into_iter().collect();
        assert_eq!(
            loads,
            [
                (10, 8, 32, true),
                (20, 8, 32, false),
                (30, 8, 64, true),
                (40, 8, 8, false)
            ]
            .into()
        );
        let comparisons: std::collections::BTreeSet<_> =
            p.machine_comparison_view.into_iter().collect();
        assert_eq!(comparisons, [(50, 8), (60, 8), (70, 64)].into());
    }

    #[test]
    fn plain_and_composed_frame_addresses_do_not_depend_on_indexed_lea_syntax() {
        let mut p = MachineStorageProgram::default();
        p.op_register.extend([("dst", "RDI"), ("sp", "RSP")]);
        p.op_indirect.push(("plain", "", "RSP", "NONE", 0, 8, 8));
        p.plea.push((10, "dst", "plain"));
        p.pmov.push((20, "dst", "sp"));
        p.padd.push((30, "dst", "sp"));
        p.padd.push((40, "sp", "dst"));
        p.instr_in_function
            .extend([(10, 1), (20, 1), (30, 1), (40, 1)]);
        p.run();
        assert!(p
            .machine_frame_anchor
            .iter()
            .any(|r| r == &(1, 10, 8, 1, None, Mreg::DI, 64)));
        assert!(p
            .machine_frame_anchor
            .iter()
            .any(|r| r == &(1, 20, 0, 1, None, Mreg::DI, 64)));
        assert!(p
            .machine_frame_anchor
            .iter()
            .any(|r| r == &(1, 30, 0, 1, Some(Mreg::DI), Mreg::DI, 64)));
        assert!(!p.machine_frame_anchor.iter().any(|r| r.1 == 40));
    }

    #[test]
    fn an_anchor_does_not_require_an_escape_or_rtl_candidate() {
        let mut p = MachineStorageProgram::default();
        p.plea.push((10, "dst", "mem"));
        p.op_register.push(("dst", "RSI"));
        p.op_indirect.push(("mem", "", "RSP", "RAX", 4, 8, 8));
        p.instr_in_function.push((10, 100));
        p.run();
        assert_eq!(p.machine_frame_anchor.len(), 1);
        assert_eq!(
            p.machine_frame_anchor[0],
            (100, 10, 8, 4, Some(Mreg::AX), Mreg::SI, 64)
        );
    }

    #[test]
    fn narrow_addresses_and_superposed_owners_remain_visible_to_the_checker() {
        let mut p = MachineStorageProgram::default();
        p.plea.push((900, "dst", "mem"));
        p.op_register.push(("dst", "ESI"));
        p.op_indirect.push(("mem", "", "RSP", "RAX", 1, 0, 4));
        p.instr_in_function.extend([(900, 1), (900, 2)]);
        p.run();
        assert_eq!(p.machine_frame_anchor.len(), 2);
        assert!(p.machine_frame_anchor.iter().all(|r| r.6 == 32));
    }
}
