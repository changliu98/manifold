use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_pass::StackAddrOrigin;
use crate::x86::types::{Node, RTLReg};
use ascent::ascent_par;

// Canonicalize exact stack-address pointer authority only after RTL alias
// closure has settled. Feeding this projection back into RTL candidate
// construction would reintroduce the negation cycle that the raw authority was
// separated to avoid.
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct StackPtrCanonicalPassProgram;

    relation exact_stack_addr_ptr_result(Node, RTLReg);
    relation xtl_canonical(RTLReg, RTLReg);
    relation canonical_stack_addr_def_origin(Node, RTLReg, StackAddrOrigin);

    #[local] relation canonical_stack_addr_origin_member(RTLReg, StackAddrOrigin);
    canonical_stack_addr_origin_member(canonical, origin) <--
        canonical_stack_addr_def_origin(_, canonical, origin);

    #[local] relation canonical_stack_addr_origin_conflict(RTLReg);
    canonical_stack_addr_origin_conflict(canonical) <--
        canonical_stack_addr_origin_member(canonical, ?StackAddrOrigin::NonStack);
    canonical_stack_addr_origin_conflict(canonical) <--
        canonical_stack_addr_origin_member(canonical, ?StackAddrOrigin::Slot(left, left_width)),
        canonical_stack_addr_origin_member(canonical, ?StackAddrOrigin::Slot(right, right_width)),
        if left != right || left_width != right_width;

    relation canonical_exact_stack_addr_ptr_result(Node, RTLReg);
    canonical_exact_stack_addr_ptr_result(*node, *canonical) <--
        exact_stack_addr_ptr_result(node, raw),
        xtl_canonical(raw, canonical),
        canonical_stack_addr_origin_member(canonical, ?StackAddrOrigin::Slot(_, _)),
        !canonical_stack_addr_origin_conflict(canonical);
}

pub struct StackPtrCanonicalPass;

impl IRPass for StackPtrCanonicalPass {
    fn name(&self) -> &'static str {
        "stack_ptr_canonical"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = StackPtrCanonicalPassProgram::default();
        prog.swap_db_fields(db);
        prog.run();

        if db.measure_rule_times {
            let pass_name = "StackPtrCanonicalPassProgram".to_string();
            let summary = format!(
                "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
                prog.scc_times_summary(),
                prog.relation_sizes_summary(),
            );
            eprintln!(
                "[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]",
                pass_name, summary
            );
            db.rule_time_reports.push((pass_name, summary));
        }

        prog.swap_db_fields(db);
    }

    crate::declare_io_from!(StackPtrCanonicalPassProgram);
}

#[cfg(test)]
mod tests {
    use super::StackPtrCanonicalPassProgram;
    use crate::decompile::passes::rtl_pass::StackAddrOrigin;

    #[test]
    fn exact_stack_pointer_authority_follows_the_settled_alias_result() {
        let mut prog = StackPtrCanonicalPassProgram::default();
        let node = 0x1000_u64;
        let raw = 0x9000_u64;
        let canonical = 0x2000_u64;
        prog.exact_stack_addr_ptr_result.push((node, raw));
        prog.xtl_canonical.push((raw, canonical));
        prog.canonical_stack_addr_def_origin
            .push((node, canonical, StackAddrOrigin::Slot(-16, 8)));
        prog.run();
        assert!(prog
            .canonical_exact_stack_addr_ptr_result
            .iter()
            .any(|fact| fact == &(node, canonical)));
    }

    #[test]
    fn scalar_definition_in_canonical_web_vetoes_hard_stack_pointer() {
        let mut prog = StackPtrCanonicalPassProgram::default();
        let pointer_node = 0x1000_u64;
        let scalar_node = 0x2000_u64;
        let raw = 0x9000_u64;
        let canonical = 0x3000_u64;
        prog.exact_stack_addr_ptr_result.push((pointer_node, raw));
        prog.xtl_canonical.push((raw, canonical));
        prog.canonical_stack_addr_def_origin.extend([
            (pointer_node, canonical, StackAddrOrigin::Slot(-16, 8)),
            (scalar_node, canonical, StackAddrOrigin::NonStack),
        ]);

        prog.run();

        assert!(!prog
            .canonical_exact_stack_addr_ptr_result
            .iter()
            .any(|fact| fact == &(pointer_node, canonical)));
    }
}
