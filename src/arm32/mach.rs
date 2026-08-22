// ARM32 (A32) machine registers in assembly spelling (R0..R15 plus the VFP file); PC is its own variant, load-bearing because A32 writes it as an ordinary destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum A32Mreg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    SP,
    LR,
    PC,
    // VFP single-precision view. S(2n)/S(2n+1) are architecturally the halves of D(n), an overlap this file does not model; see the note on the D variants.
    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    S12,
    S13,
    S14,
    S15,
    S16,
    S17,
    S18,
    S19,
    S20,
    S21,
    S22,
    S23,
    S24,
    S25,
    S26,
    S27,
    S28,
    S29,
    S30,
    S31,
    // VFP/NEON double-precision view. Kept disjoint from the S variants: folding S onto D would make S0 and S1 the same register and merge two distinct single-precision values, which is unsound in the direction that corrupts dataflow. Single- and double-precision code does not mix views within one value, so the missed alias is the safe residue.
    D0,
    D1,
    D2,
    D3,
    D4,
    D5,
    D6,
    D7,
    D8,
    D9,
    D10,
    D11,
    D12,
    D13,
    D14,
    D15,
    D16,
    D17,
    D18,
    D19,
    D20,
    D21,
    D22,
    D23,
    D24,
    D25,
    D26,
    D27,
    D28,
    D29,
    D30,
    D31,
    // NEON quadword view, disjoint from D for the same reason.
    Q0,
    Q1,
    Q2,
    Q3,
    Q4,
    Q5,
    Q6,
    Q7,
    Q8,
    Q9,
    Q10,
    Q11,
    Q12,
    Q13,
    Q14,
    Q15,
    Unknown,
}

const GP: [A32Mreg; 16] = [
    A32Mreg::R0,
    A32Mreg::R1,
    A32Mreg::R2,
    A32Mreg::R3,
    A32Mreg::R4,
    A32Mreg::R5,
    A32Mreg::R6,
    A32Mreg::R7,
    A32Mreg::R8,
    A32Mreg::R9,
    A32Mreg::R10,
    A32Mreg::R11,
    A32Mreg::R12,
    A32Mreg::SP,
    A32Mreg::LR,
    A32Mreg::PC,
];

const S: [A32Mreg; 32] = [
    A32Mreg::S0,
    A32Mreg::S1,
    A32Mreg::S2,
    A32Mreg::S3,
    A32Mreg::S4,
    A32Mreg::S5,
    A32Mreg::S6,
    A32Mreg::S7,
    A32Mreg::S8,
    A32Mreg::S9,
    A32Mreg::S10,
    A32Mreg::S11,
    A32Mreg::S12,
    A32Mreg::S13,
    A32Mreg::S14,
    A32Mreg::S15,
    A32Mreg::S16,
    A32Mreg::S17,
    A32Mreg::S18,
    A32Mreg::S19,
    A32Mreg::S20,
    A32Mreg::S21,
    A32Mreg::S22,
    A32Mreg::S23,
    A32Mreg::S24,
    A32Mreg::S25,
    A32Mreg::S26,
    A32Mreg::S27,
    A32Mreg::S28,
    A32Mreg::S29,
    A32Mreg::S30,
    A32Mreg::S31,
];

const D: [A32Mreg; 32] = [
    A32Mreg::D0,
    A32Mreg::D1,
    A32Mreg::D2,
    A32Mreg::D3,
    A32Mreg::D4,
    A32Mreg::D5,
    A32Mreg::D6,
    A32Mreg::D7,
    A32Mreg::D8,
    A32Mreg::D9,
    A32Mreg::D10,
    A32Mreg::D11,
    A32Mreg::D12,
    A32Mreg::D13,
    A32Mreg::D14,
    A32Mreg::D15,
    A32Mreg::D16,
    A32Mreg::D17,
    A32Mreg::D18,
    A32Mreg::D19,
    A32Mreg::D20,
    A32Mreg::D21,
    A32Mreg::D22,
    A32Mreg::D23,
    A32Mreg::D24,
    A32Mreg::D25,
    A32Mreg::D26,
    A32Mreg::D27,
    A32Mreg::D28,
    A32Mreg::D29,
    A32Mreg::D30,
    A32Mreg::D31,
];

const Q: [A32Mreg; 16] = [
    A32Mreg::Q0,
    A32Mreg::Q1,
    A32Mreg::Q2,
    A32Mreg::Q3,
    A32Mreg::Q4,
    A32Mreg::Q5,
    A32Mreg::Q6,
    A32Mreg::Q7,
    A32Mreg::Q8,
    A32Mreg::Q9,
    A32Mreg::Q10,
    A32Mreg::Q11,
    A32Mreg::Q12,
    A32Mreg::Q13,
    A32Mreg::Q14,
    A32Mreg::Q15,
];

const GP_NAMES: [&str; 16] = [
    "R0", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11", "R12", "SP", "LR",
    "PC",
];

impl A32Mreg {
    /// GP register by number, 0..=15; R13/R14/R15 answer as SP/LR/PC, which is what every consumer tests.
    pub fn gp(n: u8) -> Self {
        GP.get(n as usize).copied().unwrap_or(A32Mreg::Unknown)
    }

    /// VFP single-precision register by number.
    pub fn s(n: u8) -> Self {
        S.get(n as usize).copied().unwrap_or(A32Mreg::Unknown)
    }

    /// VFP/NEON double-precision register by number.
    pub fn d(n: u8) -> Self {
        D.get(n as usize).copied().unwrap_or(A32Mreg::Unknown)
    }

    /// NEON quadword register by number.
    pub fn q(n: u8) -> Self {
        Q.get(n as usize).copied().unwrap_or(A32Mreg::Unknown)
    }

    /// Canonical name ("R0".."R12", "SP", "LR", "PC", "S0".., "D0.."), normalizing capstone's aliases (FP/IP/R13/R14/R15).
    pub fn name(&self) -> &'static str {
        const S_NAMES: [&str; 32] = [
            "S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11", "S12", "S13",
            "S14", "S15", "S16", "S17", "S18", "S19", "S20", "S21", "S22", "S23", "S24", "S25",
            "S26", "S27", "S28", "S29", "S30", "S31",
        ];
        const D_NAMES: [&str; 32] = [
            "D0", "D1", "D2", "D3", "D4", "D5", "D6", "D7", "D8", "D9", "D10", "D11", "D12", "D13",
            "D14", "D15", "D16", "D17", "D18", "D19", "D20", "D21", "D22", "D23", "D24", "D25",
            "D26", "D27", "D28", "D29", "D30", "D31",
        ];
        const Q_NAMES: [&str; 16] = [
            "Q0", "Q1", "Q2", "Q3", "Q4", "Q5", "Q6", "Q7", "Q8", "Q9", "Q10", "Q11", "Q12", "Q13",
            "Q14", "Q15",
        ];
        match self {
            A32Mreg::Unknown => "NONE",
            r if r.is_gp() => GP_NAMES[GP.iter().position(|g| g == r).unwrap()],
            r if r.is_single() => S_NAMES[S.iter().position(|s| s == r).unwrap()],
            r if r.is_double() => D_NAMES[D.iter().position(|d| d == r).unwrap()],
            r => Q_NAMES[Q.iter().position(|q| q == r).unwrap()],
        }
    }

    pub fn is_gp(&self) -> bool {
        GP.contains(self)
    }

    pub fn is_single(&self) -> bool {
        S.contains(self)
    }

    pub fn is_double(&self) -> bool {
        D.contains(self)
    }

    pub fn is_quad(&self) -> bool {
        Q.contains(self)
    }

    /// True for any VFP/NEON register, in any width view.
    pub fn is_vec(&self) -> bool {
        self.is_single() || self.is_double() || self.is_quad()
    }

    /// Dense 0-based index over the register file for the fresh_xtl_reg discriminant: GP 0..15, S 16..47, D 48..79, Q 80..95, Unknown 96.
    pub fn index(&self) -> u64 {
        match self {
            A32Mreg::Unknown => 96,
            r if r.is_gp() => GP.iter().position(|g| g == r).unwrap() as u64,
            r if r.is_single() => 16 + S.iter().position(|s| s == r).unwrap() as u64,
            r if r.is_double() => 48 + D.iter().position(|d| d == r).unwrap() as u64,
            r => 80 + Q.iter().position(|q| q == r).unwrap() as u64,
        }
    }
}

impl From<&str> for A32Mreg {
    fn from(s: &str) -> Self {
        let u = s.trim().to_ascii_uppercase();
        let u = u.strip_prefix("A32.").unwrap_or(&u);

        // Architectural aliases first: these carry meaning no numeric parse would.
        match u {
            "SP" | "R13" => return A32Mreg::SP,
            "LR" | "R14" => return A32Mreg::LR,
            "PC" | "R15" => return A32Mreg::PC,
            // AAPCS names capstone prints for R11 and R12.
            "FP" => return A32Mreg::R11,
            "IP" => return A32Mreg::R12,
            // The AAPCS static base and thread register, spelled by number elsewhere.
            "SB" => return A32Mreg::R9,
            "SL" => return A32Mreg::R10,
            "UNKNOWN" => return A32Mreg::Unknown,
            _ => {}
        }

        let (tag, digits) = u.split_at(1.min(u.len()));
        let n: u8 = match digits.parse() {
            Ok(n) => n,
            Err(_) => return A32Mreg::Unknown,
        };
        match tag {
            "R" => A32Mreg::gp(n),
            "S" => A32Mreg::s(n),
            "D" => A32Mreg::d(n),
            "Q" => A32Mreg::q(n),
            _ => A32Mreg::Unknown,
        }
    }
}

impl From<String> for A32Mreg {
    fn from(s: String) -> Self {
        A32Mreg::from(s.as_str())
    }
}

impl From<&String> for A32Mreg {
    fn from(s: &String) -> Self {
        A32Mreg::from(s.as_str())
    }
}

impl From<&&str> for A32Mreg {
    fn from(s: &&str) -> Self {
        A32Mreg::from(*s)
    }
}

impl ToString for A32Mreg {
    fn to_string(&self) -> String {
        // The "A32." prefix keeps these disjoint from x86's "Machregs.*" and AArch64's "A64.*" strings, so a string round-trip cannot cross register files.
        format!("A32.{}", self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capstone_aliases_normalize_onto_the_architectural_register() {
        assert_eq!(A32Mreg::from("r13"), A32Mreg::SP);
        assert_eq!(A32Mreg::from("sp"), A32Mreg::SP);
        assert_eq!(A32Mreg::from("r14"), A32Mreg::LR);
        assert_eq!(A32Mreg::from("lr"), A32Mreg::LR);
        assert_eq!(A32Mreg::from("r15"), A32Mreg::PC);
        assert_eq!(A32Mreg::from("pc"), A32Mreg::PC);
        assert_eq!(A32Mreg::from("fp"), A32Mreg::R11);
        assert_eq!(A32Mreg::from("ip"), A32Mreg::R12);
        assert_eq!(A32Mreg::from("R0"), A32Mreg::R0);
        assert_eq!(A32Mreg::from("cpsr"), A32Mreg::Unknown);
        assert_eq!(A32Mreg::from("r16"), A32Mreg::Unknown);
    }

    #[test]
    fn the_string_round_trip_stays_inside_this_register_file() {
        for r in GP.iter().chain(S.iter()).chain(D.iter()).chain(Q.iter()) {
            let s = r.to_string();
            assert!(s.starts_with("A32."), "{s} must be namespaced");
            assert_eq!(A32Mreg::from(s.as_str()), *r, "round trip of {s}");
        }
    }

    #[test]
    fn indices_are_dense_and_distinct() {
        let mut seen: Vec<u64> = GP
            .iter()
            .chain(S.iter())
            .chain(D.iter())
            .chain(Q.iter())
            .map(|r| r.index())
            .collect();
        seen.push(A32Mreg::Unknown.index());
        let n = seen.len();
        seen.sort();
        seen.dedup();
        assert_eq!(seen.len(), n, "register indices must be distinct");
        assert_eq!(seen, (0..n as u64).collect::<Vec<_>>(), "and dense from 0");
    }

    // The width views are deliberately disjoint: merging them would alias two live values.
    #[test]
    fn single_and_double_views_are_distinct_registers() {
        assert_ne!(A32Mreg::from("s0"), A32Mreg::from("d0"));
        assert_ne!(A32Mreg::from("s0"), A32Mreg::from("s1"));
    }
}
