// AArch64 machine registers in assembly spelling (X0..X30, V0..V31); ZR is its own variant, load-bearing for MOV/CMP/CSET normalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum A64Mreg {
    X0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    X16,
    X17,
    X18,
    X19,
    X20,
    X21,
    X22,
    X23,
    X24,
    X25,
    X26,
    X27,
    X28,
    X29,
    X30,
    SP,
    ZR,
    V0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    V10,
    V11,
    V12,
    V13,
    V14,
    V15,
    V16,
    V17,
    V18,
    V19,
    V20,
    V21,
    V22,
    V23,
    V24,
    V25,
    V26,
    V27,
    V28,
    V29,
    V30,
    V31,
    Unknown,
}

const GP: [A64Mreg; 31] = [
    A64Mreg::X0,
    A64Mreg::X1,
    A64Mreg::X2,
    A64Mreg::X3,
    A64Mreg::X4,
    A64Mreg::X5,
    A64Mreg::X6,
    A64Mreg::X7,
    A64Mreg::X8,
    A64Mreg::X9,
    A64Mreg::X10,
    A64Mreg::X11,
    A64Mreg::X12,
    A64Mreg::X13,
    A64Mreg::X14,
    A64Mreg::X15,
    A64Mreg::X16,
    A64Mreg::X17,
    A64Mreg::X18,
    A64Mreg::X19,
    A64Mreg::X20,
    A64Mreg::X21,
    A64Mreg::X22,
    A64Mreg::X23,
    A64Mreg::X24,
    A64Mreg::X25,
    A64Mreg::X26,
    A64Mreg::X27,
    A64Mreg::X28,
    A64Mreg::X29,
    A64Mreg::X30,
];

const VEC: [A64Mreg; 32] = [
    A64Mreg::V0,
    A64Mreg::V1,
    A64Mreg::V2,
    A64Mreg::V3,
    A64Mreg::V4,
    A64Mreg::V5,
    A64Mreg::V6,
    A64Mreg::V7,
    A64Mreg::V8,
    A64Mreg::V9,
    A64Mreg::V10,
    A64Mreg::V11,
    A64Mreg::V12,
    A64Mreg::V13,
    A64Mreg::V14,
    A64Mreg::V15,
    A64Mreg::V16,
    A64Mreg::V17,
    A64Mreg::V18,
    A64Mreg::V19,
    A64Mreg::V20,
    A64Mreg::V21,
    A64Mreg::V22,
    A64Mreg::V23,
    A64Mreg::V24,
    A64Mreg::V25,
    A64Mreg::V26,
    A64Mreg::V27,
    A64Mreg::V28,
    A64Mreg::V29,
    A64Mreg::V30,
    A64Mreg::V31,
];

impl A64Mreg {
    /// GP register by number; X31 is not a GP register (SP or ZR by context), so callers must resolve it first.
    pub fn gp(n: u8) -> Self {
        GP.get(n as usize).copied().unwrap_or(A64Mreg::Unknown)
    }

    /// FP/SIMD register by number, for any view width (Vn/Qn/Dn/Sn/Hn/Bn).
    pub fn vec(n: u8) -> Self {
        VEC.get(n as usize).copied().unwrap_or(A64Mreg::Unknown)
    }

    /// Canonical 64-bit name ("X0".."X30", "SP", "ZR", "V0".."V31"), normalizing capstone's aliases (FP/LR/ZR) and width views (W0, D3, S3).
    pub fn name(&self) -> &'static str {
        const GP_NAMES: [&str; 31] = [
            "X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7", "X8", "X9", "X10", "X11", "X12", "X13",
            "X14", "X15", "X16", "X17", "X18", "X19", "X20", "X21", "X22", "X23", "X24", "X25",
            "X26", "X27", "X28", "X29", "X30",
        ];
        const V_NAMES: [&str; 32] = [
            "V0", "V1", "V2", "V3", "V4", "V5", "V6", "V7", "V8", "V9", "V10", "V11", "V12", "V13",
            "V14", "V15", "V16", "V17", "V18", "V19", "V20", "V21", "V22", "V23", "V24", "V25",
            "V26", "V27", "V28", "V29", "V30", "V31",
        ];
        match self {
            A64Mreg::SP => "SP",
            A64Mreg::ZR => "ZR",
            A64Mreg::Unknown => "NONE",
            r if r.is_gp() => GP_NAMES[GP.iter().position(|g| g == r).unwrap()],
            r => V_NAMES[VEC.iter().position(|v| v == r).unwrap()],
        }
    }

    pub fn is_gp(&self) -> bool {
        GP.contains(self)
    }

    pub fn is_vec(&self) -> bool {
        VEC.contains(self)
    }

    /// Dense 0-based index over the register file for the fresh_xtl_reg discriminant: GP 0..30, SP 31, ZR 32, V0..V31 33..64, Unknown 65.
    pub fn index(&self) -> u64 {
        match self {
            A64Mreg::SP => 31,
            A64Mreg::ZR => 32,
            A64Mreg::Unknown => 65,
            r if r.is_gp() => GP.iter().position(|g| g == r).unwrap() as u64,
            r => 33 + VEC.iter().position(|v| v == r).unwrap() as u64,
        }
    }
}

impl From<&str> for A64Mreg {
    fn from(s: &str) -> Self {
        let u = s.trim().to_ascii_uppercase();
        let u = u.strip_prefix("A64.").unwrap_or(&u);

        // Architectural aliases first: these carry meaning no width-view parse would.
        match u {
            "SP" | "WSP" => return A64Mreg::SP,
            "XZR" | "WZR" | "ZR" => return A64Mreg::ZR,
            "FP" => return A64Mreg::X29,
            "LR" => return A64Mreg::X30,
            "UNKNOWN" => return A64Mreg::Unknown,
            _ => {}
        }

        let (tag, digits) = u.split_at(1.min(u.len()));
        let n: u8 = match digits.parse() {
            Ok(n) => n,
            Err(_) => return A64Mreg::Unknown,
        };
        match tag {
            // Xn is the 64-bit view, Wn the 32-bit view, of one GP register.
            "X" | "W" => A64Mreg::gp(n),
            // Vn/Qn/Dn/Sn/Hn/Bn are width views of one FP/SIMD register.
            "V" | "Q" | "D" | "S" | "H" | "B" => A64Mreg::vec(n),
            _ => A64Mreg::Unknown,
        }
    }
}

impl From<String> for A64Mreg {
    fn from(s: String) -> Self {
        A64Mreg::from(s.as_str())
    }
}

impl From<&String> for A64Mreg {
    fn from(s: &String) -> Self {
        A64Mreg::from(s.as_str())
    }
}

impl From<&&str> for A64Mreg {
    fn from(s: &&str) -> Self {
        A64Mreg::from(*s)
    }
}

impl ToString for A64Mreg {
    fn to_string(&self) -> String {
        // The "A64." prefix keeps these disjoint from x86's "Machregs.*" strings, so a string round-trip cannot cross register files.
        match self {
            A64Mreg::SP => "A64.SP".to_string(),
            A64Mreg::ZR => "A64.ZR".to_string(),
            A64Mreg::Unknown => "A64.Unknown".to_string(),
            r if r.is_gp() => format!("A64.X{}", GP.iter().position(|g| g == r).unwrap()),
            r => format!("A64.V{}", VEC.iter().position(|v| v == r).unwrap()),
        }
    }
}
