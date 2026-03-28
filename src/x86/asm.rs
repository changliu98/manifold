



#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ireg {
    RAX,
    RBX,
    RCX,
    RDX,
    RSI,
    RDI,
    RBP,
    RSP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    RIP,
    Unknown,
}

impl From<&str> for Ireg {
    fn from(s: &str) -> Self {
        let s_in = s.trim();
        let s_in = if s_in.starts_with('%') {
            &s_in[1..]
        } else {
            s_in
        }
        .to_lowercase();

        match s_in.as_str() {
            "rax" | "eax" | "ax" | "al" | "ah" => Ireg::RAX,
            "rbx" | "ebx" | "bx" | "bl" | "bh" => Ireg::RBX,
            "rcx" | "ecx" | "cx" | "cl" | "ch" => Ireg::RCX,
            "rdx" | "edx" | "dx" | "dl" | "dh" => Ireg::RDX,
            "rsi" | "esi" | "si" | "sil" => Ireg::RSI,
            "rdi" | "edi" | "di" | "dil" => Ireg::RDI,
            "rbp" | "ebp" | "bp" | "bpl" => Ireg::RBP,
            "rsp" | "esp" | "sp" | "spl" => Ireg::RSP,
            "r8" | "r8d" | "r8w" | "r8b" => Ireg::R8,
            "r9" | "r9d" | "r9w" | "r9b" => Ireg::R9,
            "r10" | "r10d" | "r10w" | "r10b" => Ireg::R10,
            "r11" | "r11d" | "r11w" | "r11b" => Ireg::R11,
            "r12" | "r12d" | "r12w" | "r12b" => Ireg::R12,
            "r13" | "r13d" | "r13w" | "r13b" => Ireg::R13,
            "r14" | "r14d" | "r14w" | "r14b" => Ireg::R14,
            "r15" | "r15d" | "r15w" | "r15b" => Ireg::R15,
            "rip" | "eip" | "ip" => Ireg::RIP,
            _ => Ireg::Unknown,
        }
    }
}

impl From<String> for Ireg {
    fn from(s: String) -> Self {
        Ireg::from(s.as_str())
    }
}

impl From<&&str> for Ireg {
    fn from(s: &&str) -> Self {
        Ireg::from(*s)
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Freg {
    XMM0,
    XMM1,
    XMM2,
    XMM3,
    XMM4,
    XMM5,
    XMM6,
    XMM7,
    XMM8,
    XMM9,
    XMM10,
    XMM11,
    XMM12,
    XMM13,
    XMM14,
    XMM15,
    #[allow(dead_code)]
    Unknown,
}
impl From<String> for Freg {
    fn from(s: String) -> Self {
        match s.as_str() {
            "XMM0" => Freg::XMM0,
            "XMM1" => Freg::XMM1,
            "XMM2" => Freg::XMM2,
            "XMM3" => Freg::XMM3,
            "XMM4" => Freg::XMM4,
            "XMM5" => Freg::XMM5,
            "XMM6" => Freg::XMM6,
            "XMM7" => Freg::XMM7,
            "XMM8" => Freg::XMM8,
            "XMM9" => Freg::XMM9,
            "XMM10" => Freg::XMM10,
            "XMM11" => Freg::XMM11,
            "XMM12" => Freg::XMM12,
            "XMM13" => Freg::XMM13,
            "XMM14" => Freg::XMM14,
            "XMM15" => Freg::XMM15,
            "%xmm0" => Freg::XMM0,
            "%xmm1" => Freg::XMM1,
            "%xmm2" => Freg::XMM2,
            "%xmm3" => Freg::XMM3,
            "%xmm4" => Freg::XMM4,
            "%xmm5" => Freg::XMM5,
            "%xmm6" => Freg::XMM6,
            "%xmm7" => Freg::XMM7,
            "%xmm8" => Freg::XMM8,
            "%xmm9" => Freg::XMM9,
            "%xmm10" => Freg::XMM10,
            "%xmm11" => Freg::XMM11,
            "%xmm12" => Freg::XMM12,
            "%xmm13" => Freg::XMM13,
            "%xmm14" => Freg::XMM14,
            "%xmm15" => Freg::XMM15,
            _ => panic!("Invalid register name"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Crbit {
    #[allow(dead_code)]
    Ceq,
    #[allow(dead_code)]
    Cne,
    #[allow(dead_code)]
    Clt,
    #[allow(dead_code)]
    Cle,
    #[allow(dead_code)]
    Cgt,
    #[allow(dead_code)]
    Cge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Preg {
    #[allow(dead_code)]
    PC,
    Ir(Ireg),
    Fr(Freg),
    ST0,
    Cr(Crbit),
    #[allow(dead_code)]
    RA,
}


impl From<Ireg> for Preg {
    fn from(ireg: Ireg) -> Preg {
        Preg::Ir(ireg)
    }
}

impl From<Freg> for Preg {
    fn from(freg: Freg) -> Preg {
        Preg::Fr(freg)
    }
}

impl From<Crbit> for Preg {
    fn from(crbit: Crbit) -> Preg {
        Preg::Cr(crbit)
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TestCond {
    CondE,
    CondNe,
    CondB,
    CondBe,
    CondAe,
    CondA,
    CondL,
    CondLe,
    CondGe,
    CondG,
    CondP,
    CondNp,
    #[allow(dead_code)]
    Unknown,
}
