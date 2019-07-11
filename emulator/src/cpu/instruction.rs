#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BasicOp {
    SET,
    ADD,
    SUB,
    MUL,
    MLI,
    DIV,
    DVI,
    MOD,
    MDI,
    AND,
    BOR,
    XOR,
    SHR,
    ASR,
    SHL,
    IFB,
    IFC,
    IFE,
    IFN,
    IFG,
    IFA,
    IFL,
    IFU,
    ADX,
    SBX,
    STI,
    STD,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SpecialOp {
    JSR,
    INT,
    IAG,
    IAS,
    RFI,
    IAQ,
    HWN,
    HWQ,
    HWI,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Instruction {
    Basic(BasicInstruction),
    Special(SpecialInstruction),
}

impl Instruction {
    pub fn get_a(&self) -> &Operand {
        match self {
            Instruction::Basic(basic) => &basic.a,
            Instruction::Special(special) => &special.a,
        }
    }
}
pub mod visitor {
    use super::*;

    pub trait InstructionVisitor {
        // Basic instructions.
        fn visit_set(&mut self, b: &Operand, a: &Operand);
        fn visit_add(&mut self, b: &Operand, a: &Operand);
        fn visit_sub(&mut self, b: &Operand, a: &Operand);
        fn visit_mul(&mut self, b: &Operand, a: &Operand);
        fn visit_mli(&mut self, b: &Operand, a: &Operand);
        fn visit_div(&mut self, b: &Operand, a: &Operand);
        fn visit_dvi(&mut self, b: &Operand, a: &Operand);
        fn visit_mod(&mut self, b: &Operand, a: &Operand);
        fn visit_mdi(&mut self, b: &Operand, a: &Operand);
        fn visit_and(&mut self, b: &Operand, a: &Operand);
        fn visit_bor(&mut self, b: &Operand, a: &Operand);
        fn visit_xor(&mut self, b: &Operand, a: &Operand);
        fn visit_shr(&mut self, b: &Operand, a: &Operand);
        fn visit_asr(&mut self, b: &Operand, a: &Operand);
        fn visit_shl(&mut self, b: &Operand, a: &Operand);
        fn visit_ifb(&mut self, b: &Operand, a: &Operand);
        fn visit_ifc(&mut self, b: &Operand, a: &Operand);
        fn visit_ife(&mut self, b: &Operand, a: &Operand);
        fn visit_ifn(&mut self, b: &Operand, a: &Operand);
        fn visit_ifg(&mut self, b: &Operand, a: &Operand);
        fn visit_ifa(&mut self, b: &Operand, a: &Operand);
        fn visit_ifl(&mut self, b: &Operand, a: &Operand);
        fn visit_ifu(&mut self, b: &Operand, a: &Operand);
        fn visit_adx(&mut self, b: &Operand, a: &Operand);
        fn visit_sbx(&mut self, b: &Operand, a: &Operand);
        fn visit_sti(&mut self, b: &Operand, a: &Operand);
        fn visit_std(&mut self, b: &Operand, a: &Operand);

        // Special instructions.
        fn visit_jsr(&mut self, a: &Operand);
        fn visit_int(&mut self, a: &Operand);
        fn visit_iag(&mut self, a: &Operand);
        fn visit_ias(&mut self, a: &Operand);
        fn visit_rfi(&mut self, a: &Operand);
        fn visit_iaq(&mut self, a: &Operand);
        fn visit_hwn(&mut self, a: &Operand);
        fn visit_hwq(&mut self, a: &Operand);
        fn visit_hwi(&mut self, a: &Operand);

        fn visit(&mut self, inst: &Instruction) {
            match inst {
                Instruction::Basic(inst) => match inst.op {
                    BasicOp::SET => {
                        self.visit_set(&inst.b, &inst.a);
                    }
                    BasicOp::ADD => {
                        self.visit_add(&inst.b, &inst.a);
                    }
                    BasicOp::SUB => {
                        self.visit_sub(&inst.b, &inst.a);
                    }
                    BasicOp::MUL => {
                        self.visit_mul(&inst.b, &inst.a);
                    }
                    BasicOp::MLI => {
                        self.visit_mli(&inst.b, &inst.a);
                    }
                    BasicOp::DIV => {
                        self.visit_div(&inst.b, &inst.a);
                    }
                    BasicOp::DVI => {
                        self.visit_dvi(&inst.b, &inst.a);
                    }
                    BasicOp::MOD => {
                        self.visit_mod(&inst.b, &inst.a);
                    }
                    BasicOp::MDI => {
                        self.visit_mdi(&inst.b, &inst.a);
                    }
                    BasicOp::AND => {
                        self.visit_and(&inst.b, &inst.a);
                    }
                    BasicOp::BOR => {
                        self.visit_bor(&inst.b, &inst.a);
                    }
                    BasicOp::XOR => {
                        self.visit_xor(&inst.b, &inst.a);
                    }
                    BasicOp::SHR => {
                        self.visit_shr(&inst.b, &inst.a);
                    }
                    BasicOp::ASR => {
                        self.visit_asr(&inst.b, &inst.a);
                    }
                    BasicOp::SHL => {
                        self.visit_shl(&inst.b, &inst.a);
                    }
                    BasicOp::IFB => {
                        self.visit_ifb(&inst.b, &inst.a);
                    }
                    BasicOp::IFC => {
                        self.visit_ifc(&inst.b, &inst.a);
                    }
                    BasicOp::IFE => {
                        self.visit_ife(&inst.b, &inst.a);
                    }
                    BasicOp::IFN => {
                        self.visit_ifn(&inst.b, &inst.a);
                    }
                    BasicOp::IFG => {
                        self.visit_ifg(&inst.b, &inst.a);
                    }
                    BasicOp::IFA => {
                        self.visit_ifa(&inst.b, &inst.a);
                    }
                    BasicOp::IFL => {
                        self.visit_ifl(&inst.b, &inst.a);
                    }
                    BasicOp::IFU => {
                        self.visit_ifu(&inst.b, &inst.a);
                    }
                    BasicOp::ADX => {
                        self.visit_adx(&inst.b, &inst.a);
                    }
                    BasicOp::SBX => {
                        self.visit_sbx(&inst.b, &inst.a);
                    }
                    BasicOp::STI => {
                        self.visit_sti(&inst.b, &inst.a);
                    }
                    BasicOp::STD => {
                        self.visit_std(&inst.b, &inst.a);
                    }
                },
                Instruction::Special(inst) => match inst.op {
                    SpecialOp::JSR => {
                        self.visit_jsr(&inst.a);
                    }
                    SpecialOp::INT => self.visit_int(&inst.a),
                    SpecialOp::IAG => self.visit_iag(&inst.a),
                    SpecialOp::IAS => self.visit_ias(&inst.a),
                    SpecialOp::RFI => self.visit_rfi(&inst.a),
                    SpecialOp::IAQ => self.visit_iaq(&inst.a),
                    SpecialOp::HWN => self.visit_hwn(&inst.a),
                    SpecialOp::HWQ => self.visit_hwq(&inst.a),
                    SpecialOp::HWI => self.visit_hwi(&inst.a),
                },
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Register {
    A,
    B,
    C,
    X,
    Y,
    Z,
    I,
    J,
    SP,
    PC,
    EX,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    NextWordAsAddress,
    NextWordAsLiteral,
    Literal(i8),
    Register(Register),
    InRegisterAsAddress(Register),
    InRegisterAsAddressPlusNextWord(Register),
    PushOrPop,
    Peek,
    Pick,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BasicInstruction {
    pub op: BasicOp,
    pub b: Operand,
    pub a: Operand,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SpecialInstruction {
    pub op: SpecialOp,
    pub a: Operand,
}

#[derive(Debug)]
pub enum Error {
    BadInstruction,
}

impl std::convert::TryFrom<u16> for BasicInstruction {
    type Error = Error;
    fn try_from(val: u16) -> Result<Self, Self::Error> {
        // Opcode is the lower 5 bits.
        let op = match val & ((1 << 5) - 1) {
            0x01 => BasicOp::SET,
            0x02 => BasicOp::ADD,
            0x03 => BasicOp::SUB,
            0x04 => BasicOp::MUL,
            0x05 => BasicOp::MLI,
            0x06 => BasicOp::DIV,
            0x07 => BasicOp::DVI,
            0x08 => BasicOp::MOD,
            0x09 => BasicOp::MDI,
            0x0a => BasicOp::AND,
            0x0b => BasicOp::BOR,
            0x0c => BasicOp::XOR,
            0x0d => BasicOp::SHR,
            0x0e => BasicOp::ASR,
            0x0f => BasicOp::SHL,
            0x10 => BasicOp::IFB,
            0x11 => BasicOp::IFC,
            0x12 => BasicOp::IFE,
            0x13 => BasicOp::IFN,
            0x14 => BasicOp::IFG,
            0x15 => BasicOp::IFA,
            0x16 => BasicOp::IFL,
            0x17 => BasicOp::IFU,
            0x1a => BasicOp::ADX,
            0x1b => BasicOp::SBX,
            0x1e => BasicOp::STI,
            0x1f => BasicOp::STD,
            _ => return Err(Error::BadInstruction),
        };

        // Of the remaining 11 bits.
        let ab = val >> 5;

        // b is lower 5 bits.
        let b: u8 = (ab & ((1 << 5) - 1)) as u8;

        // a is the highest 6 bits.
        let a: u8 = (ab >> 5) as u8;

        Ok(BasicInstruction {
            op,
            a: Operand::from(a),
            b: Operand::from(b),
        })
    }
}

impl std::convert::From<u8> for Operand {
    fn from(value: u8) -> Self {
        use std::convert::TryFrom;
        match value & ((1 << 6) - 1) {
            val @ 0x00...0x07 => Operand::Register(Register::try_from(val).unwrap()),
            val @ 0x08...0x0f => Operand::InRegisterAsAddress(Register::try_from(val).unwrap()),
            val @ 0x10...0x17 => {
                Operand::InRegisterAsAddressPlusNextWord(Register::try_from(val).unwrap())
            }
            0x18 => Operand::PushOrPop,
            0x19 => Operand::Peek,
            0x1a => Operand::Pick,
            0x1b => Operand::Register(Register::SP),
            0x1c => Operand::Register(Register::PC),
            0x1d => Operand::Register(Register::EX),
            0x1e => Operand::NextWordAsAddress,
            0x1f => Operand::NextWordAsLiteral,
            val @ 0x20...0x3f => Operand::Literal(((val as i16).wrapping_sub(33)) as i8),
            _ => unreachable!(),
        }
    }
}

impl std::convert::TryFrom<u8> for Register {
    type Error = Error;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        let value = value & ((1 << 6) - 1);
        use Register::*;
        Ok(match value % 0x07 {
            0x00 => A,
            0x01 => B,
            0x02 => C,
            0x03 => X,
            0x04 => Y,
            0x05 => Z,
            0x06 => I,
            0x07 => J,
            _ => return Err(Error::BadInstruction),
        })
    }
}

impl std::convert::TryFrom<u16> for SpecialInstruction {
    type Error = Error;
    fn try_from(value: u16) -> Result<Self, Self::Error> {
        use SpecialOp::*;
        // aaaaaaooooo00000
        let op = match value & ((1 << 5) - 1) << 5 {
            0x01 => JSR,
            0x08 => INT,
            0x09 => IAG,
            0x0a => IAS,
            0x0b => RFI,
            0x0c => IAQ,
            0x10 => HWN,
            0x11 => HWQ,
            0x12 => HWI,
            _ => return Err(Error::BadInstruction),
        };

        let a = Operand::from((value >> 10) as u8);

        Ok(SpecialInstruction { op, a })
    }
}

impl std::convert::TryFrom<u16> for Instruction {
    type Error = Error;
    fn try_from(val: u16) -> Result<Self, Self::Error> {
        if val & ((1 << 5) - 1) == 0 {
            Ok(Instruction::Special(SpecialInstruction::try_from(val)?))
        } else {
            Ok(Instruction::Basic(BasicInstruction::try_from(val)?))
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::convert::TryFrom;

    #[test]
    fn test_bits() {
        assert_eq!(0xFFFF & 0b11111, (1 << 5) - 1);
    }

    /// Convenience function for creating the bytes representing a certain instruction. Note that the argument
    /// order is that of the mnemonic, so ADD (which is 0x02) B ( which is 0x01), 12 (which is 0x32) should be
    /// called as `make_instruction(0x02, 0x01, 0x32)`
    pub fn make_instruction(o: u8, b: u8, a: u8) -> u16 {
        let a: u16 = a as u16 & ((1 << 6) - 1);
        let b: u16 = b as u16 & ((1 << 5) - 1);
        let o: u16 = o as u16 & ((1 << 5) - 1);

        (a << 10 | b << 5 | o) as u16
    }

    #[test]
    fn test_make_instruction() {
        assert_eq!(make_instruction(0x1F, 0x0, 0), 0b000000_00000_11111);
        assert_eq!(make_instruction(0x00, 0x1F, 0), 0b000000_11111_00000);
        assert_eq!(make_instruction(0x00, 0x0, 0x3F), 0b111111_00000_00000);
        /* SUB C, -1 */
        assert_eq!(make_instruction(0x3, 0x2, 0x20), 0b100000_00010_00011);
    }
    /*aaaaaa_bbbbb_ooooo */
    /// FIXME: These tests aren't very thorough -- just enough to give a vague impression that the instruction
    /// decoding happens correctly.
    #[test]
    fn test_basic_instruction() -> Result<(), Error> {
        /* SET B, 12 */
        let inst = BasicInstruction::try_from(make_instruction(0x1, 0x1, 0x2D))?;
        assert_eq!(
            inst,
            BasicInstruction {
                op: BasicOp::SET,
                b: Operand::Register(Register::B),
                a: Operand::Literal(12),
            }
        );
        /* ADD B, 1: 0x02 0x0, 0x22 */
        let inst = BasicInstruction::try_from(make_instruction(0x02, 0x0, 0x22))?;
        assert_eq!(
            inst,
            BasicInstruction {
                op: BasicOp::ADD,
                b: Operand::Register(Register::A),
                a: Operand::Literal(1),
            }
        );
        /* SUB C, -1 */
        let inst = BasicInstruction::try_from(make_instruction(0x3, 0x2, 0x20))?;
        assert_eq!(
            inst,
            BasicInstruction {
                op: BasicOp::SUB,
                b: Operand::Register(Register::C),
                a: Operand::Literal(unsafe { std::mem::transmute(-1i8) }),
            }
        );

        /* MUL X, 8 */
        let inst = BasicInstruction::try_from(make_instruction(0x4, 0x3, 0x29))?;
        assert_eq!(
            inst,
            BasicInstruction {
                op: BasicOp::MUL,
                b: Operand::Register(Register::X),
                a: Operand::Literal(8),
            }
        );
        /* MLI Y, 30 */
        let inst = BasicInstruction::try_from(make_instruction(0x5, 0x4, 0x3f))?;
        assert_eq!(
            inst,
            BasicInstruction {
                op: BasicOp::MLI,
                b: Operand::Register(Register::Y),
                a: Operand::Literal(30),
            }
        );
        Ok(())
    }
}
