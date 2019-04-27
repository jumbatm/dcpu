use std::convert::TryFrom;
#[derive(Debug, PartialEq, Eq)]
pub enum Opcode {
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

#[derive(Debug, PartialEq, Eq)]
enum Register {
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

#[derive(Debug, PartialEq, Eq)]
enum Operand {
    NextWordAsAddress,
    NextWordAsLiteral,
    Literal(i8),
    Register(Register),
    AsAddress(Register),
    AsAddressPlusNextWord(Register),
    PushOrPop,
    Peek,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Instruction {
    op: Opcode,
    a: Operand,
    b: Operand,
}

#[derive(Debug)]
pub enum Error {
    BadInstruction,
}

impl std::convert::TryFrom<u16> for Instruction {
    type Error = Error;
    fn try_from(val: u16) -> Result<Self, Self::Error> {
        // Opcode is the lower 5 bits.
        let op = match val & (1 << 5) - 1 {
            0x01 => Opcode::SET,
            0x02 => Opcode::ADD,
            0x03 => Opcode::SUB,
            0x04 => Opcode::MUL,
            0x05 => Opcode::MLI,
            0x06 => Opcode::DIV,
            0x07 => Opcode::DVI,
            0x08 => Opcode::MOD,
            0x09 => Opcode::MDI,
            0x0a => Opcode::AND,
            0x0b => Opcode::BOR,
            0x0c => Opcode::XOR,
            0x0d => Opcode::SHR,
            0x0e => Opcode::ASR,
            0x0f => Opcode::SHL,
            0x10 => Opcode::IFB,
            0x11 => Opcode::IFC,
            0x12 => Opcode::IFE,
            0x13 => Opcode::IFN,
            0x14 => Opcode::IFG,
            0x15 => Opcode::IFA,
            0x16 => Opcode::IFL,
            0x17 => Opcode::IFU,
            0x1a => Opcode::ADX,
            0x1b => Opcode::SBX,
            0x1e => Opcode::STI,
            0x1f => Opcode::STD,
            _ => return Err(Error::BadInstruction),
        };

        // Of the remaining 11 bits.
        let ab = val >> 5;

        // b is lower 6 bits.
        let b: u8 = (ab & ((1 << 6) - 1)) as u8;

        // a is the highest 5 bits.
        let a: u8 = (ab >> 5) as u8;

        Ok(Instruction {
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
            val @ 0x08...0x0f => Operand::AsAddress(Register::try_from(val).unwrap()),
            val @ 0x10...0x17 => Operand::AsAddressPlusNextWord(Register::try_from(val).unwrap()),
            0x18 => Operand::PushOrPop,
            0x19 => Operand::AsAddress(Register::SP),
            0x1a => Operand::Peek,
            0x1b => Operand::Register(Register::SP),
            0x1c => Operand::Register(Register::PC),
            0x1d => Operand::Register(Register::EX),
            0x1e => Operand::NextWordAsAddress,
            0x1f => Operand::NextWordAsLiteral,
            val @ 0x20...0x3f => Operand::Literal((val as i8) - 33),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bits() {
        assert_eq!(0xFFFF & 0b11111, (1 << 5) - 1);
    }

    #[allow(exceeding_bitshifts)]
    fn make_instruction(o: u8, b: u8, a: u8) -> u16 {
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
    }
    /*aaaaaa_bbbbb_ooooo */
    #[test]
    fn test_add_instruction() -> Result<(), Error> {
        /* ADD A, 1 */
        /* 0x02 0x0, 0x22 */
        let inst = Instruction::try_from(make_instruction(0x02, 0x0, 0x22))?;
        assert_eq!(
            inst,
            Instruction {
                op: Opcode::ADD,
                a: Operand::Literal(1),
                b: Operand::Register(Register::A),
            }
        );
        Ok(())
    }
}
