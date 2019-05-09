mod instruction;
mod ram;

use instruction::Instruction;
use ram::Ram;
use std::convert::TryFrom;

pub struct CPU {
    ram: Ram,
    program_counter: u16,
    stack_pointer: u16,
    wait_ticks: u8,
    registers: Registers,
    excess: u16,
    interrupt_address: u16,
}

struct Registers {
    a: u16,
    b: u16,
    c: u16,
    x: u16,
    y: u16,
    z: u16,
    i: u16,
    j: u16,
}

impl Registers {
    fn new() -> Registers {
        Registers {
            a: 0,
            b: 0,
            c: 0,
            x: 0,
            y: 0,
            z: 0,
            i: 0,
            j: 0,
        }
    }

    fn get_register(&mut self, reg: &instruction::Register) -> Option<&mut u16> {
        use instruction::Register::*;
        Some(match reg {
            A => &mut self.a,
            B => &mut self.b,
            C => &mut self.c,
            X => &mut self.x,
            Y => &mut self.y,
            Z => &mut self.z,
            I => &mut self.i,
            J => &mut self.j,
            _ => return None,
        })
    }
}

impl From<Ram> for CPU {
    fn from(ram: Ram) -> CPU {
        let mut result = CPU::new();
        result.ram = ram;
        result
    }
}

#[derive(Debug)]
enum Error {
    RamError(ram::Error),
    InstructionError(instruction::Error),
}

impl From<ram::Error> for Error {
    fn from(err: ram::Error) -> Self {
        Error::RamError(err)
    }
}

impl CPU {
    pub fn new() -> CPU {
        CPU {
            ram: Ram::new(),
            program_counter: 0,
            stack_pointer: 0xFFFF,
            wait_ticks: 0,
            registers: Registers::new(),
            interrupt_address: 0,
            excess: 0,
        }
    }
    /// Get a reference to the word pointed to by the PC. Then, increment the PC.    
    fn increment_pc_and_mut(&mut self) -> Option<&mut u16> {
        let result: &mut u16 = match self.ram.mut_word(self.program_counter) {
            Ok(word) => word,
            Err(_) => return None,
        };
        if self.program_counter == 0xFFFF {
            self.program_counter = 0;
            return None;
        }
        self.program_counter += 1;
        Some(result)
    }
    /// Get the current word pointed to by the PC as an instruction. Then, increment the PC.
    fn fetch_instruction(&mut self) -> Option<Result<Instruction, Error>> {
        Some(match Instruction::try_from(*self.increment_pc_and_mut()?) {
            Ok(instruction) => Ok(instruction),
            Err(error_type) => Err(Error::InstructionError(error_type)),
        })
    }

    fn get_reference_to_register(&mut self, register: &instruction::Register) -> &mut u16 {
        if let Some(reg) = self.registers.get_register(&register) {
            reg
        } else {
            match register {
                instruction::Register::EX => &mut self.interrupt_address,
                instruction::Register::SP => &mut self.stack_pointer,
                instruction::Register::PC => &mut self.program_counter,
                _ => unreachable!(),
            }
        }
    }

    /// Execute an instruction. This is where the "brains" of our CPU live.
    pub fn execute(&mut self, instruction: Instruction) {
        use instruction::{BasicOp, Operand, SpecialOp};

        enum ResolvedOperand<'a> {
            Literal(u16),
            Reference(&'a mut u16),
        };

        impl<'a> ResolvedOperand<'a> {
            fn as_literal(&self) -> u16 {
                match &self {
                    ResolvedOperand::Literal(v) => *v,
                    ResolvedOperand::Reference(v) => **v,
                }
            }
        }

        fn resolve_operand_a<'a>(cpu: &'a mut CPU, a: &Operand) -> ResolvedOperand<'a> {
            let a: &mut u16 = match *a {
                Operand::Literal(v) => return ResolvedOperand::Literal(v as u16),
                Operand::NextWordAsLiteral => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(v).unwrap()
                }
                Operand::InRegisterAsAddress(ref register) => {
                    let v = *cpu.get_reference_to_register(register);
                    cpu.ram.mut_word(v).unwrap()
                }
                Operand::NextWordAsAddress => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(v).unwrap()
                }
                Operand::Register(ref reg) => cpu.get_reference_to_register(reg),
                Operand::InRegisterAsAddressPlusNextWord(ref reg) => {
                    let r = *cpu.get_reference_to_register(reg);
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(v + r).unwrap()
                }
                Operand::PushOrPop => {
                    // Operand a. Therefore, this is a POP operation.
                    let result = cpu.ram.mut_word(cpu.stack_pointer).unwrap();
                    cpu.stack_pointer += 1;
                    result
                }
                Operand::Peek => cpu.ram.mut_word(cpu.stack_pointer).unwrap(),
                Operand::Pick => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(cpu.stack_pointer + v).unwrap()
                }
            };
            ResolvedOperand::Reference(a)
        };

        fn arithmetic_shift(x: u16, num_bits: i8) -> u16 {
            let shift_amount: u32 = num_bits as u32;
            let shift = if num_bits < 0 {
                i16::wrapping_shl
            } else if num_bits > 0 {
                i16::wrapping_shr
            } else {
                return x;
            };

            let x = shift(x as i16, shift_amount);
            x as u16
        }

        // We pre-emptively grab a copy of what's in the interrupt address here, to avoid double mut borrow later.
        let interrupt_address_copy = self.interrupt_address;
        let a: ResolvedOperand = match instruction.get_a() {
            Operand::Literal(v) => ResolvedOperand::Literal(*v as u16),
            reference => {
                ResolvedOperand::Reference(match reference {
                    Operand::NextWordAsLiteral => {
                        let v = *self.increment_pc_and_mut().unwrap();
                        self.ram.mut_word(v).unwrap()
                    }
                    Operand::InRegisterAsAddress(ref register) => {
                        let v = *self.get_reference_to_register(register);
                        self.ram.mut_word(v).unwrap()
                    }
                    Operand::NextWordAsAddress => {
                        let v = *self.increment_pc_and_mut().unwrap();
                        self.ram.mut_word(v).unwrap()
                    }
                    Operand::Register(reg) => self.get_reference_to_register(reg),
                    Operand::InRegisterAsAddressPlusNextWord(ref reg) => {
                        let r = *self.get_reference_to_register(reg);
                        let v = *self.increment_pc_and_mut().unwrap();
                        self.ram.mut_word(v + r).unwrap()
                    }
                    Operand::PushOrPop => {
                        // Operand a. Therefore, this is a POP operation.
                        let result = self.ram.mut_word(self.stack_pointer).unwrap();
                        self.stack_pointer += 1;
                        result
                    }
                    Operand::Peek => self.ram.mut_word(self.stack_pointer).unwrap(),
                    Operand::Pick => {
                        let v = *self.increment_pc_and_mut().unwrap();
                        self.ram.mut_word(self.stack_pointer + v).unwrap()
                    }
                    _ => unreachable!(),
                })
            }
        };

        if let Instruction::Basic(instruction) = &instruction {
            let a = match resolve_operand_a(self, &instruction.a) {
                ResolvedOperand::Literal(v) => v,
                ResolvedOperand::Reference(v) => *v,
            };
            let b = match &instruction.b {
                Operand::Literal(_) => {
                    // Attempting to write to a literal value is a no-op.
                    return;
                }
                Operand::NextWordAsLiteral => {
                    self.increment_pc_and_mut().unwrap();
                    // Writing to a literal value fails silently here as well.
                    return;
                }
                Operand::InRegisterAsAddress(register) => {
                    let v = *self.get_reference_to_register(register);
                    self.ram.mut_word(v).unwrap()
                }
                Operand::NextWordAsAddress => {
                    let v = *self.increment_pc_and_mut().unwrap();
                    self.ram.mut_word(v).unwrap()
                }
                Operand::Register(reg) => self.registers.get_register(reg).unwrap(),
                Operand::InRegisterAsAddressPlusNextWord(reg) => {
                    let r = *self.get_reference_to_register(reg);
                    let v = *self.increment_pc_and_mut().unwrap();
                    self.ram.mut_word(v + r).unwrap()
                }
                Operand::PushOrPop => {
                    // Operand b. Therefore, this is a PUSH operation.
                    self.stack_pointer -= 1;
                    self.ram.mut_word(self.stack_pointer).unwrap()
                }
                Operand::Peek => self.ram.mut_word(self.stack_pointer).unwrap(),
                Operand::Pick => {
                    let v = *self.increment_pc_and_mut().unwrap();
                    self.ram.mut_word(self.stack_pointer + v).unwrap()
                }
            };

            match instruction.op {
                BasicOp::SET => {
                    *b = a;
                }
                BasicOp::ADD => {
                    *b = b.wrapping_add(a);
                }
                BasicOp::SUB => {
                    *b = b.wrapping_sub(a);
                }
                BasicOp::MUL => {
                    let full_result: u32 = (*b as u32) * (a as u32);
                    // Overflow register will contain the upper 16 bits.
                    let overflow: u16 = ((full_result >> 16) & 0xFFFF) as u16;
                    // We store the lower 16 bits of the result in b.
                    *b = (full_result & 0xFFFFu32) as u16;
                    self.excess = overflow;
                }
                BasicOp::MLI => {
                    let b_signed: i16 = *b as i16;
                    let a_signed: i16 = a as i16;
                    // Perform the multiplication in a signed way.
                    let full_result: isize = (b_signed as isize) * (a_signed as isize);
                    // Then reinterpret the result as unsigned.

                    // Overflow register will contain the upper 16 bits.
                    let overflow: u16 = ((full_result.wrapping_shr(16)) & 0xFFFF) as u16;
                    // We store the lower 16 bits of the result in b.
                    *b = (full_result & 0xFFFF) as u16;
                    // And the overflow in register_EX.
                    self.excess = overflow;
                }
                BasicOp::DIV => {
                    // Division by zero causes EX and B to be set to zero.
                    if a == 0 {
                        *b = 0;
                        self.excess = 0;
                        return;
                    }
                    // We fill EX up with the fractional part.
                    let tmp = (*b as usize).wrapping_shl(16);
                    self.excess = ((tmp / (a as usize)) & 0xFFFF) as u16;

                    // Otherwise, we perform unsigned division.
                    *b /= a;
                }
                BasicOp::DVI => {
                    // Like DIV, but treat b and a as signed.
                    if a == 0 {
                        *b = 0;
                        self.excess = 0;
                        return;
                    }
                    let a_signed: i16 = a as i16;
                    let b_signed: i16 = *b as i16;
                    *b = b_signed.wrapping_div(a_signed) as u16;
                    self.excess = (((b_signed as isize).wrapping_shl(16) / a_signed as isize)
                        & 0xFFFF) as u16;
                }
                BasicOp::MOD => {
                    if a == 0 {
                        *b = 0;
                        return;
                    }
                    *b = *b % a;
                }
                BasicOp::MDI => {
                    if a == 0 {
                        return;
                    }
                    let b_signed: i16 = *b as i16;
                    let a_signed: i16 = a as i16;
                    let result: u16 = (b_signed % a_signed) as u16;

                    // TODO: Check that the modulo behaves as described in spec: MDI -7, 16 = -7
                    // If not, we'll need to perform the modulo unsigned, then re-apply the signedness
                    // of a/abs(a) * b/abs(b) * result
                    *b = result;
                }
                BasicOp::AND => {
                    *b &= a;
                }
                BasicOp::BOR => {
                    *b |= a;
                }
                BasicOp::XOR => {
                    *b ^= a;
                }
                BasicOp::SHR => {
                    // Perform right shift on a. Rust will perform logical shifts on unsigned types, and
                    // arithmetic shifts on signed types.
                    // DCPU-16 spec denotes it in Java's notation: >>> for logical shift (perform
                    // shift as if unsigned. >> for arithmetic shift (preserve signedness).

                    // Get a copy of b. We use this to calculate EX's value later.
                    // Now we set EX to ((b << 16) >>> a & 0xFFFF).
                    self.excess = arithmetic_shift(arithmetic_shift(*b, -16), a as i8) & 0xFFFF;

                    // Perform b <<< a
                    *b >>= a;
                }
                BasicOp::ASR => {
                    self.excess = arithmetic_shift(*b, -16) >> a;
                    *b = arithmetic_shift(*b, a as i8);
                }
                BasicOp::SHL => {
                    self.excess = arithmetic_shift(arithmetic_shift(*b, -(a as i8)), 16) & 0xFFFF;
                    *b <<= a;
                }
                BasicOp::IFB => {
                    // Performs next instruction iff b & a != 0.
                    if !((a & *b) != 0) {
                        // In other words, we skip an instruction if it is equal to zero.
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFC => {
                    // Performs next instruction iff (b&a) == 0
                    if !((a & *b) == 0) {
                        // In other words, we skip the next instruction if it's not equal to zero.
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFE => {
                    // Perform next instruction only if b == a.
                    if !(*b == a) {
                        // In other words... Yeah, I think you get the gist.
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFN => {
                    if !(*b == a) {
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFG => {
                    if !(*b > a) {
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFA => {
                    if !((*b as i16) > (a as i16)) {
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFL => {
                    if !(*b < a) {
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::IFU => {
                    if !((*b as i16) < (a as i16)) {
                        self.increment_pc_and_mut();
                    }
                }
                BasicOp::ADX => {
                    let b_large = *b as usize + a as usize + self.excess as usize;
                    *b = (b_large & 0xFFFF) as u16;
                    // Check for overflow.
                    self.excess = if b_large > std::u16::MAX as usize {
                        1
                    } else {
                        0
                    };
                }
                BasicOp::SBX => {
                    let b_small: isize = *b as isize - a as isize + self.excess as isize;
                    *b = ((b_small as usize) & 0xFFFF) as u16;
                    // Check for underflow.
                    self.excess = if b_small < 0 { 0xFFFF } else { 0 };
                }
                BasicOp::STI => {
                    *b = a;
                    self.registers.i += 1;
                }
                BasicOp::STD => {
                    *b = a;
                    self.registers.j -= 1;
                }
            };
        } else if let Instruction::Special(instruction) = instruction {
            match instruction.op {
                SpecialOp::JSR => {
                    let a = resolve_operand_a(self, &instruction.a).as_literal();
                    // Push address of next instruction to stack, then set PC to a.
                    self.stack_pointer -= 1;
                    *self.ram.mut_word(self.stack_pointer).unwrap() = self.program_counter + 1;
                    self.program_counter = a;
                }
                // SpecialOp::INT => {}
                SpecialOp::IAG => {
                    if let ResolvedOperand::Literal(_) = a {
                        return;
                    } else if let ResolvedOperand::Reference(a) = a {
                        *a = interrupt_address_copy;
                    }
                }
                /*
                SpecialOp::IAS => {
                    let a = resolve_operand_a(self, &instruction.a).as_literal();
                    self.interrupt_address = a;
                }
                SpecialOp::IAQ => {
                    // If a is nonzero, add interrupts to queue instead of executing them right away.
                }
                SpecialOp::HWN => {
                    // Set a to the number of hardware devices.
                }
                SpecialOp::HWQ => {
                    // Set A, B, C, X, Y registers to information about hardware at a.
                }
                SpecialOp::HWI => {
                    // Send hardware interrupt to a.
                }
                SpecialOp::RFI => {}
                */
                _ => panic!("Unimplemented SpecialOp: {:?}", instruction.op),
            }
        } else {
            // Instruction is neither Instruction::Basic nor Instruction::Special.
            unreachable!();
        }
    }

    /// Fetch and execute an instruction, or pretend to be still be busy with an instruction, in which case
    /// nothing will be done for this tick.
    pub fn tick(&mut self) {
        // We're still busy executing an instruction.
        if self.wait_ticks > 0 {
            self.wait_ticks -= 1;
            return;
        }

        // Fetch and decode an instruction.
        let instruction = self.fetch_instruction();

        if let Some(instruction) = instruction {
            let instruction: Instruction = instruction.unwrap();
            self.execute(instruction);
        } else {
            panic!("End of ram."); // TODO: Replace with appropriate behaviour.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::instruction::*;

    macro_rules! exec_basic_on_register {
        ($cpu:ident, $op:ident, $b:ident, $a:expr) => {
            $cpu.execute(Instruction::Basic(BasicInstruction {
                op: BasicOp::$op,
                b: Operand::Register(Register::$b),
                a: Operand::Literal($a),
            }));
        };
    }

    macro_rules! on_all_registers {
        ($cpu:ident, $op: ident, $a: expr) => {
            exec_basic_on_register!($cpu, $op, A, $a);
            exec_basic_on_register!($cpu, $op, B, $a);
            exec_basic_on_register!($cpu, $op, C, $a);
            exec_basic_on_register!($cpu, $op, X, $a);
            exec_basic_on_register!($cpu, $op, Y, $a);
            exec_basic_on_register!($cpu, $op, Z, $a);
            exec_basic_on_register!($cpu, $op, I, $a);
            exec_basic_on_register!($cpu, $op, J, $a);
        };
    }

    macro_rules! set_registers_to_increment {
        ($cpu:ident) => {
            exec_basic_on_register!($cpu, SET, A, 1);
            exec_basic_on_register!($cpu, SET, B, 2);
            exec_basic_on_register!($cpu, SET, C, 3);
            exec_basic_on_register!($cpu, SET, X, 4);
            exec_basic_on_register!($cpu, SET, Y, 5);
            exec_basic_on_register!($cpu, SET, Z, 6);
            exec_basic_on_register!($cpu, SET, I, 7);
            exec_basic_on_register!($cpu, SET, J, 8);
        };
    }

    #[test]
    fn test_set_instruction_and_set_registers_to_increment_macro() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        assert_eq!(cpu.registers.a, 1);
        assert_eq!(cpu.registers.b, 2);
        assert_eq!(cpu.registers.c, 3);
        assert_eq!(cpu.registers.x, 4);
        assert_eq!(cpu.registers.y, 5);
        assert_eq!(cpu.registers.z, 6);
        assert_eq!(cpu.registers.i, 7);
        assert_eq!(cpu.registers.j, 8);
    }

    #[test]
    fn test_add_sub_instructions() {
        let mut cpu = CPU::new();

        set_registers_to_increment!(cpu);

        on_all_registers!(cpu, ADD, 20);

        assert_eq!(cpu.registers.a, 21);
        assert_eq!(cpu.registers.b, 22);
        assert_eq!(cpu.registers.c, 23);
        assert_eq!(cpu.registers.x, 24);
        assert_eq!(cpu.registers.y, 25);
        assert_eq!(cpu.registers.z, 26);
        assert_eq!(cpu.registers.i, 27);
        assert_eq!(cpu.registers.j, 28);

        on_all_registers!(cpu, SUB, 7);
        assert_eq!(cpu.registers.a, 14);
        assert_eq!(cpu.registers.b, 15);
        assert_eq!(cpu.registers.c, 16);
        assert_eq!(cpu.registers.x, 17);
        assert_eq!(cpu.registers.y, 18);
        assert_eq!(cpu.registers.z, 19);
        assert_eq!(cpu.registers.i, 20);
        assert_eq!(cpu.registers.j, 21);

        // Test underflow.
        on_all_registers!(cpu, SUB, 22);
        assert_eq!(cpu.registers.a, -8i16 as u16);
        assert_eq!(cpu.registers.b, -7i16 as u16);
        assert_eq!(cpu.registers.c, -6i16 as u16);
        assert_eq!(cpu.registers.x, -5i16 as u16);
        assert_eq!(cpu.registers.y, -4i16 as u16);
        assert_eq!(cpu.registers.z, -3i16 as u16);
        assert_eq!(cpu.registers.i, -2i16 as u16);
        assert_eq!(cpu.registers.j, -1i16 as u16);
    }
    #[test]
    fn test_mul() {
        let mut cpu = CPU::new();

        // Test MUL.
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, MUL, 10);
        assert_eq!(cpu.registers.a, 10);
        assert_eq!(cpu.registers.b, 20);
        assert_eq!(cpu.registers.c, 30);
        assert_eq!(cpu.registers.x, 40);
        assert_eq!(cpu.registers.y, 50);
        assert_eq!(cpu.registers.z, 60);
        assert_eq!(cpu.registers.i, 70);
        assert_eq!(cpu.registers.j, 80);
        on_all_registers!(cpu, MUL, 127);

        assert_eq!(cpu.registers.a, ((10 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.b, ((20 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.c, ((30 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.x, ((40 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.y, ((50 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.z, ((60 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.i, ((70 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.j, ((80 * 127) as usize & 0xFFFF) as u16);

        // Last multiplication to be performed is with register J, so we'll only end up testing with
        // Register J's excess value.
        assert_eq!(
            cpu.excess,
            (((80 * 127) as usize).wrapping_shr(16) & 0xFFFF) as u16
        );
        on_all_registers!(cpu, MUL, 127);

        assert_eq!(cpu.registers.a, ((10 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.b, ((20 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.c, ((30 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.x, ((40 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.y, ((50 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.z, ((60 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.i, ((70 * 127 * 127) as usize & 0xFFFF) as u16);
        assert_eq!(cpu.registers.j, ((80 * 127 * 127) as usize & 0xFFFF) as u16);

        // Last multiplication to be performed is with register J, so we'll only end up testing with
        // Register J's excess value.
        assert_eq!(
            cpu.excess,
            (((80 * 127 * 127) as usize).wrapping_shr(16) & 0xFFFF) as u16
        );
    }

    #[test]
    fn test_mli() {
        let mut cpu = CPU::new();
        // Test MLI.
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, MLI, -20);
        assert_eq!(cpu.registers.a, -20i16 as u16);
        assert_eq!(cpu.registers.b, -40i16 as u16);
        assert_eq!(cpu.registers.c, -60i16 as u16);
        assert_eq!(cpu.registers.x, -80i16 as u16);
        assert_eq!(cpu.registers.y, -100i16 as u16);
        assert_eq!(cpu.registers.z, -120i16 as u16);
        assert_eq!(cpu.registers.i, -140i16 as u16);
        assert_eq!(cpu.registers.j, -160i16 as u16);
        // Because this is two's complement, we expect these upper bits to be all 1 (which is the unsigned
        // equivalent of reading as 0).
        assert_eq!(cpu.excess, 0xFFFF);
    }

    #[test]
    fn test_div() {
        let mut cpu = CPU::new();
        // Test DIV.
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, MUL, 5);
        on_all_registers!(cpu, DIV, 8);
        assert_eq!(cpu.registers.a, 5 / 8);
        assert_eq!(cpu.registers.b, 10 / 8);
        assert_eq!(cpu.registers.c, 15 / 8);
        assert_eq!(cpu.registers.x, 20 / 8);
        assert_eq!(cpu.registers.y, 25 / 8);
        assert_eq!(cpu.registers.z, 30 / 8);
        assert_eq!(cpu.registers.i, 35 / 8);
        assert_eq!(cpu.registers.j, 40 / 8);

        // Now test DIV's excess behaviour. We need to handcraft some values for this.
        cpu.registers.a = 1;
        exec_basic_on_register!(cpu, DIV, A, 16);
        assert_eq!(cpu.registers.a, 0);
        // 1/16 is the same as doing 1 >> 4. The excess part acts as the fractional part of a fixed-point
        // number. Therefore, we expect the shift to go into this fractional part, starting from the
        // right.
        assert_eq!(cpu.excess, 1 << (16 - 4));

        // Try values that should evaluate to 1/2, or 1 >> 1
        cpu.registers.b = 4;
        exec_basic_on_register!(cpu, DIV, B, 8);
        assert_eq!(cpu.registers.b, 0);
        assert_eq!(cpu.excess, 1 << (16 - 1));

        // Try division by zero.
        cpu.registers.c = 255;
        exec_basic_on_register!(cpu, DIV, C, 0);
        // Should also set B to 0.
        assert_eq!(cpu.registers.c, 0);
        assert_eq!(cpu.excess, 0);
    }
    #[test]
    fn test_dvi() {
        let mut cpu = CPU::new();
        // DVI instruction.
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, MUL, 20);
        on_all_registers!(cpu, DVI, -10);
        assert_eq!(cpu.registers.a, -2i16 as u16);
        assert_eq!(cpu.registers.b, -4i16 as u16);
        assert_eq!(cpu.registers.c, -6i16 as u16);
        assert_eq!(cpu.registers.x, -8i16 as u16);
        assert_eq!(cpu.registers.y, -10i16 as u16);
        assert_eq!(cpu.registers.z, -12i16 as u16);
        assert_eq!(cpu.registers.i, -14i16 as u16);
        assert_eq!(cpu.registers.j, -16i16 as u16);

        // Test DVI excess.
        cpu.registers.b = -1i16 as u16;
        exec_basic_on_register!(cpu, DVI, B, 2);
        assert_eq!(cpu.registers.b, 0);
        assert_eq!(cpu.excess, 1 << (16 - 1));
    }

    #[test]
    fn test_mod() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, MOD, 3);
        assert_eq!(cpu.registers.a, 1);
        assert_eq!(cpu.registers.b, 2);
        assert_eq!(cpu.registers.c, 0);
        assert_eq!(cpu.registers.x, 1);
        assert_eq!(cpu.registers.y, 2);
        assert_eq!(cpu.registers.z, 0);
        assert_eq!(cpu.registers.i, 1);
        assert_eq!(cpu.registers.j, 2);
    }

    #[test]
    fn test_mdi() {
        let mut cpu = CPU::new();
        exec_basic_on_register!(cpu, SET, B, 12);
        exec_basic_on_register!(cpu, MDI, B, 11);
        assert_eq!(cpu.registers.b, 1);

        exec_basic_on_register!(cpu, SET, A, -7);
        exec_basic_on_register!(cpu, MDI, A, 16);
        assert_eq!(cpu.registers.a, -7i16 as u16);
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, AND, 0b11);
        assert_eq!(cpu.registers.a, 0b01);
        assert_eq!(cpu.registers.b, 0b10);
        assert_eq!(cpu.registers.c, 0b11);
        assert_eq!(cpu.registers.x, 0b00);
        assert_eq!(cpu.registers.y, 0b01);
        assert_eq!(cpu.registers.z, 0b10);
        assert_eq!(cpu.registers.i, 0b11);
        assert_eq!(cpu.registers.j, 0b00);
    }

    #[test]
    fn test_bor() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, BOR, 0b11);
        assert_eq!(cpu.registers.a, 0b11);
        assert_eq!(cpu.registers.b, 0b11);
        assert_eq!(cpu.registers.c, 0b11);
        assert_eq!(cpu.registers.x, 0b111);
        assert_eq!(cpu.registers.y, 0b111);
        assert_eq!(cpu.registers.z, 0b111);
        assert_eq!(cpu.registers.i, 0b111);
        assert_eq!(cpu.registers.j, 0b1011);
    }

    #[test]
    fn test_xor() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, XOR, 0b11);
        assert_eq!(cpu.registers.a & 0b11, 0b10); // 0b01
        assert_eq!(cpu.registers.b & 0b11, 0b01); // 0b10
        assert_eq!(cpu.registers.c & 0b11, 0b00); // 0b11
        assert_eq!(cpu.registers.x & 0b11, 0b11); // 0b100
        assert_eq!(cpu.registers.y & 0b11, 0b10); // 0b101
        assert_eq!(cpu.registers.z & 0b11, 0b01); // 0b110
        assert_eq!(cpu.registers.i & 0b11, 0b00); // 0b111
        assert_eq!(cpu.registers.j & 0b11, 0b11); // 0b1000
    }

    #[test]
    fn test_shr() {
        let mut cpu = CPU::new();
        set_registers_to_increment!(cpu);
        on_all_registers!(cpu, SHR, 1);
        assert_eq!(cpu.registers.a, 0);
        assert_eq!(cpu.registers.b, 1);
        assert_eq!(cpu.registers.c, 1);
        assert_eq!(cpu.registers.x, 2);
        assert_eq!(cpu.registers.y, 2);
        assert_eq!(cpu.registers.z, 3);
        assert_eq!(cpu.registers.i, 3);
        assert_eq!(cpu.registers.j, 4);

        // Test that this is a logical shift.
        cpu.registers.a = -1i16 as u16;
        exec_basic_on_register!(cpu, SHR, A, 1);
        assert_ne!(cpu.registers.a, (-1i16 >> 1) as u16);
        assert_eq!(cpu.registers.a, 0x7FFF);
        assert_eq!(cpu.excess, 0xFFFF);
    }

    #[test]
    fn test_asr() {
        let mut cpu = CPU::new();
        cpu.registers.a = -16i16 as u16;
        exec_basic_on_register!(cpu, ASR, A, 2);
        assert_eq!(cpu.registers.a, -4i16 as u16);
        assert_eq!(cpu.excess, 0);
    }

}
