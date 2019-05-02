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
    register_a: u16,
    register_b: u16,
    register_c: u16,
    register_x: u16,
    register_y: u16,
    register_z: u16,
    register_i: u16,
    register_j: u16,
    register_sp: u16,
    register_pc: u16,
    register_ex: u16,
    interrupt_address: u16,
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
            register_a: 0,
            register_b: 0,
            register_c: 0,
            register_x: 0,
            register_y: 0,
            register_z: 0,
            register_i: 0,
            register_j: 0,
            register_sp: 0,
            register_pc: 0,
            register_ex: 0,
            interrupt_address: 0,
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

    /// Fetch and execute an instruction, or pretend to be still be busy with an instruction, in which case
    /// nothing will be done for this tick.
    pub fn tick(&mut self) {
        // We're still busy executing an instruction.
        if self.wait_ticks > 0 {
            self.wait_ticks -= 1;
            return;
        }
        use instruction::BasicOp;
        use instruction::Operand;

        fn get_reference_to_register<'a>(
            cpu: &'a mut CPU,
            reg: &instruction::Register,
        ) -> &'a mut u16 {
            use instruction::Register::*;
            match reg {
                A => &mut cpu.register_a,
                B => &mut cpu.register_b,
                C => &mut cpu.register_c,
                X => &mut cpu.register_x,
                Y => &mut cpu.register_y,
                Z => &mut cpu.register_z,
                I => &mut cpu.register_i,
                J => &mut cpu.register_j,
                SP => &mut cpu.stack_pointer,
                PC => &mut cpu.program_counter,
                EX => &mut cpu.register_ex,
            }
        };

        fn resolve_operand_b<'a>(cpu: &'a mut CPU, b: &Operand) -> Option<&'a mut u16> {
            Some(match b {
                Operand::Literal(_) => {
                    // Attempting to write to a literal value is a no-op.
                    return None;
                }
                Operand::NextWordAsLiteral => {
                    cpu.increment_pc_and_mut().unwrap();
                    // Writing to a literal value fails silently here as well.
                    return None;
                }
                Operand::InRegisterAsAddress(register) => {
                    let v = *get_reference_to_register(cpu, register);
                    cpu.ram.mut_word(v).unwrap()
                }
                Operand::NextWordAsAddress => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(v).unwrap()
                }
                Operand::Register(reg) => get_reference_to_register(cpu, reg),
                Operand::InRegisterAsAddressPlusNextWord(reg) => {
                    let r = *get_reference_to_register(cpu, reg);
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(v + r).unwrap()
                }
                Operand::PushOrPop => {
                    // Operand b. Therefore, this is a PUSH operation.
                    cpu.stack_pointer -= 1;
                    cpu.ram.mut_word(cpu.stack_pointer).unwrap()
                }
                Operand::Peek => cpu.ram.mut_word(cpu.stack_pointer).unwrap(),
                Operand::Pick => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    cpu.ram.mut_word(cpu.stack_pointer + v).unwrap()
                }
            })
        };
        fn resolve_operand_a(cpu: &mut CPU, a: &Operand) -> u16 {
            let a: u16 = match *a {
                Operand::Literal(v) => v as u16,
                Operand::NextWordAsLiteral => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    *cpu.ram.mut_word(v).unwrap()
                }
                Operand::InRegisterAsAddress(ref register) => {
                    let v = *get_reference_to_register(cpu, register);
                    *cpu.ram.mut_word(v).unwrap()
                }
                Operand::NextWordAsAddress => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    *cpu.ram.mut_word(v).unwrap()
                }
                Operand::Register(ref reg) => *get_reference_to_register(cpu, reg),
                Operand::InRegisterAsAddressPlusNextWord(ref reg) => {
                    let r = *get_reference_to_register(cpu, reg);
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    *cpu.ram.mut_word(v + r).unwrap()
                }
                Operand::PushOrPop => {
                    // Operand a. Therefore, this is a POP operation.
                    let result = *cpu.ram.mut_word(cpu.stack_pointer).unwrap();
                    cpu.stack_pointer += 1;
                    result
                }
                Operand::Peek => *cpu.ram.mut_word(cpu.stack_pointer).unwrap(),
                Operand::Pick => {
                    let v = *cpu.increment_pc_and_mut().unwrap();
                    *cpu.ram.mut_word(cpu.stack_pointer + v).unwrap()
                }
            };
            a
        };

        fn arithmetic_shift(x: u16, num_bits: i8) -> u16 {
            let shift_amount: u32 = num_bits as u32;
            let x_transmuted: isize = unsafe { std::mem::transmute::<u16, i16>(x) } as isize;
            let shift = if num_bits < 0 {
                isize::wrapping_shl
            } else if num_bits > 0 {
                isize::wrapping_shr
            } else {
                return x;
            };

            let x_transmuted = shift(x_transmuted, shift_amount);
            // Transmute back to usize.
            let x_shifted: usize = unsafe { std::mem::transmute(x_transmuted) };
            x_shifted as u16
        }

        fn as_signed(x: u16) -> i16 {
            unsafe { std::mem::transmute(x) }
        }
        fn as_unsigned(x: i16) -> u16 {
            unsafe { std::mem::transmute(x) }
        }

        // Fetch and decode an instruction.
        let instruction = self.fetch_instruction();
        if let Some(instruction) = instruction {
            let instruction: Instruction = instruction.unwrap();

            if let Instruction::Basic(ref instruction) = instruction {
                let a = resolve_operand_a(self, &instruction.a);
                if let Some(b) = resolve_operand_b(self, &instruction.b) {
                    match instruction.op {
                        // At this level, we resolve operands to the corresponding u16 contained with ram.
                        BasicOp::SET => {
                            *b = a;
                        }
                        BasicOp::ADD => {
                            *b += a;
                        }
                        BasicOp::SUB => {
                            *b -= a;
                        }
                        BasicOp::MUL => {
                            let full_result: u32 = (*b as u32) * (a as u32);
                            // Overflow register will contain the upper 16 bits.
                            let overflow: u16 = ((full_result >> 16) & 0xFFFF) as u16;
                            // We store the lower 16 bits of the result in b.
                            *b = (full_result & 0xFFFFu32) as u16;
                            self.register_ex = overflow;
                        }
                        BasicOp::MLI => {
                            let b_signed: i16 = as_signed(*b);
                            let a_signed: i16 = as_signed(a);
                            // Perform the multiplication in a signed way.
                            let full_result: isize = (b_signed as isize) * (a_signed as isize);
                            // Then reinterpret the result as unsigned.

                            // Overflow register will contain the upper 16 bits.
                            let overflow: u16 = ((full_result >> 16) & 0xFFFF) as u16;
                            // We store the lower 16 bits of the result in b.
                            *b = (full_result & 0xFFFF) as u16;
                            // And the overflow in register_EX.
                            self.register_ex = overflow;
                        }
                        BasicOp::DIV => {
                            // Division by zero causes EX and B to be set to zero.
                            if a == 0 {
                                *b = 0;
                                self.register_ex = 0;
                                return;
                            }
                            // Otherwise, we perform unsigned division.
                            *b /= a;
                            // We fill EX up with the fractional part.
                            self.register_ex = ((((*b as u32) << 16) / (a as u32)) & 0xFFFF) as u16;
                        }
                        BasicOp::DVI => {
                            // Like DIV, but treat b and a as signed.
                            let a_signed: i16 = as_signed(a);
                            let b_signed: i16 = as_signed(*b);

                            let full_result: isize = (a_signed as isize) * (b_signed as isize);
                            *b = (full_result & 0xFFFF) as u16;
                            self.register_ex = ((full_result >> 16) & 0xFFFF) as u16;
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
                            let b_signed: i16 = as_signed(*b);
                            let a_signed: i16 = as_signed(a);
                            let result: u16 = as_unsigned(b_signed % a_signed);

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
                            let b_copy: u16 = *b;

                            // Perform b <<< a
                            *b <<= a;

                            // Now we set EX to ((b << 16) >>> a & 0xFFFF).
                            // Transmute to isize so Rust will perform an arithmetic shift.
                            self.register_ex =
                                arithmetic_shift(arithmetic_shift(b_copy, -16), a as i8) & 0xFFFF;
                        }
                        BasicOp::ASR => {
                            let b_copy = *b;
                            *b = arithmetic_shift(*b, a as i8);
                            self.register_ex = arithmetic_shift(b_copy, -16) >> a;
                        }
                        BasicOp::SHL => {
                            let b_copy = *b;
                            *b <<= a;
                            self.register_ex =
                                arithmetic_shift(arithmetic_shift(b_copy, -(a as i8)), 16) & 0xFFFF;
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
                            if !as_signed(*b) > as_signed(a) {
                                self.increment_pc_and_mut();
                            }
                        }
                        BasicOp::IFL => {
                            if !(*b < a) {
                                self.increment_pc_and_mut();
                            }
                        }
                        BasicOp::IFU => {
                            if !(as_signed(*b) < as_signed(a)) {
                                self.increment_pc_and_mut();
                            }
                        }
                        BasicOp::ADX => {
                            let b_large = *b as isize;
                            let value = a + self.register_ex;
                            *b = value;
                        }
                        _ => {
                            panic!("Unimplemented instruction! {:?}", instruction);
                        }
                    };
                }
            } else if let Instruction::Special(instruction) = instruction {
                // Do something
            } else {
                // Instruction is neither Instruction::Basic nor Instruction::Special.
                unreachable!();
            }
        } else {
            panic!("End of ram."); // TODO: Replace with appropriate behaviour.
        }
    }
}
