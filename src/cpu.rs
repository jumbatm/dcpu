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
    register_A: u16,
    register_B: u16,
    register_C: u16,
    register_X: u16,
    register_Y: u16,
    register_Z: u16,
    register_I: u16,
    register_J: u16,
    register_SP: u16,
    register_PC: u16,
    register_EX: u16,
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
            register_A: 0,
            register_B: 0,
            register_C: 0,
            register_X: 0,
            register_Y: 0,
            register_Z: 0,
            register_I: 0,
            register_J: 0,
            register_SP: 0,
            register_PC: 0,
            register_EX: 0,
        }
    }
    fn increment_pc_and_mut(&mut self) -> Option<&mut u16> {
        if self.program_counter >= 0xFFFF {
            return None;
        }
        let result: &mut u16 = match self.ram.mut_word(self.program_counter) {
            Ok(word) => word,
            Err(err) => return None,
        };
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
    pub fn tick<'a, 'b: 'a>(&'a mut self) {
        // We're still busy executing an instruction.
        if self.wait_ticks > 0 {
            self.wait_ticks -= 1;
            return;
        }
        use instruction::BasicOp;
        use instruction::Operand;

        fn get_reference_to_register<'a>(
            cpu: &'a mut CPU,
            reg: instruction::Register,
        ) -> &'a mut u16 {
            use instruction::Register::*;
            match reg {
                A => &mut cpu.register_A,
                B => &mut cpu.register_B,
                C => &mut cpu.register_C,
                X => &mut cpu.register_X,
                Y => &mut cpu.register_Y,
                Z => &mut cpu.register_Z,
                I => &mut cpu.register_I,
                J => &mut cpu.register_J,
                SP => &mut cpu.stack_pointer,
                PC => &mut cpu.program_counter,
                EX => &mut cpu.register_EX,
            }
        };
        // Fetch and decode an instruction.
        match self.fetch_instruction() {
            Some(instruction) => match instruction.unwrap() {
                Instruction::Basic(instruction) => match instruction.op {
                    // At this level, we resolve operands to the corresponding u16 contained with ram.
                    SET => {
                        let b: &mut u16 = match instruction.b {
                            Operand::Literal(_) => {
                                // Attempting to write to a literal value is a no-op.
                                return;
                            }
                            Operand::InRegisterAsAddress(register) => self
                                .ram
                                .mut_word(*get_reference_to_register(self, register))
                                .unwrap(),
                            Operand::NextWordAsAddress => self.increment_pc_and_mut().unwrap(),
                        };
                    }
                    _ => {
                        panic!("Unimplemented instruction! {:?}", instruction);
                    }
                },
                Instruction::Special(instruction) => {}
            },
            None => panic!("End of ram."), // TODO: Replace with appropriate behaviour.
        };
    }
}
