mod instruction;
mod ram;

use instruction::Instruction;
use ram::Ram;
use std::convert::TryFrom;

pub struct CPU {
    ram: Ram,
    program_counter: u16,
    stack_pointer: u16,
}

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
            stack_pointer: 0,
        }
    }
    /// Get the currently pointed-to instruction and increment the PC.
    fn fetch_instruction(&mut self) -> Result<Instruction, Error> {
        let result: u16 = *self.ram.mut_word(self.program_counter)?;
        self.program_counter += 1;
        match Instruction::try_from(result) {
            Ok(instruction) => Ok(instruction),
            Err(error_type) => Err(Error::InstructionError(error_type)),
        }
    }
}
