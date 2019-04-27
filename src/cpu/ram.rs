pub struct Ram {
    memory: Vec<u8>,
}

#[derive(Debug)]
pub enum Error {
    AccessViolation(u16),
}

const MEMORY_SIZE: usize = 0x10000;

impl Ram {
    pub fn new() -> Ram {
        let mut memory = Vec::with_capacity(MEMORY_SIZE);
        memory.resize(MEMORY_SIZE, 0);
        Ram { memory: memory }
    }
    /// Get a mutable reference to a single byte at a particular address.
    pub fn mut_byte(&mut self, address: u16) -> Result<&mut u8, Error> {
        // We don't _really_ need this check as long as we're using 0x10000 bytes, which translates to
        // u16::max_value(). However, in case we ever change that...
        if self.address_is_valid(address) {
            Ok(&mut self.memory[address as usize])
        } else {
            Err(Error::AccessViolation(address))
        }
    }

    fn address_is_valid(&self, address: u16) -> bool {
        (address as usize) < self.memory.len()
    }

    /// Read the value at a certain address. Always performs word-aligned access.
    pub fn mut_word(&mut self, address: u16) -> Result<&mut u16, Error> {
        if self.address_is_valid(address + 1) {
            unsafe {
                let r: &mut u8 = self.mut_byte(address)?;
                Ok(std::mem::transmute(r as *mut u8 as *mut u16))
            }
        } else {
            Err(Error::AccessViolation(address))
        }
    }
}

mod tests {
    use super::*;

    #[test]
    fn zero_initialised() -> Result<(), Error> {
        let mut ram = Ram::new();
        assert_eq!(*ram.mut_byte(0)?, 0);
        Ok(())
    }
    #[test]
    fn read_address_as() -> Result<(), Error> {
        let mut ram = Ram::new();
        *ram.mut_word(0)? = 0xFFAA;

        let first_byte = *ram.mut_byte(0)?;
        let second_byte = *ram.mut_byte(1)?;

        let big_endian = if first_byte == 0xFF && second_byte == 0xAA {
            true
        } else if first_byte == 0xAA && second_byte == 0xFF {
            false
        } else {
            panic!(
                "Did not recognise value! Values are {}, {}",
                first_byte, second_byte
            );
        };

        *ram.mut_word(0)? = 0xAAFF;
        let (big_idx, small_idx) = if big_endian { (0, 1) } else { (1, 0) };
        assert_eq!(*ram.mut_byte(big_idx)?, 0xAA);
        assert_eq!(*ram.mut_byte(small_idx)?, 0xFF);

        Ok(())
    }
}
