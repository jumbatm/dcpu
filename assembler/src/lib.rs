use emulator::cpu::instruction::*;
use std::io::Bytes;
use std::io::Read;

#[derive(Debug)]
pub enum Op {
    Basic(BasicOp),
    Special(SpecialOp),
}

#[derive(Debug)]
pub enum Token {
    // SET
    Mnemonic(Op),
    // 10
    Literal(u16),
    MemoryAddress(u16),
    // A
    Register(Register),
    RegisterPlusWord(Register, u16),
    Push,
    Pop,
    Peek,
    Pick,
    // [A]
    RegisterAsMemoryAddress(Register),
    // :label
    Label(String),
}

#[derive(Copy, Clone, Debug)]
pub enum ProgramWord {
    Inst(emulator::cpu::instruction::Instruction),
    Data(u16),
}

use std::collections::BTreeSet;
use std::collections::{HashMap, VecDeque};

/// An iterator which sits atop a Read and performs the lexing, parsing and label resolution required.
pub struct InstructionStream<T: Read> {
    /// The source lexer.
    lex: Lexer<T>,

    /// We buffer instructions for when an instruction spans multiple words. We use Rcs because we also need to
    /// refer back to them from unresolved_names. Using Rcs means that the data will always sit in the same
    /// (heap-allocated) location, even if the vec resizes.
    instruction_queue: VecDeque<ProgramWord>,

    /// A lookahead queue of parsed instructions. Whenever we run into a label which we can't immediately
    /// resolve, we parse ahead and add to this queue until all labels are resolved.
    parse_queue: VecDeque<ParsedInstruction>,

    /// We also track what address we're currently at. We use this to translate labels to addresses.
    current_address: u16,

    /// A symbol table for our labels.
    labels: HashMap<String, u16>,

    /// Scratch space for tracking unresolved label names.
    unresolved_names: BTreeSet<String>,
}

#[derive(Debug)]
struct ParsedInstruction {
    op: Op,
    b: Option<Token>,
    a: Token,
}

impl<T: Read> InstructionStream<T> {
    /// Get an immutable reference to the underlying lexer. Most of the time, you'd only want this to check
    /// the source position -- useful if you're looking to report the position an error was found at.
    pub fn get_lexer_position(&self) -> (u16, u16) {
        self.lex.source_position
    }

    /// Convert a token operand into an instruction operand. If an extra word is needed to store the operand,
    /// it is placed into `queue`. The assumption is that queue dictates what the next instruction will be.
    fn convert_operand_or_pack(
        op: Token,
        queue: &mut VecDeque<ProgramWord>,
        labels: &HashMap<String, u16>,
    ) -> Result<Operand, ErrorType> {
        // Resolve the label first, if possible.
        let op = if let Token::Label(l) = op {
            if let Some(addr) = labels.get(&l) {
                Token::Literal(*addr)
            } else {
                return Err(ErrorType::UnresolvedLabelError(l));
            }
        } else {
            op
        };
        Ok(match op {
            Token::RegisterPlusWord(reg, word) => {
                queue.push_back(ProgramWord::Data(word));
                Operand::InRegisterAsAddressPlusNextWord(reg)
            }
            Token::Literal(lit) => {
                if lit <= 0x3F {
                    Operand::Literal(lit as u8 as i8)
                } else {
                    queue.push_back(ProgramWord::Data(lit));
                    Operand::NextWordAsLiteral
                }
            }
            Token::RegisterAsMemoryAddress(reg) => Operand::InRegisterAsAddress(reg),
            Token::Push | Token::Pop => Operand::PushOrPop,
            Token::Pick => Operand::Pick,
            Token::Peek => Operand::Peek,
            Token::MemoryAddress(lit) => {
                queue.push_back(ProgramWord::Data(lit));
                Operand::NextWordAsAddress
            }
            Token::Register(reg) => Operand::Register(reg),
            _ => unreachable!(),
        })
    }

    /// Convert a token operand to a ParsedOperand. Note that no attempt is made to perform name resolution of
    /// labels -- that's done at a later stage. This function _will_ insert Data where needed, though.
    fn convert_operand(&mut self, op: Token) -> Result<Operand, ErrorType> {
        Self::convert_operand_or_pack(op, &mut self.instruction_queue, &mut self.labels)
    }

    fn convert_instruction(
        &mut self,
        parsed_instruction: ParsedInstruction,
    ) -> Result<Instruction, ErrorType> {
        Ok(match parsed_instruction.op {
            Op::Basic(op) => {
                let b = self.convert_operand(parsed_instruction.b.unwrap())?;
                let a = self.convert_operand(parsed_instruction.a)?;
                Instruction::Basic { op, a, b }
            }
            Op::Special(op) => {
                let a = self.convert_operand(parsed_instruction.a)?;
                Instruction::Special { op, a }
            }
        })
    }

    /// Parse an entire instruction. Note that this function makes no attempt to resolve labels as operands.
    /// However, it _will_ register label definitions into `labels`. TODO: Now that ParsedInstruction holds
    /// tokens, we _could_ return labels from parse_instruction, and return them from this function.
    fn parse_instruction_and_resolve_labels(
        &mut self,
    ) -> Result<Option<ParsedInstruction>, ErrorType> {
        // Initially, we eat any leading whitespace.
        self.lex.eat_whitespace(true)?;

        match self.lex.peek_char() {
            Some(b':') => {
                if let Token::Label(lab) = self.lex.eat_label()? {
                    self.lex.eat_whitespace(false)?;
                    if self.lex.eat_char()?.unwrap_or(b'\0') != b'\n' {
                        return Err(self.lex.make_syntax_error());
                    }
                    // Add this to our resolved labels.
                    if self.labels.contains_key(&lab) {
                        return Err(ErrorType::DuplicateLabelDefinition(lab));
                    }
                    self.labels.insert(lab.clone(), self.current_address);

                    // Clear this label from unresolved names.
                    self.unresolved_names.remove(&lab);
                } else {
                    unreachable!();
                }
            }
            None => {
                return Ok(None);
            }
            _ => {}
        }

        self.lex.eat_whitespace(true)?;
        let op = if let Token::Mnemonic(op) = self.lex.get_mnemonic()? {
            op
        } else {
            unreachable!();
        };

        self.lex.eat_whitespace(false)?;

        let result;
        {
            let mut get_operand = |is_left: bool| -> Result<Token, ErrorType> {
                if !is_left {
                    // Eat the separating comma.
                    self.lex.eat_whitespace(false)?;
                    if !self.lex.eat_char()?.unwrap_or(b'\0') == b',' {
                        return Err(self.lex.make_syntax_error());
                    }
                    self.lex.eat_whitespace(false)?;
                }
                self.lex.eat_whitespace(false)?;

                self.lex.get_operand(is_left)
            };
            let b;
            let a;

            match op {
                Op::Basic(_) => {
                    b = Some(get_operand(true)?);
                    a = get_operand(false)?;
                }
                Op::Special(_) => {
                    b = None;
                    a = get_operand(true)?;
                }
            }

            result = ParsedInstruction { op, b, a };

            // Eat any trailing whitespace.
            self.lex.eat_whitespace(false)?;
            // Expect a newline.
            if self.lex.eat_char()?.unwrap_or(b'\n') != b'\n' {
                return Err(self.lex.make_syntax_error());
            }
        }
        self.current_address += 1;
        Ok(Some(result))
    }
}

impl<T: Read> std::convert::From<T> for InstructionStream<T> {
    fn from(read: T) -> Self {
        InstructionStream {
            lex: read.into(),
            instruction_queue: VecDeque::new(),
            parse_queue: VecDeque::new(),
            current_address: 0,
            unresolved_names: BTreeSet::new(),
            labels: std::collections::HashMap::new(),
        }
    }
}

impl<T: Read> Iterator for InstructionStream<T> {
    type Item = Result<ProgramWord, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(Ok(if !self.instruction_queue.is_empty() {
            self.instruction_queue.pop_front().unwrap()
        } else {
            // A convenience macro for parsing an instruction and building the Error type if it fails.
            macro_rules! parse_instruction {
                () => {
                    match self.parse_instruction_and_resolve_labels() {
                        Ok(v) => v,
                        Err(e) => {
                            return Some(Err(Error {
                                error: e,
                                line_no: self.lex.source_position.0,
                                col_no: self.lex.source_position.1,
                            }));
                        }
                    }
                };
            };
            // We need to get a new instruction. We either fetch this from the parse queue, or we parse a new
            // instruction.
            let parsed_inst = if self.parse_queue.is_empty() {
                if let Some(p) = parse_instruction!() {
                    p
                } else {
                    return None;
                }
            } else {
                self.parse_queue.pop_front().unwrap()
            };
            {
                // Check for unresolved names.
                let mut add_unresolved_label = |tok: &Token| {
                    if let Token::Label(label) = tok {
                        if !self.labels.contains_key(label.as_str()) {
                            self.unresolved_names.insert(label.clone());
                        }
                    }
                };
                add_unresolved_label(&parsed_inst.a);
                if let Some(ref b) = parsed_inst.b {
                    add_unresolved_label(b);
                }
            }
            while !self.unresolved_names.is_empty() {
                // Peek ahead until all names are resolved.
                let s = parse_instruction!();
                self.parse_queue.push_back(if let Some(p) = s {
                    p
                } else {
                    break;
                });
            }
            // At this point, we know for certain that all names have been resolved. Therefore, we can safely
            // convert the parsed instruction.
            ProgramWord::Inst(self.convert_instruction(parsed_inst).unwrap())
        }))
    }
}

#[derive(Debug)]
pub enum ErrorType {
    IOError(std::io::Error),
    SyntaxError(Option<u8>),
    UnresolvedLabelError(String),
    DuplicateLabelDefinition(String),
    MalformedParsedInstruction,
}

#[derive(Debug)]
pub struct Error {
    pub line_no: u16,
    pub col_no: u16,
    pub error: ErrorType,
}

impl std::convert::From<std::io::Error> for ErrorType {
    fn from(e: std::io::Error) -> ErrorType {
        ErrorType::IOError(e)
    }
}

/**
 * Wraps a Read and converts it into an iterator of instructions.
 */
struct Lexer<T: Read> {
    source: Bytes<T>,
    current_char: Option<u8>,
    next_char: Option<u8>,
    source_position: (u16, u16), // line, col
}

impl<T: Read> Lexer<T> {
    fn get_chars(&self) -> (Option<u8>, Option<u8>) {
        (self.current_char, self.next_char)
    }

    fn make_syntax_error(&self) -> ErrorType {
        ErrorType::SyntaxError(self.next_char)
    }
    /// Eat the current character. Returns the new current character. Comments are handled in this function: if
    /// a newline is met, it is made to be the next character returned by eat_char.
    fn eat_char(&mut self) -> std::io::Result<Option<u8>> {
        self.current_char = self.next_char;

        let mut comment = false;
        loop {
            let n = Self::rewrap_char(self.source.next())?;
            if let Some(c) = n {
                if c == b'\r' {
                    // We don't deal with \r.
                    continue;
                }
                // Update the source position.
                if c == b'\n' {
                    self.source_position.0 += 1;
                    self.source_position.1 = 0;
                    comment = false;
                } else {
                    self.source_position.1 += 1;
                }

                // Start a comment, if required.
                if c == b';' {
                    comment = true;
                }
                self.next_char = n;

                if !comment {
                    break;
                }
            } else {
                self.next_char = None;
                break;
            }
        }
        Ok(self.current_char)
    }

    // Peek one character ahead.
    fn peek_char(&self) -> Option<u8> {
        self.next_char
    }

    // Rewraps the Option<Result<u8>> returned by the iterator as an Result<Option<u8>>. That way, with the
    // ? operator, we return io errors, and we can deal with the optional character in the successful path.
    fn rewrap_char(c: Option<std::io::Result<u8>>) -> std::io::Result<Option<u8>> {
        match c {
            // Option<Result<u8>>
            None => Ok(None),
            Some(result) => match result {
                Ok(c) => Ok(Some(c)),
                Err(e) => Err(e),
            },
        }
    }

    fn is_space(c: u8) -> bool {
        let c = c as char;
        c == ' ' || c == '\t'
    }

    // Eat whitespace, leaving the lexer such that the next call to eat_char() will return the first
    // non-whitespace character.
    fn eat_whitespace(&mut self, eat_newlines: bool) -> Result<(), ErrorType> {
        loop {
            if let Some(c) = self.peek_char() {
                if !(Self::is_space(c) || (eat_newlines && c == b'\n')) {
                    break;
                }
                self.eat_char()?;
            } else {
                break;
            }
        }
        return Ok(());
    }

    fn get_position(&self) -> (u16, u16) {
        self.source_position
    }

    fn get_mnemonic(&mut self) -> Result<Token, ErrorType> {
        let c0 = self.eat_char()?.unwrap_or(b'\0');
        let c1 = self.eat_char()?.unwrap_or(b'\0');
        let c2 = self.eat_char()?.unwrap_or(b'\0');

        Ok(Token::Mnemonic(match c0 {
            b'A' => match c1 {
                b'D' => match c2 {
                    b'D' => Op::Basic(BasicOp::ADD),
                    b'X' => Op::Basic(BasicOp::ADX),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'N' => {
                    if c2 == b'D' {
                        Op::Basic(BasicOp::AND)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                b'S' => {
                    if c2 == b'R' {
                        Op::Basic(BasicOp::ASR)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'B' => {
                if c1 == b'O' {
                    if c2 == b'R' {
                        Op::Basic(BasicOp::BOR)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                } else {
                    return Err(self.make_syntax_error());
                }
            }
            b'D' => match c1 {
                b'I' => {
                    if c2 == b'V' {
                        Op::Basic(BasicOp::DIV)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                b'V' => {
                    if c2 == b'I' {
                        Op::Basic(BasicOp::DVI)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'H' => match c1 {
                b'W' => match c2 {
                    b'I' => Op::Special(SpecialOp::HWI),
                    b'N' => Op::Special(SpecialOp::HWN),
                    b'Q' => Op::Special(SpecialOp::HWQ),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'I' => match c1 {
                b'A' => match c2 {
                    b'G' => Op::Special(SpecialOp::IAG),
                    b'Q' => Op::Special(SpecialOp::IAQ),
                    b'S' => Op::Special(SpecialOp::IAS),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'F' => match c2 {
                    b'A' => Op::Basic(BasicOp::IFA),
                    b'B' => Op::Basic(BasicOp::IFB),
                    b'C' => Op::Basic(BasicOp::IFC),
                    b'E' => Op::Basic(BasicOp::IFE),
                    b'G' => Op::Basic(BasicOp::IFG),
                    b'L' => Op::Basic(BasicOp::IFL),
                    b'N' => Op::Basic(BasicOp::IFN),
                    b'U' => Op::Basic(BasicOp::IFU),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'N' => {
                    if c2 == b'T' {
                        Op::Special(SpecialOp::INT)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'J' => {
                if c1 == b'S' && c2 == b'R' {
                    Op::Special(SpecialOp::JSR)
                } else {
                    return Err(self.make_syntax_error());
                }
            }
            b'M' => match c1 {
                b'D' => {
                    if c2 == b'I' {
                        Op::Basic(BasicOp::MDI)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                b'L' => {
                    if c2 == b'I' {
                        Op::Basic(BasicOp::MLI)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                b'O' => {
                    if c2 == b'D' {
                        Op::Basic(BasicOp::MOD)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                b'U' => {
                    if c2 == b'L' {
                        Op::Basic(BasicOp::MUL)
                    } else {
                        return Err(self.make_syntax_error());
                    }
                }
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'R' => {
                if c1 == b'F' && c2 == b'I' {
                    Op::Special(SpecialOp::RFI)
                } else {
                    return Err(self.make_syntax_error());
                }
            }
            b'S' => match c1 {
                b'B' => match c2 {
                    b'X' => Op::Basic(BasicOp::SBX),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'E' => match c2 {
                    b'T' => Op::Basic(BasicOp::SET),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'H' => match c2 {
                    b'L' => Op::Basic(BasicOp::SHL),
                    b'R' => Op::Basic(BasicOp::SHR),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'T' => match c2 {
                    b'D' => Op::Basic(BasicOp::STD),
                    b'I' => Op::Basic(BasicOp::STI),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                b'U' => match c2 {
                    b'B' => Op::Basic(BasicOp::SUB),
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                },
                _ => {
                    return Err(self.make_syntax_error());
                }
            },
            b'X' => {
                if c1 == b'O' && c2 == b'R' {
                    Op::Basic(BasicOp::XOR)
                } else {
                    return Err(self.make_syntax_error());
                }
            } // match 'X'
            _ => {
                return Err(self.make_syntax_error());
            }
        })) // top level match c0
    }

    fn get_operand(&mut self, left: bool) -> Result<Token, ErrorType> {
        self.eat_operand(left, true)
    }

    fn eat_operand(&mut self, left: bool, top: bool) -> Result<Token, ErrorType> {
        let n = self.peek_char().unwrap_or(b'\0');
        if n.is_ascii_digit() {
            self.eat_literal()
        } else if n.is_ascii_alphabetic() {
            let reg = self.eat_register();
            if let Ok(Token::Pop) = reg {
                // We disallow POP to appear on the left hand side.
                if left {
                    return Err(self.make_syntax_error());
                }
            }
            reg
        } else if n == b'[' && top {
            self.eat_bracketed_operand(left)
        } else if n == b':' {
            self.eat_label()
        } else {
            Err(self.make_syntax_error())
        }
    }

    fn eat_bracketed_operand(&mut self, left: bool) -> Result<Token, ErrorType> {
        if self.eat_char()?.unwrap_or(b'\0') != b'[' {
            return Err(self.make_syntax_error());
        }
        let mut result = self.eat_operand(left, false)?;
        let tail;
        self.eat_whitespace(false)?;
        if let Some(b'+') = self.peek_char() {
            self.eat_char()?;
            self.eat_whitespace(false)?;
            tail = self.eat_literal()?;
            if let Token::Literal(s) = tail {
                if let Token::Register(r) = result {
                    result = Token::RegisterPlusWord(r, s);
                } else {
                    return Err(self.make_syntax_error());
                }
            } else {
                panic!("eat_literal did not return a literal.");
            }
        }
        self.eat_whitespace(false)?;
        if self.eat_char()?.unwrap_or(b'\0') != b']' {
            return Err(self.make_syntax_error());
        }
        // If required, transform the operand that was eaten to the token which corresponds with [operand].
        Ok(match result {
            Token::Register(r) => Token::RegisterAsMemoryAddress(r),
            Token::Literal(l) => Token::MemoryAddress(l),
            val @ Token::RegisterPlusWord(_, _) => val,
            _ => {
                return Err(self.make_syntax_error());
            }
        })
    }

    // Entry point for literal eating.
    fn eat_literal(&mut self) -> Result<Token, ErrorType> {
        let leading_zero = if self.peek_char().unwrap_or(b'\0') == b'0' {
            // Eat it. This digit is insignificant anyway.
            assert_eq!(self.eat_char()?.unwrap(), b'0');
            true
        } else {
            false
        };
        let n = self.peek_char().unwrap_or(b'\0');
        if n == b'x' {
            self.eat_char()?;
            return self.eat_hex_literal();
        } else if n == b'b' {
            self.eat_char()?;
            return self.eat_bin_literal();
        }
        return self.eat_dec_literal(leading_zero);
    }

    fn eat_bin_literal(&mut self) -> Result<Token, ErrorType> {
        self.eat_base_literal(2, false)
    }
    fn eat_hex_literal(&mut self) -> Result<Token, ErrorType> {
        self.eat_base_literal(16, false)
    }
    fn eat_dec_literal(&mut self, leading_zero: bool) -> Result<Token, ErrorType> {
        self.eat_base_literal(10, leading_zero)
    }
    fn eat_base_literal(&mut self, radix: u32, leading_zero: bool) -> Result<Token, ErrorType> {
        let mut result = String::from(if leading_zero { "0" } else { "" });
        while (self.peek_char().unwrap_or(b'\0') as char).is_digit(radix) {
            result.push(self.eat_char().unwrap().unwrap() as char);
        }
        if result.is_empty() {
            // Expected at least one numeric.
            Err(self.make_syntax_error())
        } else {
            // FIXME: Will panic on too-large literals.
            Ok(Token::Literal(u16::from_str_radix(&result, radix).unwrap()))
        }
    }

    fn eat_label(&mut self) -> Result<Token, ErrorType> {
        if self.eat_char()?.unwrap_or(b'\0') != b':' {
            return Err(self.make_syntax_error());
        }
        let mut label = String::new();
        loop {
            if let Some(c) = self.peek_char() {
                let c = c as char;
                // We allow [A-Za-z0-9_]+ in labels.
                if !(c.is_alphanumeric() || c == '_') {
                    break;
                }
            } else {
                break;
            }
            label.push(self.eat_char()?.unwrap() as char);
        }
        Ok(Token::Label(label))
    }

    fn eat_register(&mut self) -> Result<Token, ErrorType> {
        let c0 = self.eat_char()?.unwrap();
        // Match single-character.
        if !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric() {
            return Ok(Token::Register(match c0 {
                b'A' => emulator::cpu::instruction::Register::A,
                b'B' => emulator::cpu::instruction::Register::B,
                b'C' => emulator::cpu::instruction::Register::C,
                b'X' => emulator::cpu::instruction::Register::X,
                b'Y' => emulator::cpu::instruction::Register::Y,
                b'Z' => emulator::cpu::instruction::Register::Z,
                b'I' => emulator::cpu::instruction::Register::I,
                b'J' => emulator::cpu::instruction::Register::J,
                _ => {
                    return Err(self.make_syntax_error());
                }
            }));
        } else {
            // Match two-character operands.
            let c1 = self.eat_char()?.unwrap_or(b'\0');
            // This must be a two-letter register: EX, SP or PC. This must be followed by a space.
            if !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric() {
                match c0 {
                    b'E' => {
                        if c1 == b'X' {
                            return Ok(Token::Register(emulator::cpu::instruction::Register::EX));
                        } else {
                            return Err(self.make_syntax_error());
                        }
                    }
                    b'P' => {
                        if c1 == b'C' {
                            return Ok(Token::Register(emulator::cpu::instruction::Register::PC));
                        } else {
                            return Err(self.make_syntax_error());
                        }
                    }
                    b'S' => {
                        if c1 == b'P' {
                            return Ok(Token::Register(emulator::cpu::instruction::Register::SP));
                        } else {
                            return Err(self.make_syntax_error());
                        }
                    }
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                }
            } else {
                // This must be a more-than-two target:
                // PEEK,
                // PICK
                // POP,
                // PUSH,
                if c0 != b'P' {
                    return Err(self.make_syntax_error());
                }
                let c2 = self.eat_char()?.unwrap_or(b'\0');
                match c1 {
                    b'E' => {
                        let c3 = self.eat_char()?.unwrap_or(b'\0');
                        if c2 == b'E'
                            && c3 == b'K'
                            && !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric()
                        {
                            return Ok(Token::Peek);
                        }
                    }
                    b'I' => {
                        let c3 = self.eat_char()?.unwrap_or(b'\0');
                        if c2 == b'C'
                            && c3 == b'K'
                            && !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric()
                        {
                            return Ok(Token::Pick);
                        }
                    }
                    b'O' => {
                        if c2 == b'P'
                            && !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric()
                        {
                            return Ok(Token::Pop);
                        }
                    }
                    b'U' => {
                        let c3 = self.eat_char()?.unwrap_or(b'\0');
                        if c2 == b'S'
                            && c3 == b'H'
                            && !(self.peek_char().unwrap_or(b'\0') as char).is_alphanumeric()
                        {
                            return Ok(Token::Push);
                        }
                    }
                    _ => {
                        return Err(self.make_syntax_error());
                    }
                }
            }
        }
        Err(self.make_syntax_error())
    }
}
impl<T: Read> std::convert::From<T> for Lexer<T> {
    fn from(read: T) -> Lexer<T> {
        let mut source = read.bytes();
        let current_char = None;
        let next_char = Self::rewrap_char(source.next()).unwrap();

        Lexer {
            source,
            current_char,
            next_char,
            source_position: (1, 1),
        }
    }
}

// #[cfg(test)] // TODO: Need to find a way to yhave generate-assembler-tests define cfg(test) when it runs.
pub mod integration_tests {
    pub fn get_root() -> &'static str {
        env!("ASSEMBLER_TEST_ROOT")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_literal_matching() -> Result<(), super::ErrorType> {
        let src = "123 0x123 0b101".as_bytes();
        let mut lex = Lexer::from(src);
        {
            let t = lex.eat_literal()?;
            if let Token::Literal(v) = t {
                assert_eq!(v, 123);
            } else {
                panic!();
            }
        }
        lex.eat_whitespace(false)?;
        {
            let t = lex.eat_literal()?;
            if let Token::Literal(v) = t {
                assert_eq!(v, 0x123);
            } else {
                panic!();
            }
        }
        lex.eat_whitespace(false)?;
        {
            let t = lex.eat_literal()?;
            if let Token::Literal(v) = t {
                assert_eq!(v, 0b101);
            } else {
                panic!();
            }
        }
        Ok(())
    }
    #[test]
    fn test_instruction_matching() -> Result<(), super::ErrorType> {
        let src = "ADD ADX AND ASR BOR DIV DVI IFA IFB IFC IFE IFG IFL IFN IFU MDI MLI MOD MUL SBX SET SHL SHR STD STI SUB XOR JSR INT IAG IAS RFI IAQ HWN HWQ HWI";
        let mut lex = Lexer::from(src.as_bytes());

        macro_rules! expect {
            ($op:path, $expected:path) => {
                lex.eat_whitespace(false)?;
                if let Token::Mnemonic($op(m)) = lex.get_mnemonic().unwrap() {
                    assert_eq!(m, $expected);
                } else {
                    panic!();
                }
            };
        }

        expect!(Op::Basic, BasicOp::ADD);
        expect!(Op::Basic, BasicOp::ADX);
        expect!(Op::Basic, BasicOp::AND);
        expect!(Op::Basic, BasicOp::ASR);
        expect!(Op::Basic, BasicOp::BOR);
        expect!(Op::Basic, BasicOp::DIV);
        expect!(Op::Basic, BasicOp::DVI);
        expect!(Op::Basic, BasicOp::IFA);
        expect!(Op::Basic, BasicOp::IFB);
        expect!(Op::Basic, BasicOp::IFC);
        expect!(Op::Basic, BasicOp::IFE);
        expect!(Op::Basic, BasicOp::IFG);
        expect!(Op::Basic, BasicOp::IFL);
        expect!(Op::Basic, BasicOp::IFN);
        expect!(Op::Basic, BasicOp::IFU);
        expect!(Op::Basic, BasicOp::MDI);
        expect!(Op::Basic, BasicOp::MLI);
        expect!(Op::Basic, BasicOp::MOD);
        expect!(Op::Basic, BasicOp::MUL);
        expect!(Op::Basic, BasicOp::SBX);
        expect!(Op::Basic, BasicOp::SET);
        expect!(Op::Basic, BasicOp::SHL);
        expect!(Op::Basic, BasicOp::SHR);
        expect!(Op::Basic, BasicOp::STD);
        expect!(Op::Basic, BasicOp::STI);
        expect!(Op::Basic, BasicOp::SUB);
        expect!(Op::Basic, BasicOp::XOR);
        expect!(Op::Special, SpecialOp::JSR);
        expect!(Op::Special, SpecialOp::INT);
        expect!(Op::Special, SpecialOp::IAG);
        expect!(Op::Special, SpecialOp::IAS);
        expect!(Op::Special, SpecialOp::RFI);
        expect!(Op::Special, SpecialOp::IAQ);
        expect!(Op::Special, SpecialOp::HWN);
        expect!(Op::Special, SpecialOp::HWQ);
        expect!(Op::Special, SpecialOp::HWI);
        Ok(())
    }
    #[test]
    fn test_register_matching() -> Result<(), super::ErrorType> {
        let mut lex = Lexer::from("A B C X Y Z I J SP PC EX PUSH POP PEEK PICK".as_bytes());
        {
            macro_rules! expect {
                ($expected:ident) => {
                    lex.eat_whitespace(false)?;
                    if let Token::Register(emulator::cpu::instruction::Register::$expected) =
                        lex.eat_register()?
                    {
                        assert!(true);
                    } else {
                        assert!(false);
                    }
                };
            }

            expect!(A);
            expect!(B);
            expect!(C);
            expect!(X);
            expect!(Y);
            expect!(Z);
            expect!(I);
            expect!(J);
            expect!(SP);
            expect!(PC);
            expect!(EX);
        }

        {
            macro_rules! expect {
                ($type:ident) => {
                    lex.eat_whitespace(false)?;
                    if let Token::$type = lex.eat_register()? {
                        assert!(true);
                    } else {
                        assert!(false);
                    }
                };
            }
            expect!(Push);
            expect!(Pop);
            expect!(Peek);
            expect!(Pick);
        }
        Ok(())
    }

    #[test]
    fn test_operand_matching_left() -> Result<(), super::ErrorType> {
        let src = "A [B] [C + 10] PUSH POP";
        let mut lex = Lexer::from(src.as_bytes());

        lex.eat_whitespace(false)?;

        if let Token::Register(emulator::cpu::instruction::Register::A) = lex.get_operand(true)? {
            assert!(true);
        } else {
            assert!(false);
        }
        lex.eat_whitespace(false)?;

        if let Token::RegisterAsMemoryAddress(emulator::cpu::instruction::Register::B) =
            dbg!(lex.get_operand(true)?)
        {
            assert!(true);
        } else {
            assert!(false);
        }

        lex.eat_whitespace(false)?;

        if let Token::RegisterPlusWord(emulator::cpu::instruction::Register::C, 10) =
            dbg!(lex.get_operand(true))?
        {
            assert!(true);
        } else {
            assert!(false);
        }

        lex.eat_whitespace(false)?;

        if let Token::Push = lex.get_operand(true)? {
            assert!(true);
        } else {
            assert!(false);
        }
        if let Err(super::ErrorType::SyntaxError(_)) = lex.get_operand(true) {
            assert!(true);
        } else {
            assert!(false);
        }
        Ok(())
    }
    #[test]
    fn test_operand_matching_right() -> Result<(), super::ErrorType> {
        let src = "A [B] [C + 10] POP PUSH";
        let mut lex = Lexer::from(src.as_bytes());

        lex.eat_whitespace(false)?;

        if let Token::Register(emulator::cpu::instruction::Register::A) = lex.get_operand(true)? {
            assert!(true);
        } else {
            assert!(false);
        }
        lex.eat_whitespace(false)?;

        if let Token::RegisterAsMemoryAddress(emulator::cpu::instruction::Register::B) =
            dbg!(lex.get_operand(false)?)
        {
            assert!(true);
        } else {
            assert!(false);
        }

        lex.eat_whitespace(false)?;

        if let Token::RegisterPlusWord(emulator::cpu::instruction::Register::C, 10) =
            dbg!(lex.get_operand(false))?
        {
            assert!(true);
        } else {
            assert!(false);
        }

        lex.eat_whitespace(false)?;

        if let Token::Pop = lex.get_operand(false)? {
            assert!(true);
        } else {
            assert!(false);
        }
        if let Err(super::ErrorType::SyntaxError(_)) = lex.get_operand(false) {
            assert!(true);
        } else {
            assert!(false);
        }
        Ok(())
    }

    #[test]
    fn test_eat_label() -> Result<(), super::ErrorType> {
        let mut lex = Lexer::from(":label1 :label2 :underscores_allowed :123456789".as_bytes());

        macro_rules! expect {
            ($lit:expr) => {
                lex.eat_whitespace(false)?;
                if let Token::Label(s) = lex.eat_label()? {
                    assert_eq!(s, $lit);
                } else {
                    assert!(false);
                }
            };
        }

        expect!("label1");
        expect!("label2");
        expect!("underscores_allowed");
        expect!("123456789");
        Ok(())
    }
}
