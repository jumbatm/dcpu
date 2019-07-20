This is an assembler for the DCPU-16. 
Almost every instruction maps directly to a single instruction in the DCPU-16, with a few exceptions.

First, the assembler automatically inserts data and next word operands. 
This is performed when a literal value is specified as an operand, and the operand is larger than can fit in the operand  part of the instruction. For example:

```dasm16
SET PUSH, 0x3F ; This fits in the instruction word.
SET PUSH, 0xFFFF ; 0xFFFF will be inserted after the instruction. Then, the generated operand will be 0x1F - next word (literal)
```

Another case where an extra word is inserted is in register + next word.
See below:

```dasm16
SET [A + 0xFF], 10 ; 0xFF will be inserted in the next word.
```
The final case is for the PICK instruction.

```
SET A, PICK 0x123
```
Here, the next word is set to 0x123.

# Testing
The integration tests for the assembler aren't handwritten. Instead, the expected outputs are first generated, manually verified, and then later changes are compared with the expected output. The check happens automatically with `cargo test`, but you need to manually run the generate step when required.

## Running the generate step
If you've made an update on purpose that makes a change to the instructions that are generated, or you've added a new test file, you need to run the generate step. To do this:

```bash
$ cd ./generate-assembler-tests
$ cargo run
```
