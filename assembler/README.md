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
