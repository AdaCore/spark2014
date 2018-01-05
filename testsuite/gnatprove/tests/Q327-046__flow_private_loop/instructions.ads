package Instructions is

   type Instruction is private;

   procedure Read with Global => null;

private

   type Instruction is (A, B, C);

end Instructions;
