package Instructions is

   type Instruction is private;

   procedure Read;

private

   type Instruction is (A, B, C);

end Instructions;
