with Stack_ASM;

package body Test
is

   procedure Test_01
     with Global => (Output => Stack_ASM.State)
   is
   begin
      Stack_ASM.Clear;
   end Test_01;

   procedure Test_02 (I : out Integer)
     with Global => Stack_ASM.State
   is
   begin
      I := Stack_ASM.Top;
   end Test_02;

   procedure Test_03 (I : out Integer)
     with Global => (Output => Stack_ASM.State)
   is
   begin
      I := Stack_ASM.Top;
   end Test_03;

   procedure Test_04 (I : out Integer)
     with Global => (Output => Stack_ASM.State)
   is
   begin
      Stack_ASM.Clear;
      I := Stack_ASM.Top;
   end Test_04;

end Test;
