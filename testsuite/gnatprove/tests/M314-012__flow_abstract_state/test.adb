with Stack_ASM;

package body Test
is

   procedure Test_01
     with Global => (Output => Stack_ASM.State)
   is
   begin
      Stack_ASM.Clear;
   end Test_01;

end Test;
