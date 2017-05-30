with A;
with B;

package body C
with Refined_State => (State_C => (Flag_C_0, Flag_C_1, Flag_C_2))
is

   Flag_C_0 : Boolean := False;
   Flag_C_1 : Boolean := False;
   Flag_C_2 : Boolean := False;

   procedure Terminal_C is
   begin
      Flag_C_0 := True;
   end Terminal_C;

   procedure Do_C_A is
   begin
      Flag_C_1 := True;
      A.Terminal_A;
   end Do_C_A;

   procedure Do_C_B_A is
   begin
      Flag_C_2 := True;
      B.Do_B_A;
   end Do_C_B_A;

end C;
