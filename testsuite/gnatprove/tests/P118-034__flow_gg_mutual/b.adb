with A;
with C;

package body B
with Refined_State => (State_B => (Flag_B_0, Flag_B_1, Flag_B_2, Flag_B_3, Flag_B_4))
is

   Flag_B_0 : Boolean := False;
   Flag_B_1 : Boolean := False;
   Flag_B_2 : Boolean := False;
   Flag_B_3 : Boolean := False;
   Flag_B_4 : Boolean := False;

   procedure Terminal_B is
   begin
      Flag_B_0 := True;
   end Terminal_B;

   procedure Do_B_A is
   begin
      Flag_B_1 := True;
      A.Terminal_A;
   end Do_B_A;

   procedure Do_B_C is
   begin
      Flag_B_2 := True;
      C.Terminal_C;
   end Do_B_C;

   procedure Do_B_C_A is
   begin
      Flag_B_3 := True;
      C.Do_C_A;
   end Do_B_C_A;

   procedure Do_B_C_B_A is
   begin
      Flag_B_4 := True;
      C.Do_C_B_A;
   end Do_B_C_B_A;

end B;
