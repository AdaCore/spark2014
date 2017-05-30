with B;
with C;

package body A
with Refined_State => (State_A => (Flag_A_0, Flag_A_1, Flag_A_2, Flag_A_3, Flag_A_4, Flag_A_5, Flag_A_6, Flag_A_7))
is

   Flag_A_0 : Boolean := False;
   Flag_A_1 : Boolean := False;
   Flag_A_2 : Boolean := False;
   Flag_A_3 : Boolean := False;
   Flag_A_4 : Boolean := False;
   Flag_A_5 : Boolean := False;
   Flag_A_6 : Boolean := False;
   Flag_A_7 : Boolean := False;

   procedure Terminal_A is
   begin
      Flag_A_0 := True;
   end Terminal_A;

   procedure Do_A_B is
   begin
      Flag_A_1 := True;
      B.Terminal_B;
   end Do_A_B;

   procedure Do_A_C is
   begin
      Flag_A_2 := True;
      C.Terminal_C;
   end Do_A_C;

   procedure Do_A_B_A is
   begin
      Flag_A_3 := True;
      B.Do_B_A;
   end Do_A_B_A;

   procedure Do_A_B_C is
   begin
      Flag_A_4 := True;
      B.Do_B_C;
   end Do_A_B_C;

   procedure Do_A_C_A is
   begin
      Flag_A_5 := True;
      C.Do_C_A;
   end Do_A_C_A;

   procedure Do_A_B_C_A is
   begin
      Flag_A_6 := True;
      B.Do_B_C_A;
   end Do_A_B_C_A;

   procedure Do_A_B_C_B_A is
   begin
      Flag_A_7 := True;
      B.Do_B_C_B_A;
   end Do_A_B_C_B_A;

end A;
