with Pack_A, Pack_B;
with Ada.Integer_Text_IO;
procedure Pack_Test is
begin
   Ada.Integer_Text_IO.Put (Pack_A.Var_1);
   Ada.Integer_Text_IO.Put (Pack_B.Var_3);
end Pack_Test;
