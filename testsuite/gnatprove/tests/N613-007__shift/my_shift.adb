package body My_Shift is

   procedure P (Z : in out My_Mod) is
      Z_Old : constant My_Mod := Z;
   begin
      Z := Shift_Right (Z, 1);
      pragma Assert (Z = Z_Old / 2);
      Z := Shift_Right (Z, 2);
      pragma Assert (Z = Z_Old / 8);
   end P;

end My_Shift;
