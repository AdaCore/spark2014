package body Pack_A is

   Var_2 : Integer := 5 * Pack_B.Var_3 / 6;

   procedure Increment (Item : in out Integer) is
   begin
      Item := Item + 1;
   end Increment;

end Pack_A;
