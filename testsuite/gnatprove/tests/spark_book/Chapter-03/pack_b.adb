with Pack_A;
package body Pack_B is

   Var_4 : Integer := 3 * Pack_A.Var_1 / 4;

   procedure Decrement (Item : in out Integer) is
   begin
      Item := Item - 1;
   end Decrement;

end Pack_B;
