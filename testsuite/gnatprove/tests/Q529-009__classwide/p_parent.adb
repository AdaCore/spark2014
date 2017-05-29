package body P_Parent
with SPARK_Mode
is

   function Get_X0 (This : in T_Parent) return T0
   is (This.X0);

   procedure Set_X0 (This  : in out T_Parent;
                     Value : in     T0) is
   begin
      This.X0 := Value;
   end Set_X0;

   procedure Compute (This : in out T_Parent) is
   begin
      This.Set_X0 (Value => This.Get_X0 + 1);
   end Compute;

end P_Parent;
