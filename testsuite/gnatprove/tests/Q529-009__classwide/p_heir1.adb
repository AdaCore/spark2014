package body P_Heir1
with SPARK_Mode
is

   function Get_X1 (This : in T_Heir1) return T1
     is (This.X1);

   procedure Set_X1 (This  : in out T_Heir1;
                     Value : in     T1) is
   begin
      This.X1 := Value;
   end Set_X1;

   overriding procedure Compute (This : in out T_Heir1) is
   begin
      This.Set_X1 (Value => This.Get_X1 + 1);
      This.Set_X0 (Value => This.Get_X0 + This.Get_X1);
   end Compute;

end P_Heir1;
