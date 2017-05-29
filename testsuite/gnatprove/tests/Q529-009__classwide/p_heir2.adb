package body P_Heir2
with SPARK_Mode
is

   function Get_X2 (This : in T_Heir2) return T2
     is (This.X2);

   procedure Set_X2 (This  : in out T_Heir2;
                     Value : in     T2) is
   begin
      This.X2 := Value;
   end Set_X2;

   overriding procedure Compute (This : in out T_Heir2) is
   begin
      This.Set_X2 (Value => This.Get_X2 + 2);
      This.Set_X0 (Value => This.Get_X0 + This.Get_X2);
   end Compute;

end P_Heir2;
