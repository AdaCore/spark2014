package body P
with SPARK_Mode,
     Refined_State => (P_Abs_State => P_State)
is

   procedure Set_Value (Value : in Integer) with
     Refined_Global => (Output => P_State)
   is
   begin
      P_State := Value;
   end Set_Value;

   function Calculate (X : Integer) return Integer
   is
   begin
      return X / P_State;
   end Calculate;

end P;
