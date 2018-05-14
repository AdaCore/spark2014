package body Saturation with SPARK_Mode is

   procedure Saturate (Val : in out Saturable_Value) is
   begin
      Val.Value := Unsigned_16'Max (Val.Value, Val.Upper_Bound);
   end Saturate;

end Saturation;
