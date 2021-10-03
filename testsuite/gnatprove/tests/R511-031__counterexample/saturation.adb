package body Saturation with SPARK_Mode is

   type Unsigned_16 is mod 2 ** 16;

   type Saturable_Value is record
      Value : Unsigned_16;
      Upper_Bound : Unsigned_16;
   end record;

   procedure Saturate (Val : in out Saturable_Value) with
     Contract_Cases =>
       (Val.Value <= Val.Upper_Bound => --  @ COUNTEREXAMPLE
          Val = Val'Old,
        Val.Value > Val.Upper_Bound  =>
          Val = Val'Old'Update (Value => Val'Old.Upper_Bound));

   procedure Saturate (Val : in out Saturable_Value) is
   begin
      Val.Value := Unsigned_16'Max (Val.Value, Val.Upper_Bound);
   end Saturate;

end Saturation;
