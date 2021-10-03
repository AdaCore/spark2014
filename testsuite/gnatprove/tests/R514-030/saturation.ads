package Saturation with SPARK_Mode
is

   type Unsigned_16 is mod 2 ** 16;

   type Saturable_Value is record
      Value : Unsigned_16;
      Upper_Bound : Unsigned_16;
   end record;

   procedure Saturate (Val : in out Saturable_Value) with
     Postcondition => Val = Val'Old; --  @ COUNTEREXAMPLE

end Saturation;
