procedure Layout with SPARK_Mode is
   type Byte is mod 256 with Size => 8;
   type R is record
      B : Byte;
      F : Positive;
   end record;
   for R use record
      B at 0 range 0 .. 7;
      F at 4 range 0 .. 31;
   end record;
   type D is new R;
   for D use record
      B at 0 range 0 .. 15;
      F at 4 range 0 .. 31;
   end record;
   X : R with Import, Potentially_Invalid;
   Y : D with Import, Potentially_Invalid;
   Z : D with Import, Potentially_Invalid;
begin
   Y.B := 0;
   pragma Assert (Y.B'Valid);
   Y.F := 1;
   pragma Assert (Y'Valid_Scalars);
   pragma Assert (X.F'Valid); -- @ASSERT:FAIL
   pragma Assert (Z.B'Valid); -- @ASSERT:FAIL
end Layout;
