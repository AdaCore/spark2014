with Ada.Unchecked_Conversion;

procedure Constrained_Target with SPARK_Mode is
   type Word is mod 2 ** 64 with Size => 64;
   type Rec (D : Integer) is record
      Value : Natural;
   end record with Size => 64;
   subtype Fixed is Rec (0);
   function Convert is new Ada.Unchecked_Conversion (Word, Fixed) --@UNCHECKED_CONVERSION:FAIL
     with Potentially_Invalid;
   X : Fixed := Convert (0) with Potentially_Invalid;
begin
   pragma Assert (X.Value'Valid); --@ASSERT:FAIL
end Constrained_Target;
