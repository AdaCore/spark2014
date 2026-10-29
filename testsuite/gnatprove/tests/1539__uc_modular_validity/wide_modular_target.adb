with Ada.Unchecked_Conversion;

procedure Wide_Modular_Target with SPARK_Mode is
   type U16 is mod 2 ** 16 with Size => 16;
   type U8 is mod 2 ** 8 with Size => 8;
   type Target is record
      Value : U8;
   end record with Size => 16;
   for Target use record
      Value at 0 range 0 .. 15;
   end record;
   function Convert is new Ada.Unchecked_Conversion (U16, Target)
     with Potentially_Invalid;
   X : U16 := 256;
   Y : Target := Convert (X) with Potentially_Invalid;
begin
   --  A wider component slot must be checked before narrowing to BV8
   pragma Assert (Y.Value'Valid); --@ASSERT:FAIL
end Wide_Modular_Target;
