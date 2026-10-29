with Ada.Unchecked_Conversion;

procedure Oversized_Modular_Target with SPARK_Mode is
   type U16 is mod 2 ** 16 with Size => 16;
   type U8 is mod 2 ** 8 with Size => 16;
   function Convert is new Ada.Unchecked_Conversion (U16, U8)
     with Potentially_Invalid;
   X : U16 := 256;
   Y : U8 := Convert (X) with Potentially_Invalid;
begin
   --  The complete 16-bit pattern does not represent a valid U8 value
   pragma Assert (Y'Valid); --@ASSERT:FAIL
end Oversized_Modular_Target;
