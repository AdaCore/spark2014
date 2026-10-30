with Ada.Unchecked_Conversion;

procedure Signed_Source (Negative : Boolean) with SPARK_Mode is
   type S16 is range -(2 ** 15) .. 2 ** 15 - 1 with Size => 16;
   type U8 is mod 2 ** 8 with Size => 16;
   function Convert is new Ada.Unchecked_Conversion (S16, U8)
     with Potentially_Invalid;
   X : S16 := (if Negative then -1 else 256);
   Y : U8 := Convert (X) with Potentially_Invalid;
begin
   --  Neither 16#FFFF# nor 16#0100# represents a valid U8 value
   pragma Assert (Y'Valid); --@ASSERT:FAIL
end Signed_Source;
