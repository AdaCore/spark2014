with Ada.Unchecked_Conversion;

procedure Signed_To_Modular with SPARK_Mode is
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;
   type U24 is mod 2 ** 24 with Size => 24;
   function Convert is new Ada.Unchecked_Conversion (S24, U24);
   X : S24 := -1;
   Y : U24 := Convert (X);
begin
   --  The actual result is 16#FF_FFFF#, so this must remain unproved
   pragma Assert (Y = 0); --@ASSERT:FAIL
end Signed_To_Modular;
