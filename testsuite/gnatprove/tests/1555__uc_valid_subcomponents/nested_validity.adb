with Ada.Unchecked_Conversion;

procedure Nested_Validity with SPARK_Mode is
   type Bits is mod 2 ** 64 with Size => 64;
   type Inner is record
      Value : Integer;
   end record;
   for Inner use record
      Value at 0 range 0 .. 31;
   end record;
   type Target is record
      I : Inner;
      N : Natural;
   end record;
   for Target use record
      I at 0 range 0 .. 31;
      N at 4 range 0 .. 31;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Bits, Target)
     with Potentially_Invalid;
   X : Target := Convert (0) with Potentially_Invalid;
   Y : Target := Convert (16#FFFF_FFFF_0000_0000#) with Potentially_Invalid;
begin
   pragma Assert (X'Valid_Scalars);
   pragma Assert (X.I.Value = 0 and X.N = 0);
   pragma Assert (not Y.N'Valid);
   pragma Assert (Y.I.Value = 0);
   pragma Assert (X.I.Value = 1); --@ASSERT:FAIL
end Nested_Validity;
