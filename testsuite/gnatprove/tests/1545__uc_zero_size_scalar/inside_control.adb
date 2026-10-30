with Ada.Unchecked_Conversion;

procedure Inside_Control with SPARK_Mode is
   type U7 is mod 2 ** 7 with Size => 7;
   type E is (A) with Size => 0;
   type Rec is record
      Value : U7;
      Tag   : E;
   end record with Size => 7;
   for Rec use record
      Value at 0 range 0 .. 6;
      Tag   at 0 range 7 .. 6;
   end record;
   function Convert is new Ada.Unchecked_Conversion (U7, Rec);
   Y : Rec := Convert (42);
begin
   pragma Assert (Y.Value = 42);
   pragma Assert (Y.Tag = A);
   pragma Assert (Y.Value /= 42); --@ASSERT:FAIL
end Inside_Control;
