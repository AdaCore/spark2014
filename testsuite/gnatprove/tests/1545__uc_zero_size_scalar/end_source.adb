with Ada.Unchecked_Conversion;

procedure End_Source with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type E is (A) with Size => 0;
   type Rec is record
      Value : Byte;
      Tag   : E;
   end record with Size => 8;
   for Rec use record
      Value at 0 range 0 .. 7;
      Tag   at 1 range 0 .. -1;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Rec, Byte);
   X : Rec := (Value => 42, Tag => A);
   Y : Byte := Convert (X);
begin
   pragma Assert (Y = 42);
   pragma Assert (Y /= 42); --@ASSERT:FAIL
end End_Source;
