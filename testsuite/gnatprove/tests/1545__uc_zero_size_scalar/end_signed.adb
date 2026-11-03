with Ada.Unchecked_Conversion;

procedure End_Signed with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   subtype Zero is Integer range 0 .. 0;
   type Rec is record
      Value : Byte;
      Tag   : Zero;
   end record with Size => 8;
   for Rec use record
      Value at 0 range 0 .. 7;
      Tag   at 1 range 0 .. -1;
   end record;
   function To_Record is new Ada.Unchecked_Conversion (Byte, Rec);
   function To_Byte is new Ada.Unchecked_Conversion (Rec, Byte);
   X : Rec := To_Record (42);
   Y : Byte := To_Byte (X);
begin
   pragma Assert (X.Value = 42);
   pragma Assert (X.Tag = 0);
   pragma Assert (Y = 42);
   pragma Assert (Y /= 42); --@ASSERT:FAIL
end End_Signed;
