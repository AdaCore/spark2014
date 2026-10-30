with Ada.Unchecked_Conversion;

procedure Unbiased_Control with SPARK_Mode is
   type Word is mod 2 ** 16 with Size => 16;
   subtype Positive_Byte is Integer range 1 .. 256;
   type Rec is record
      F : Positive_Byte;
   end record with Size => 16;
   for Rec use record
      F at 0 range 0 .. 15;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Rec, Word);
   X : Rec := (F => 1);
   Y : Word := Convert (X);
begin
   pragma Assert (Y = 1);
   pragma Assert (Y = 0); --@ASSERT:FAIL
end Unbiased_Control;
