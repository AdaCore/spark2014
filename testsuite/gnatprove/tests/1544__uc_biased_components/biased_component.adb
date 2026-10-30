with Ada.Unchecked_Conversion;

procedure Biased_Component with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   subtype Positive_Byte is Integer range 1 .. 256;
   type Rec is record
      F : Positive_Byte;
   end record with Size => 8;
   for Rec use record
      F at 0 range 0 .. 7;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Rec, Byte);
   X : Rec := (F => 1);
   Y : Byte := Convert (X);
begin
   --  The biased field stores zero for the value 1
   pragma Assert (Y = 1); --@ASSERT:FAIL
end Biased_Component;
