with Ada.Unchecked_Conversion;

procedure Zero_Size_Integer with SPARK_Mode is
   type Zero is range 0 .. 0 with Size => 0;
   type Rec is record
      F : Zero;
   end record with Size => 0;
   for Rec use record
      F at 0 range 0 .. -1;
   end record;
   function To_Zero is new Ada.Unchecked_Conversion (Rec, Zero);
   function To_Record is new Ada.Unchecked_Conversion (Zero, Rec);
   X : Rec := (F => 0);
   Y : Zero := To_Zero (X);
   Z : Rec := To_Record (Y);
begin
   pragma Assert (Y = 0);
   pragma Assert (Z.F = 0);
   pragma Assert (Z = X);
   pragma Assert (Y /= 0); --@ASSERT:FAIL
end Zero_Size_Integer;
