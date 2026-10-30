with Ada.Unchecked_Conversion;

procedure Zero_Size_Enum with SPARK_Mode is
   type E is (A) with Size => 0;
   type Rec is record
      F : E;
   end record with Size => 0;
   for Rec use record
      F at 0 range 0 .. -1;
   end record;
   function To_Enum is new Ada.Unchecked_Conversion (Rec, E);
   function To_Record is new Ada.Unchecked_Conversion (E, Rec);
   X : Rec := (F => A);
   Y : E := To_Enum (X);
   Z : Rec := To_Record (Y);
begin
   pragma Assert (Y = A);
   pragma Assert (Z.F = A);
   pragma Assert (Z = X);
   pragma Assert (Y /= A); --@ASSERT:FAIL
end Zero_Size_Enum;
