with Ada.Unchecked_Conversion;

procedure Biased_Enum with SPARK_Mode is
   type Bit is mod 2 with Size => 1;
   type E is (A, B, C);
   subtype Last_Two is E range B .. C;
   type Rec is record
      F : Last_Two;
   end record with Size => 1;
   for Rec use record
      F at 0 range 0 .. 0;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Rec, Bit);
   X : Rec := (F => B);
   Y : Bit := Convert (X);
begin
   --  The biased field stores zero for B, whose position is 1
   pragma Assert (Y = 1); --@ASSERT:FAIL
end Biased_Enum;
