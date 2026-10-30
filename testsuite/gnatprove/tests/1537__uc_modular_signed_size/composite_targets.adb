with Ada.Unchecked_Conversion;

procedure Composite_Targets with SPARK_Mode is
   type U24 is mod 2 ** 24 with Size => 24;
   type S12 is range -(2 ** 11) .. 2 ** 11 - 1 with Size => 12;

   type Target_Record is record
      Low  : S12;
      High : S12;
   end record with Size => 24;
   for Target_Record use record
      Low  at 0 range 0 .. 11;
      High at 1 range 4 .. 15;
   end record;

   type Target_Array is array (1 .. 2) of S12
     with Component_Size => 12, Size => 24;

   function To_Record is new Ada.Unchecked_Conversion (U24, Target_Record);
   function To_Array is new Ada.Unchecked_Conversion (U24, Target_Array);

   R : Target_Record;
   A : Target_Array;
begin
   --  Each component uses its own 12-bit sign position, not the whole
   --  target's 24-bit size or the intermediate BV32 width.
   R := To_Record (16#800_800#);
   pragma Assert (R.Low = S12'First and R.High = S12'First);
   A := To_Array (16#800_800#);
   pragma Assert (A (1) = S12'First and A (2) = S12'First);

   R := To_Record (16#7FF_7FF#);
   pragma Assert (R.Low = S12'Last and R.High = S12'Last);
   A := To_Array (16#7FF_7FF#);
   pragma Assert (A (1) = S12'Last and A (2) = S12'Last);

   R := To_Record (16#FFF_FFF#);
   pragma Assert (R.Low = -1 and R.High = -1);
   A := To_Array (16#FFF_FFF#);
   pragma Assert (A (1) = -1 and A (2) = -1);
end Composite_Targets;
