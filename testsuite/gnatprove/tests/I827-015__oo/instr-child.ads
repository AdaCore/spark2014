package Instr.Child is

   subtype Thousand is Integer range 0 .. 1000;

   type Accurate_Clock is new Clock with private;

   procedure Display_Value (X : Accurate_Clock);
   procedure Increment (X : in out Accurate_Clock; inc : Integer := 1);

private
   type Accurate_Clock is new Clock with record
      MilliSec : Thousand := 0;
   end record;

end;










