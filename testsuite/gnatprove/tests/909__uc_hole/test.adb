with Ada.Text_IO;
with Ada.Unchecked_Conversion;

procedure Test with spark_mode is

   type R is record
      I : Natural;
   end record;

   function Conv is new Ada.Unchecked_Conversion (Integer, R); --@UNCHECKED_CONVERSION:FAIL

   X : Integer := -12;
   Y : R := Conv (X);
   Z : constant Integer := Y.I;


   type BR is record
      I : Natural;
      B : Boolean;
   end record;

   type BR2 is record
      I : Integer;
      B : Character;
   end record;

   function Conv is new Ada.Unchecked_Conversion (BR2, BR); --@UNCHECKED_CONVERSION:FAIL

begin
   pragma Assert (Z >= 0);
end;
