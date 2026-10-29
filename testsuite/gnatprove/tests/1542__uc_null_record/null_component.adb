with Ada.Unchecked_Conversion;

procedure Null_Component with SPARK_Mode is
   type Byte is mod 2 ** 8 with Size => 8;
   type Empty is null record;
   type Source is record
      Nothing : Empty;
      Value   : Byte;
   end record with Size => 8;
   for Source use record
      Nothing at 0 range 0 .. -1;
      Value   at 0 range 0 .. 7;
   end record;
   function Convert is new Ada.Unchecked_Conversion (Source, Byte);
   X : Source := (Nothing => (null record), Value => 1);
   Y : Byte := Convert (X);
begin
   pragma Assert (Y = 1);
end Null_Component;
