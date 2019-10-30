with Interfaces; use Interfaces;
with Ada.Unchecked_Conversion;
procedure Unchecked_Conv with SPARK_Mode is
   function To_Signed is new Ada.Unchecked_Conversion (Source => Unsigned_64,
                                                       Target => Integer_64);
   function To_Unsigned is new Ada.Unchecked_Conversion (Source => Integer_64,
                                                         Target => Unsigned_64);
   X : constant Unsigned_64 := 0;
   Y : constant Integer_64 := To_Signed (X);
begin
   pragma Assert (To_Unsigned (Y) = X);
end Unchecked_Conv;
