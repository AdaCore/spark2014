with System; use System;
with System.Storage_Elements; use System.Storage_Elements;
procedure Main is

   X : Integer_Address := 1;
   Y : Integer_Address := To_Integer (To_Address (1));
   Z : Address := To_Address (X) + Storage_Offset'(2);
   U : Address := Storage_Offset'(2) + To_Address (X);
begin
   pragma Assert (X = Y);
   pragma Assert (To_Integer (Z) = 3);
end Main;
