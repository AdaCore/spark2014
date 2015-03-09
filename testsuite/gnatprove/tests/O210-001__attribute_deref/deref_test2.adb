with System; use System;
procedure Deref_Test2 is
   X : Integer := 4;
   Y : Address := X'Address;
begin
   if Integer'Deref (Y) /= 4 then
      raise Program_Error;
   end if;
   Integer'Deref (Y) := 3;
   if Integer'Deref (Y) /= 3 then
      raise Program_Error;
   end if;
end Deref_Test2;
