with System; use System;
procedure Deref_Test is
   X : Integer := 4;
   Y : Address := X'Address;
begin
   if Integer'Deref (Y) /= 4 then
      raise Program_Error;
   end if;
end Deref_Test;
