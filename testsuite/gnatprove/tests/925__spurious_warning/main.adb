procedure Main is
   function Random return Integer is (Integer'Last);
   X : Integer := Random;
   Y : Integer;
begin
   Y := X + X;
   raise Program_Error;
exception
   when Program_Error =>
      null;
end Main;
