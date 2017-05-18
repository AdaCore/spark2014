package Circular is

   function F return Boolean is (True) with Global => C;

   C : constant Boolean := F;

end;
