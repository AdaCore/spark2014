package body Foo
is

   procedure Test (A : in out Arr)
   is
      X : Arr := A;
   begin
      A (5) := False;
   end Test;

end Foo;
