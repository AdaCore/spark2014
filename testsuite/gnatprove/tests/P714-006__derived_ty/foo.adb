package body Foo
is

   procedure Test (A : in out Arr)
   is
      X : Arr := A;
   begin
      A (5) := False;
   end Test;

   procedure Dynamic (A, B : Integer) is
      type Arr is array (Positive range A .. B) of Boolean;
   begin
      null;
   end Dynamic;

end Foo;
