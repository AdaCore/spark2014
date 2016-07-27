package Foo
is

   type Arr is array (Positive range 1 .. 100) of Boolean;

   procedure Test (A : in out Arr)
   with Post => A (5) = True;

end Foo;
