package Foo
is

   type Arr is array (Positive range 0 .. 100) of Boolean;

   procedure Test (A : in out Arr)
   with Pre => A'Length = 100,
        Post => A (5) = True;

end Foo;
