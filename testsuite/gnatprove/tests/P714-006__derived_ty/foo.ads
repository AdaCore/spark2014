package Foo
is

   type Arr is array (Positive range 0 .. 100) of Boolean; --@RANGE_CHECK:FAIL

   procedure Test (A : in out Arr)
   with Post => A (5) = True;

end Foo;
