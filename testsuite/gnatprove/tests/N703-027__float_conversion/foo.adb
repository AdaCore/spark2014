package body Foo
is

   pragma Warnings (Off, "subprogram * has no effect");

   procedure Test_Err
   is
      type T is range 0 .. 2 ** 25 - 1;
      A : Float;
      B : T;
   begin
      A := Float (T'Last);
      B := T (A); -- @RANGE_CHECK:FAIL
   end Test_Err;

   procedure Test_Ok
   is
      type T is range 0 .. 2 ** 24 - 1;
      A : Float;
      B : T;
   begin
      A := Float (T'Last);
      B := T (A);
   end Test_Ok;

end Foo;
