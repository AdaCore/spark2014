package body Foo
is
   subtype Angle is Float range 0.0 .. 360.0;

   procedure Test_01 (A, B : Angle;
                      C    : out Angle)
   is
   begin
      C := Float'Remainder (A + B, Angle'Last);
   end Test_01;

end Foo;
