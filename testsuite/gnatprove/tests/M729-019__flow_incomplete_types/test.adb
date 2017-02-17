package body Test
is


   procedure Test_01 (X : out Boolean)
   is
      type Foo;

      type Foo is record
         A : Integer;
         B : Integer;
      end record;

      R : Foo;
   begin
      R.A := 5;
      R.B := 12;
      X := R.A = R.B;
   end Test_01;

end Test;
