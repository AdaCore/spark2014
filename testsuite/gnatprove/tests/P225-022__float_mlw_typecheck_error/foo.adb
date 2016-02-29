--  This caused a very strange why3 error in the smtlib fp branch, so its
--  good to keep it as a regression test.
package body Foo
is

   type Type_A is digits 6 range -4096.0 .. 4096.0;
   pragma Assert (Float (Type_A'Base'First) = Float'First);

   type Type_B is
      record
         X : Type_A;
         Y : Type_A;
      end record;

   Null_Type_B : constant Type_B := Type_B'(X => 0.0, Y => 0.0);

   procedure Wibble
   is
      type Type_C is digits 15 range 0.0 .. 1.0;
   begin
      null;
   end Wibble;

end Foo;
