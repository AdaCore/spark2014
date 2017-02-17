package body Foo
is


   procedure Test_01 (X, Y : in out Boolean)
   with Post => (X = Y'Old and Y = X'Old)
   is
   begin
      X := X xor Y;
      Y := X xor Y;
      X := X xor Y;
   end Test_01;

end Foo;
