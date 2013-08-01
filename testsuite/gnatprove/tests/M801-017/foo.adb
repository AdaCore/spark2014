procedure Foo (X : out Integer)
is

   procedure Test_01
     with Global => (In_Out => X)
   is
   begin
      X := X + 1;
   end Test_01;

   procedure Test_02
     with Global => (In_Out => X),
          Depends => (X => X)
   is
   begin
      X := X + 1;
   end Test_02;

begin

   X := 0;
   Test_01;
   Test_02;

end Foo;

