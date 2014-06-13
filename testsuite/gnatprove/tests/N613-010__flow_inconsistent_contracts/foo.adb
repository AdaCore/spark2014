package body Foo
is

   G : Integer;
   H : Integer;

   procedure P (X : Integer)
   with Depends => (H => X)
   is
   begin
      G := X;
   end P;

   procedure Test_01 (X : Integer)
   is
   begin
      P (X);
   end Test_01;

end Foo;
