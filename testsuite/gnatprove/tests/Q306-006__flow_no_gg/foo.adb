package body Foo
is

   G : Integer;

   procedure P (X : out Integer)
   is
   begin
      X := G;
   end P;

   function F (N : Integer) return Integer
   is
   begin
      return Integer'Max (G, N);
   end F;

   function E (N : Integer) return Integer is (Integer'Max (G, N));

begin

   G := 42;
   Public_G := 42;

end Foo;
