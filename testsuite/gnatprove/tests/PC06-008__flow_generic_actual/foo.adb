procedure Foo with Global => null
is

   X : Integer := 0;

   generic
      I : Integer;
   package GEN with
      Initializes => (J => I)
   is
      J : Integer := I;
   end GEN;

   package PACK is new GEN (X);

begin
   null;
end Foo;
