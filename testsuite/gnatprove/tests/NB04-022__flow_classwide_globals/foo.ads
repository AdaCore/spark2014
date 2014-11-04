package Foo is

   G1 : Boolean := False;
   G2 : Boolean := False;

   type Base_T is tagged null record;

   function F (X : Base_T) return Boolean
   with Global => G1;

   type Derived_T is new Base_T with null record;

   function F (X : Derived_T) return Boolean
   with Global => G2;

end Foo;
