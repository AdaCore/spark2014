package Foo is

   type R is record
      A : Boolean;
      B : Boolean;
   end record;

   G1 : Boolean := False;
   G2 : R := (False, False);

   type Base_T is tagged null record;

   function Input_Rule (X : Base_T) return Boolean
   with Global => G1;

   procedure In_Out_Rule (X : Base_T)
   with Global => G1;

   procedure In_Out_Rule_2 (X : Base_T)
   with Global => (Output => G1);

   type Derived_T is new Base_T with null record;

   function Input_Rule (X : Derived_T) return Boolean
   with Global => G2;

   procedure In_Out_Rule (X : Derived_T)
   with Global => (In_Out => G1);

   procedure In_Out_Rule_2 (X : Derived_T)
   with Global => (In_Out => G1);

end Foo;
