package body Foo is

   function F (X : Base_T) return Boolean
   is
   begin
      return G1;
   end F;

   function F (X : Derived_T) return Boolean
   is
   begin
      return G2;
   end F;

end Foo;
