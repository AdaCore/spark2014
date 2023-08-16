procedure Pkg_Decl with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
      package Nested is
         V1 : R;
      end Nested;
   begin
      return True;
   end F;

begin
   null;
end;
