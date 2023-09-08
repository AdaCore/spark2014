procedure Pkg_Body with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
      package Nested is
         B : Boolean;
      end Nested;

      package body Nested is
      begin
         B := (R (V).A = 1);
      end Nested;
   begin
      return True;
   end F;

begin
   null;
end;
