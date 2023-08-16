procedure Qualified_Expression with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post =>  False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is (R'(V).A = 1);

begin
   null;
end;
