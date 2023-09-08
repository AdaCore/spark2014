procedure Recursive_Predicates with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Post => False;

   subtype R1 is T with Predicate => R2 (R1).A = 1;
   subtype R2 is T with Predicate => F (R1 (R2));

   function F (V : T) return Boolean is
   begin
      return R1 (V).A = 1;
   end F;
begin
   null;
end;
