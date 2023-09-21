procedure Func_Formal with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with Pre => True, Post => False;

   subtype S is T with Predicate => F (S);

   function G (X : S) return Boolean is (X = 1);

   function F (X : T) return Boolean is
     (G (X));

begin
   null;
end;
