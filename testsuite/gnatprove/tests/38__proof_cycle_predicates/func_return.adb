procedure Func_Return with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with Pre => True, Post => False;

   subtype S is T with Predicate => F (S);

   function G (X : T) return S is (0);

   function F (X : T) return Boolean is
     (G (X) = 0);

begin
   null;
end;
