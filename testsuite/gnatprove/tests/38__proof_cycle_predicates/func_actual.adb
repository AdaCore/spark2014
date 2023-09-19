procedure Func_Actual with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with Pre => True, Post => False;

   subtype S is T with Predicate => F (S);

   V : constant S := 1;

   function G (X : S) return Boolean is (X = 1);

   function F (X : T) return Boolean is
     (G (V));
begin
   null;
end;
