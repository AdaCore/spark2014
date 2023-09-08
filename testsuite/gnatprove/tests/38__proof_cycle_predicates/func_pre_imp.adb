procedure Func_Pre_Imp with SPARK_Mode is
   type T is new Integer;

   function F (X : T) return Boolean with Pre => True, Post => False;

   subtype S is T with Predicate => F (S);

   function Foo (X : S) return Boolean with Import;

   function G (X : T) return Boolean with Import, Pre => Foo (X);

   function F (X : T) return Boolean is
     (G (X));

begin
   null;
end;
