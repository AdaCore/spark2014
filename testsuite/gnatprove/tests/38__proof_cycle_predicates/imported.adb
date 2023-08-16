procedure Imported with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post =>  False;

   subtype R is T with Predicate => F (R);

   function Imp (X : R) return Boolean with Import;

   function F (V : T) return Boolean
   is (Imp (V));

begin
   null;
end;
