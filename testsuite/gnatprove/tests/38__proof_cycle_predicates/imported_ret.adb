procedure Imported_Ret with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post =>  False;

   subtype R is T with Predicate => F (R);

   function Imp (X : Integer) return R with Import;

   function F (V : T) return Boolean
   is (Imp (V.A).A = 1);

begin
   null;
end;
