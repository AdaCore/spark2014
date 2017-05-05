package Bar with SPARK_Mode is
   subtype B is Boolean with Predicate => B = True;
   function Ident (X : B) return B is (X);
   function Bizarre (X : Boolean) return B is (Ident (X));
   procedure P;
end Bar;
