procedure T with
  SPARK_Mode
is
   type S is mod 2**8 with Static_Predicate => S > 0 and S /= 4;

   procedure Decr (X : in out S);

   procedure Decr (X : in out S) is
   begin
      X := S'Pred (X); -- @PREDICATE_CHECK:FAIL
   end Decr;
begin
   null;
end T;
