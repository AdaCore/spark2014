procedure Main with SPARK_Mode is

   type R is record
      F, G : Integer;
   end record;
   subtype S is R with Predicate => S.F < S.G;

   function Test1 (X : R) return Boolean with
     Relaxed_Initialization => X
   is
   begin
      return (X in S); --@INIT_BY_PROOF:FAIL
   end Test1;

begin
   null;
end Main;
