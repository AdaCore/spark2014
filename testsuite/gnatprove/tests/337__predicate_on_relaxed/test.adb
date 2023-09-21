procedure Test (B : Boolean) with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   type RR is new R with
     Relaxed_Initialization,
     Ghost_Predicate => F'Initialized or G'Initialized;

   type RP is new R with
     Ghost_Predicate => F /= 0;

   X : R with Relaxed_Initialization;
   Y : RR;
   Z : RP with Relaxed_Initialization;
begin
   if B then
      X.F := 1;
      Y := RR (X);  -- @INIT_BY_PROOF:NONE @PREDICATE_CHECK:PASS
      Z := RP (X);  -- @INIT_BY_PROOF:FAIL @PREDICATE_CHECK:PASS
   else
      Y := RR (X);  -- @INIT_BY_PROOF:NONE @PREDICATE_CHECK:FAIL
   end if;
end Test;
