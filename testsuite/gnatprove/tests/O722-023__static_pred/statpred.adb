procedure Statpred
  with SPARK_Mode
is
   subtype T is Integer with Static_Predicate => T < -1 or T > 1;
   function Id (X : Integer) return Integer is (X);
begin
   pragma Assert (Id(2) in T);      --  @ASSERT:PASS
   pragma Assert (Id(-2) in T);     --  @ASSERT:PASS
   pragma Assert (Id(0) not in T);  --  @ASSERT:PASS
end Statpred;
