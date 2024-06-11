pragma SPARK_Mode (On);

with P.Gen_Child;
function P.Gen_Child_Inst is new P.Gen_Child; -- @INVARIANT_CHECK:FAIL
