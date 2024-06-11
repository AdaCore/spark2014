pragma SPARK_Mode (On);

with P.Gen_Child;
private function P.Gen_Child_Inst_Priv is new P.Gen_Child; -- @INVARIANT_CHECK:NONE
