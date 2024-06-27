pragma SPARK_Mode (On);

with P.Gen_Priv_Child;
private function P.Gen_Priv_Child_Inst is new P.Gen_Priv_Child; -- @INVARIANT_CHECK:NONE
