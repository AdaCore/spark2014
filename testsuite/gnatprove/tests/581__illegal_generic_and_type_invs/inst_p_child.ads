pragma SPARK_Mode;
with Gen.P_Child;
with Inst;

--  Instance outside Inst is rejected

procedure Inst_P_Child is new Inst.P_Child;
