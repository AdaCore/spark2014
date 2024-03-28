pragma SPARK_Mode;
with Gen.P_Child;
with Inst;

--  Instance as a child unit is OK, invariant check is required

procedure Inst.P_Child_I is new Inst.P_Child; --@INVARIANT_CHECK:FAIL
