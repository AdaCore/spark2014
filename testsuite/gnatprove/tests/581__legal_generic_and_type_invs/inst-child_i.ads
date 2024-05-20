pragma SPARK_Mode;
with Gen.Child;
with Inst;

--  Instance as a child unit is OK, invariant check is required

package Inst.Child_I is new Inst.Child;
