pragma SPARK_Mode;
with Gen.Child;
with Inst;

--  Instance outside Inst is rejected

package Inst_Child is new Inst.Child;
