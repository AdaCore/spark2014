with SPARK.Containers.Functional.Sets;

package P1 with SPARK_Mode is
   type C is private with Default_Initial_Condition;
   type E is private;
   function All_In (V : C) return Boolean
     with Ghost;
   procedure Lemma with
     Global => null,
     Ghost,
     Post => False;
private
   type E is new Integer with Type_Invariant => E >= 0, Default_Value => 0;
   package E_Set is new SPARK.Containers.Functional.Sets (E);
   --  Quantification on E_Set would be handled inconsistently inside and
   --  outside of P1. An invariant check should fail on iteration primitives.
   type C is new E_Set.Set;
   function All_In (V : C) return Boolean is
     (for all X of E_Set.Set (V) => X >= 0);
end P1;
