with SPARK.Containers.Functional.Sets;
package P3.Child with SPARK_Mode is
   type C is private with Default_Initial_Condition;
   package E_Set is new SPARK.Containers.Functional.Sets (E);
   --  Quantification on E_Set are handled consistently inside and
   --  outside of P3.Child. There should be no failed checks.
   function All_In (V : C) return Boolean with Ghost;
   procedure Lemma with
     Global => null,
     Ghost,
     Post => False;
private
   type C is new E_Set.Set;
   function All_In (V : C) return Boolean is
     (for all X of E_Set.Set (V) => X >= 0);
end P3.Child;
