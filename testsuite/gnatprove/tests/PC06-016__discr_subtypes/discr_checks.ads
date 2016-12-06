pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Discr_Checks with SPARK_Mode is

   function Bad return Integer is (6);

   procedure Check_Subtype_Rec;

   procedure Check_Derived_Rec;

   procedure Check_Subtype_Priv;

   procedure Check_Derived_Priv;

   procedure Check_Subtype_Prot;

   procedure Check_Derived_Prot;

   procedure Check_Subtype_Task;

   procedure Check_Derived_Task;
end Discr_Checks;
