pragma SPARK_Mode;
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Task_Types is
   task type My_Task_Type (C : Natural := 0);

   T : My_Task_Type;
   T2 : My_Task_Type (1);

   procedure Do_Something (T1, T2 : My_Task_Type);

   procedure Call;
end Task_types;
