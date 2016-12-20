pragma SPARK_Mode (On);
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

with Ada.Synchronous_Task_Control;

package Q is

   procedure Suspend (Arg : in out Ada.Synchronous_Task_Control.Suspension_Object);

   SO : Ada.Synchronous_Task_Control.Suspension_Object;

   task type TT1;
   task type TT2;

   TO1 : TT1;
   TO2 : TT2;

end;
