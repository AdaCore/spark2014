pragma SPARK_Mode (On);
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

with Ada.Synchronous_Task_Control;

package P is

   procedure Suspend (Arg : in out Ada.Synchronous_Task_Control.Suspension_Object);

   SO : Ada.Synchronous_Task_Control.Suspension_Object;

   task type TT;

   TO1, TO2 : TT;

end;
