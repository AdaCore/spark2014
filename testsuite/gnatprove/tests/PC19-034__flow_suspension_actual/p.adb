pragma SPARK_Mode (On);
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package body P is

   procedure Suspend (Arg : in out Ada.Synchronous_Task_Control.Suspension_Object) is
   begin
      Ada.Synchronous_Task_Control.Suspend_Until_True (Arg);
   end;

   task body TT is
   begin
      loop
         Suspend (SO);
      end loop;
   end;

end;
