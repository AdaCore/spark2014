pragma SPARK_Mode (On);
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package body Q is

   procedure Suspend (Arg : in out Ada.Synchronous_Task_Control.Suspension_Object) is
   begin
      Ada.Synchronous_Task_Control.Suspend_Until_True (Arg);
   end;

   task body TT1 is
   begin
      loop
         Suspend (SO);
      end loop;
   end;

   task body TT2 is
   begin
      loop
         Ada.Synchronous_Task_Control.Suspend_Until_True (SO);
      end loop;
   end;

end;
