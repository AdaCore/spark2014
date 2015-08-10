with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package body Two_Tasks_Single_SO is

   task body T1 is
   begin
      Suspend_Until_True (SO);
   end;

   task body T2 is
   begin
      Suspend_Until_True (SO);
   end;

end;
