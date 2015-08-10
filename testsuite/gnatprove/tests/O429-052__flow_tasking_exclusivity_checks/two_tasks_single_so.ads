with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package Two_Tasks_Single_SO is

   SO : Suspension_Object;

   task T1;

   task T2;

end;
