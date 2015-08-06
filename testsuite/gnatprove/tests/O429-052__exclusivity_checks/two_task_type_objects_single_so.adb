with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package body Two_Task_Type_Objects_Single_SO is

   task body TT is
   begin
      Suspend_Until_True (SO);
   end;

   T1, T2 : TT;

end;
