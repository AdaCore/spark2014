with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package body Task_Type_Array_Single_SO is

   task body TT is
   begin
      Suspend_Until_True (SO);
   end;

   type one_two_three is range 1 .. 3;
   Task_Array : array (one_two_three) of TT;

end;
