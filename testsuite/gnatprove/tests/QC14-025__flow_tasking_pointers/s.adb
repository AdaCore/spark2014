with Ada.Synchronous_Task_Control;

package body S is

   Obj : aliased Ada.Synchronous_Task_Control.Suspension_Object;
   Ptr : access Ada.Synchronous_Task_Control.Suspension_Object;

   procedure Dummy is
   begin
      Ada.Synchronous_Task_Control.Suspend_Until_True (Ptr.all);
   end;

end S;
