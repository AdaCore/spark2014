with Ada.Synchronous_Task_Control;

package body Task_And_SO_Arrays is

   -------
   -- T --
   -------

   task body T is
   begin
      Ada.Synchronous_Task_Control.Suspend_Until_True (SOs (Id));
   end T;

end;
