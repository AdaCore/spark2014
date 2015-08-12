with Ada.Synchronous_Task_Control;

package Task_And_SO_Arrays is

   type Task_Id is (A,B,C);

   task type T (Id : Task_Id := A);

   SOs : array (Task_Id) of Ada.Synchronous_Task_Control.Suspension_Object;
   Ts  : array (Task_Id) of T;

end;
