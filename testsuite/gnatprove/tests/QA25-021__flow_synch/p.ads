with Ada.Synchronous_Task_Control;

package P with Initializes => Obj is

   type R1 is record
      S : Ada.Synchronous_Task_Control.Suspension_Object;
   end record with Volatile;

   type R2 is record
      C1, C2 : R1;
   end record with Volatile;

   Obj : R2;
end;
