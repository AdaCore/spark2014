with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;
package Semaphores1 with
  SPARK_Mode
is
   Semaphore : Suspension_Object;
   task T1;
   task T2;
end Semaphores1;
