with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;
package Semaphores2 with
  SPARK_Mode
is
   Semaphore1, Semaphore2 : Suspension_Object;
   task T1;
   task T2;
end Semaphores2;
