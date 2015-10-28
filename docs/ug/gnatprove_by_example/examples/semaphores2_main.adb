with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;
with Semaphores2; use Semaphores2;
procedure Semaphores2_Main with
  SPARK_Mode
is
begin
   Set_True (Semaphore1);
end Semaphores2_Main;
