with System; use System;
with Interfaces.C; use Interfaces.C;

package Worker_Pack
  with SPARK_Mode
is
   -- Types
   subtype Pvoid is System.Address;

   type Action is (Log_Run, Neo_Pixel_Ring, None);

   type Worker_Work is record
      Func : Action;
      Arg  : Pvoid;
   end record;

   -- Constants and Global Variables
   WORKER_QUEUE_LENGTH : constant Natural := 5;

   Worker_Queue : Pvoid := System.Null_Address;

   -- Procedures and Functions
   procedure Worker_Init;
   pragma Export(C, Worker_Init, "ada_workerInit");

   function Worker_Test return Integer;
   pragma Export(C, Worker_Test, "ada_workerTest");

   procedure Worker_Loop;
   pragma Export(C, Worker_Loop, "ada_workerLoop");

   function Worker_Schedule(Func_ID : Integer; Arg : Pvoid) return Integer;
   pragma Export(C, Worker_Schedule, "ada_workerSchedule");

   procedure Log_Run_Worker (Arg : Pvoid);

   procedure Neo_Pixel_Ring_Worker (Arg : Pvoid);

end Worker_Pack;
