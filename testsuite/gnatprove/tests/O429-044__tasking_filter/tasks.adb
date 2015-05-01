with Ada.Real_Time; use Ada.Real_Time;
with Ada.Task_Identification;

package body Tasks is

   --  Bad_Guard : Boolean;

   task body Timer
   is
      NextPeriod : Ada.Real_Time.Time := Ada.Real_Time.Clock;
   begin
      loop
         delay until NextPeriod;
         NextPeriod := NextPeriod + Ada.Real_Time.Seconds (1);
      end loop;
   end Timer;

   task body Timer_Stub is separate;

   Last_Caller : Ada.Task_Identification.Task_Id;

   protected body Store is
      function Get return Integer is
      begin
         return The_Stored_Data;
      end Get;

      procedure Put (X : Integer) is
      begin
         The_Stored_Data := X;
         The_Guard := X > 0;
      end Put;

      entry Wait when The_Guard is
      begin
         null;
         --  Last_Caller := Wait'Caller;
         --  delay 1.0;
      end Wait;
   end Store;

   protected body Store_Stub is separate;

   The_Store : Store;
   The_Timer : Timer;

   procedure Entry_Call
     with Global => null
   is
      B : Boolean;
   begin
      null;
      The_Store.Wait;
      --  B := The_Timer'Callable;
   end Entry_Call;

   task Single_Task;

   task body Single_Task is
   begin
      null;
   end Single_Task;

end Tasks;
