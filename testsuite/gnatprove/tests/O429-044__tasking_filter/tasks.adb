with Ada.Real_Time; use Ada.Real_Time;
with Ada.Task_Identification;

package body Tasks is

   task body Task_With_Invalid_Discriminant is
   begin
      null;
   end;

   task body Timer
   is
      NextPeriod : Ada.Real_Time.Time := Ada.Real_Time.Clock;
   begin
      loop
         delay until NextPeriod;
         NextPeriod := NextPeriod + Ada.Real_Time.Seconds (1);
      end loop;
   end;

   task body Timer_Stub is separate;

   Last_Caller : Ada.Task_Identification.Task_Id;

   protected body Bad_Store is
      function Get return Integer is
      begin
         return The_Stored_Data;
      end;

      procedure Put (X : Integer) is
      begin
         The_Stored_Data := X;
         The_Guard := X > 0;
      end;

      entry Wait (Dummy : Integer) when The_Guard is
      begin
         null;
         Last_Caller := Wait'Caller;
         --  delay 1.0;
      end;
   end;

   protected body Simple is
      entry Dummy when True is
      begin
         null;
      end;
   end;

   protected body Store_Stub is separate;
   protected body Invalid_Protected_Stub is separate;

   The_Store : Bad_Store;
   The_Timer : Timer (10);

   The_Sub_Store : Bad_Store;
   The_Sub_Timer : Sub_Timer;

   -- single protected object

   protected Single_PO is
   end;

   protected body Single_PO is
   end;

   -- single task object

   task Single_Task is
   end;

   task body Single_Task is
   begin
      null;
   end;

   procedure Entry_Call
     with Global => null
   is
      B : Boolean;
   begin
      null;
      The_Store.Wait (0);
      if The_Timer'Terminated then
         B := The_Timer'Callable;
      else
         Last_Caller := The_Timer'Identity;
      end if;
   end;

   --  type Serial_Device is task interface;

   protected body Store_With_No_Initialization is
      entry Wait (Dummy : Integer) when True is
      begin
         null;
      end;
   end;

   protected body Null_Protected_Type is
   end;

   protected body Store_With_Mixed_Initialization is
      entry Wait (Dummy : Integer) when True is
      begin
         null;
      end;
   end;

end;
