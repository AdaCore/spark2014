with Ada.Real_Time; use Ada.Real_Time;

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
      end Wait;
   end Store;

   The_Store : Store;

   procedure Entry_Call
     with Global => null
   is
   begin
      The_Store.Wait;
   end Entry_Call;

end Tasks;
