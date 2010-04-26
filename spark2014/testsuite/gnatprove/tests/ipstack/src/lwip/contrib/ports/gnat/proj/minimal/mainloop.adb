------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Time_Types;
with Timers;

with Ada.Text_IO; use Ada.Text_IO;

procedure Mainloop is
   use type Time_Types.Time;

   Events : Integer;
   Prev_Clock, Clock  : Time_Types.Time := Time_Types.Time'First;

   Poll_Freq : constant := 100;
   --  100 ms

   procedure tcp_fasttmr;
   pragma Import (C, tcp_fasttmr, "tcp_fasttmr");

   procedure tcp_slowtmr;
   pragma Import (C, tcp_slowtmr, "tcp_slowtmr");

   procedure etharp_tmr;
   pragma Import (C, etharp_tmr, "etharp_tmr");

   function Process_Interface_Events return Integer is
   begin
      --  No interface defined yet

      return 0;
   end Process_Interface_Events;

begin
   Put_Line ("Mainloop: enter");
   loop
      Events := Process_Interface_Events;

      loop
         Clock := Time_Types.Now;
         exit when Events > 0 or else Clock >= Prev_Clock + Poll_Freq;
      end loop;

      Prev_Clock := Clock;

      if Timers.Timer_Fired (Clock, Timers.TIMER_EVT_TCPFASTTMR) then
         tcp_fasttmr;
      end if;

      if Timers.Timer_Fired (Clock, Timers.TIMER_EVT_TCPSLOWTMR) then
         tcp_slowtmr;
      end if;

      if Timers.Timer_Fired (Clock, Timers.TIMER_EVT_ETHARPTMR) then
         etharp_tmr;
      end if;
   end loop;
end Mainloop;
