------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Text_IO;

with Raw_TCPEcho;
with AIP_Support.Mainloop;
with AIP.OSAL;
with AIP.OSAL.Single;
with AIP_Support.Time_Types;
with AIP_Support.Timers;

procedure Echop is
   use type AIP_Support.Time_Types.Time;

   Events : Integer;
   Prev_Clock, Clock  : AIP_Support.Time_Types.Time :=
                          AIP_Support.Time_Types.Time'First;

   Poll_Freq : constant := 100;
   --  100 ms

   --  Commented out until ARP and TCP are reimplemented

--     procedure tcp_fasttmr;
--     pragma Import (C, tcp_fasttmr, "tcp_fasttmr");
--
--     procedure tcp_slowtmr;
--     pragma Import (C, tcp_slowtmr, "tcp_slowtmr");
--
--     procedure etharp_tmr;
--     pragma Import (C, Etharp_Tmr, "etharp_tmr");

begin
   Ada.Text_IO.Put_Line ("*** IPStack starting ***");

   --  Initialize IP stack

   AIP.OSAL.Initialize;

   --  Initialize application services

   Raw_TCPEcho.Init;

   --  Run application main loop

   loop
      --  Process pending network events

      Events := AIP.OSAL.Single.Process_Interface_Events;

      --  Block for a while or do some stuff

      loop
         Clock := AIP_Support.Time_Types.Now;
         exit when Events > 0 or else Clock >= Prev_Clock + Poll_Freq;
      end loop;
      Prev_Clock := Clock;

      --  Fire timers as appropriate

--        if AIP.Timers.Timer_Fired (Clock, AIP.Timers.TIMER_EVT_TCPFASTTMR) then
--           tcp_fasttmr;
--        end if;
--
--        if AIP.Timers.Timer_Fired (Clock, AIP.Timers.TIMER_EVT_TCPSLOWTMR) then
--           tcp_slowtmr;
--        end if;
--
--        if AIP.Timers.Timer_Fired (Clock, AIP.Timers.TIMER_EVT_ETHARPTMR) then
--           etharp_tmr;
--        end if;
   end loop;
end Echop;
