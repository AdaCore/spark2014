------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Text_IO;

with Raw_TCPEcho;
with AIP.OSAL;
with AIP.OSAL.Single;
with AIP.Time_Types;
with AIP.Timers;

procedure Echop is
   use type AIP.Time_Types.Time;

   Events : Integer;
   Prev_Clock, Clock  : AIP.Time_Types.Time := AIP.Time_Types.Time'First;

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
         Clock := AIP.Time_Types.Now;
         exit when Events > 0 or else Clock >= Prev_Clock + Poll_Freq;
      end loop;
      Prev_Clock := Clock;

      AIP.OSAL.Single.Process_Timers (Clock);
   end loop;
end Echop;
