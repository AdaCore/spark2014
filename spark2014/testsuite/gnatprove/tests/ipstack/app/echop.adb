------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Text_IO;

--  with Raw_TCPEcho;
--  TCP service temporarily deactivated???

with Raw_UDP_Syslog;
with Raw_UDP_Dispatcher;
pragma Warnings (Off, Raw_UDP_Dispatcher);

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

begin
   Ada.Text_IO.Put_Line ("*** IPStack starting ***");

   --  Initialize IP stack

   AIP.OSAL.Initialize;

   --  Initialize application services

   --  Raw_TCPEcho.Init;
   Raw_UDP_Syslog.Init;

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
