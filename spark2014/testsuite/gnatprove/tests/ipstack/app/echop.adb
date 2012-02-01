------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2012, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with Raw_TCP_Echo;
with Raw_TCP_Dispatcher;
pragma Warnings (Off, Raw_TCP_Dispatcher);

with Raw_UDP_Syslog;
with Raw_UDP_Dispatcher;
pragma Warnings (Off, Raw_UDP_Dispatcher);

with Shell;

with AIP.IO;
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
   AIP.IO.Put_Line ("*** IPstack starting ***");

   --  Initialize IP stack

   AIP.OSAL.Initialize;

   --  Initialize application services

   Raw_TCP_Echo.Init;
   Raw_UDP_Syslog.Init;

   --  Run application main loop

   loop
      --  Process pending network events

      Events := AIP.OSAL.Single.Process_Interface_Events;

      --  Handle console interaction

      Shell.Poll;

      --  Block for a while or do some stuff

      loop
         Clock := AIP.Time_Types.Now;
         exit when Events > 0 or else Clock >= Prev_Clock + Poll_Freq;
      end loop;
      Prev_Clock := Clock;

      AIP.OSAL.Single.Process_Timers (Clock);
   end loop;
end Echop;
