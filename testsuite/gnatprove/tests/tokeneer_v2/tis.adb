------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- TIS main program
--
-- Description:
--    Harness for the The TIS main program
--
-- Implementation Notes:
--    Not SPARK since it starts Support software first and
--    then determines whether to start the TIS Application.
------------------------------------------------------------------
with TISMain;

with Text_IO;
with TcpIP;

procedure TIS
  with SPARK_Mode => Off
is

  OK : Boolean;

   ------------------------------------------------------------------
   -- InitTestDevices
   --
   -- Description:
   --    Performs the Initialisation of the
   --    TCP/IP interface.
   --
   -- Implementation Notes:
   --    Uses Non-SPARK support package TCPIP.
   --
   -- Traceunit: C.TIS.InitTestDevices
   ------------------------------------------------------------------
   procedure InitTestDevices (Success : out Boolean)
   is
   begin
      TCPIP.Init(Success);
      if Success then
         TCPIP.OpenAll(Success);
         if not Success then
            Text_IO.Put_Line("Failed to connect to Test Drivers");
         end if;
      end if;
   end InitTestDevices;

   ------------------------------------------------------------------
   -- FinaliseTestDevices
   --
   -- Description:
   --    Performs the Finalisation of the
   --    TCP/IP interface.
   --
   -- Implementation Notes:
   --    Uses Non-SPARK support package TCPIP.
   --
   -- Traceunit: C.TIS.FinaliseTestDevices
   ------------------------------------------------------------------
   procedure FinaliseTestDevices
   is
   begin
      TCPIP.CloseAll;
   end FinaliseTestDevices;

--------------------------------------------------------------
-- begin TIS
--------------------------------------------------------------
begin

   InitTestDevices(Success => OK);

   if OK then
      TISMain;
   end if;

   FinaliseTestDevices;

end TIS;
