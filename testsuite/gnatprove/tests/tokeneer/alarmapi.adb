------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- AlarmAPI
--
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with TcpIp;
with MsgProc;
with Ada.Strings.Fixed;

package body AlarmAPI
  with SPARK_Mode => On
is

   ------------------------------------------------------------------
   -- Activate
   --
   -- Implementation Notes:
   --    Don't check whether alarm is activated or not.
   --
   ------------------------------------------------------------------
   procedure Activate
   is
      InMsg     : TcpIp.MessageT;
      OutMsg    : constant TcpIp.MessageT :=
        (Data   =>
           Ada.Strings.Fixed.Overwrite(Source   => TcpIp.NullMsg.Data,
                                       Position => 1,
                                       New_Item => "alarm.activate()"),
         Length => 16);



      CommsIsOK : Boolean;
   begin
      TcpIp.SendAndReceive (IsAdmin  => True,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOk);
   end Activate;

   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Implementation Notes:
   --    Don't check whether alarm is deactivated or not.
   --
   ------------------------------------------------------------------
   procedure Deactivate
   is
      InMsg     : TcpIp.MessageT;
      OutMsg    : constant TcpIp.MessageT :=
        (Data   =>
           Ada.Strings.Fixed.Overwrite(Source   => TcpIp.NullMsg.Data,
                                       Position => 1,
                                       New_Item => "alarm.deactivate()"),
         Length => 18);



      CommsIsOK : Boolean;
   begin
      TcpIp.SendAndReceive (IsAdmin  => True,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOk);
   end Deactivate;

end AlarmAPI;
