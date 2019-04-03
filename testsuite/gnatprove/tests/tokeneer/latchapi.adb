------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- LatchAPI
--
-- Implementation Notes:
--    Uses SPREs door.lock() and door.unlock() methods
--
------------------------------------------------------------------
with TcpIp;
with Ada.Strings.Fixed;
with MsgProc;

package body LatchAPI is

   ------------------------------------------------------------------
   -- Local
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- ReadBack
   --
   -- Description:
   --    Gets the state of the latch.
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure ReadBack
     (IsLocked : out Boolean;
      Success  : out Boolean);

   procedure ReadBack
     (IsLocked : out Boolean;
      Success  : out Boolean)
     with SPARK_Mode => Off
   is
      InMsg     : TcpIp.MessageT;
      CommsIsOK : Boolean;
      OutMsg    : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "door.getState()"),
         Length => 15);

   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      declare
         Msg : String := MsgProc.GetResponseFromMsg(InMsg);
         StateDict : MsgProc.DictionaryT :=
           MsgProc.GetDictionary(Msg => Msg, Arg => 1);
      begin
         Success := Boolean'Value
           (MsgProc.GetStringByKey(Dic => StateDict,
                                   Key => "operational?"))
           and CommsIsOK;
         IsLocked := Boolean'Value
           (MsgProc.GetStringByKey(Dic => StateDict,
                                   Key => "locked?"));
      end;

   exception
      when E : others =>
         Success  := False;
         IsLocked := False;
   end ReadBack;

   ------------------------------------------------------------------
   -- Exported
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- Unlock
   --
   -- Implementation Notes:
   --    Performs readback to check the latch has changed state.
   --
   ------------------------------------------------------------------

   procedure Unlock(Failed : out Boolean) is
      InMsg  : TcpIp.MessageT with Unreferenced;
      OutMsg : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "door.unlock()"),
         Length => 13);



      IsLocked, CommsIsOK, ReadBackOK  : Boolean;

   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOk);

      if CommsIsOK then
         -- Check that latch state has actually changed
         ReadBack (IsLocked => IsLocked,
                   Success  => ReadBackOK);
         Failed := IsLocked or not ReadBackOK;
      else
         Failed := True;
      end if;
   end Unlock;

   ------------------------------------------------------------------
   -- Lock
   --
   -- Implementation Notes:
   --    Performs readback to check the latch has changed state.
   --
   ------------------------------------------------------------------

   procedure Lock (Failed : out Boolean) is
      InMsg  : TcpIp.MessageT with Unreferenced;
      OutMsg : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "door.lock()"),
         Length => 11);



     IsLocked, CommsIsOK, ReadBackOK : Boolean;

   begin
      TcpIp.SendAndReceive
        (IsAdmin  => False,
         Outgoing => OutMsg,
         Incoming => InMsg,
         Success  => CommsIsOk);

      if CommsIsOK then
         -- Check that latch state has actually changed
         ReadBack (IsLocked => IsLocked, Success  => ReadBackOK);
         Failed := not IsLocked or not ReadBackOK;
      else
         Failed := True;
      end if;
   end Lock;

end LatchAPI;
