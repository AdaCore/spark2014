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
-- DoorAPI
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

with Ada.Strings.Fixed;
with TcpIp;
with MsgProc;

package body DoorAPI is

   function GetDoorStateRaw return DoorStateT
     with Global => null;
   --  Same as GetDoorState, compatible with SPARK (no exception handler)

   function GetDoorStateRaw return DoorStateT is
      InMsg     : TcpIp.MessageT;
      OutMsg    : constant TcpIp.MessageT :=
        (Data   =>
           Ada.Strings.Fixed.Overwrite(Source   => TcpIp.NullMsg.Data,
                                       Position => 1,
                                       New_Item => "door.getState()"),
         Length => 15);



      DoorState : DoorStateT := Error;
      IsOp,
      IsClosed,
      CommsIsOK : Boolean;
   begin
      TcpIp.SendAndReceive
        (IsAdmin  => False,
         Outgoing => OutMsg,
         Incoming => InMsg,
         Success  => CommsIsOK);

      if CommsIsOK then
         declare
            Msg       : String := MsgProc.GetResponseFromMsg (InMsg);
            StateDict : MsgProc.DictionaryT :=
               MsgProc.GetDictionary (Msg => Msg, Arg => 1);
         begin
            IsOp := Boolean'Value
              (MsgProc.GetStringByKey
                (Dic => StateDict, Key => "operational?"));
            pragma Annotate (GNATprove, Intentional,
                             "precondition might fail",
                             "Malformed input should trigger an exception here");
            IsClosed := Boolean'Value
              (MsgProc.GetStringByKey (Dic => StateDict, Key => "closed?"));
            pragma Annotate (GNATprove, Intentional,
                             "precondition might fail",
                             "Malformed input should trigger an exception here");
         end;

         if IsOp then
            if IsClosed then
               DoorState := Closed;
            else
               DoorState := Open;
            end if;
         end if;
      end if;

      return DoorState;
   end GetDoorStateRaw;

   ------------------------------------------------------------------
   -- GetDoorState
   --
   -- Implementation Notes:
   --    Set return value to Error if door state cannot be determined.
   --
   ------------------------------------------------------------------
   function GetDoorState return DoorStateT
     with SPARK_Mode => Off  --  exception handlers
   is
   begin
      return GetDoorStateRaw;
   exception
      when others =>
         return Error;
   end GetDoorState;

end DoorAPI;
