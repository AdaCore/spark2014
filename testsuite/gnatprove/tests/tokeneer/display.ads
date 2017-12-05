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
-- Display
--
-- Description:
--    Provides the interface to the display used to prompt a
--    user attempting to enter the enclave.
--
------------------------------------------------------------------

with AuditLog,
     AuditTypes,
     CommonTypes,
     Clock,
     ConfigData;

package Display
  with Abstract_State => (State,
                          (Output with External => Async_Readers)),
       Initializes => Output
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- MsgT
   --
   -- Description:
   --    The possible messages to be displayed
   --
   -- Traceunit : C.Display.Msg
   -- Traceto   : FD.Types.RealWorld
   -------------------------------------------------------------------
   type MsgT is (Blank,
                 Welcome,
                 InsertFinger,
                 OpenDoor,
                 Wait,
                 RemoveToken,
                 TokenUpdateFailed,
                 DoorUnlocked);


   -- MsgLineT represents a line of the message text
   subtype MsgTextCount is Natural range 0..23;
   subtype MsgTextI is MsgTextCount range 1..MsgTextCount'Last;
   subtype MsgTextT is String(MsgTextI);

   type MsgLineT is record
      Text : MsgTextT;
      Len  : MsgTextCount;
   end record;

   BlankLine : constant MsgLineT :=
     MsgLineT'(Text => "                       ",
               Len  => 0);

   -- MsgStrT represents the whole of a message, written over two lines
   type MsgStrT is record
      Top    : MsgLineT;
      Bottom : MsgLineT;
   end record;


   -- ScrollStrT represents a line of scrollable text
   MaxScrollSize : constant := 50;
   subtype ScrollTextCount is Natural range 0..MaxScrollSize;
   subtype ScrollTextI is ScrollTextCount range 1..ScrollTextCount'Last;
   subtype ScrollTextT is String(ScrollTextI);

   type ScrollStrT is record
      Text : ScrollTextT;
      Len  : ScrollTextCount;
   end record;


   ------------------------------------------------------------------
   -- SetValue
   --
   -- Description:
   --    Sets the internal display state to Msg.
   --
   -- Traceunit : C.Display.SetValue
   -- Traceto   : FD.AuditLog.LogChange
   ------------------------------------------------------------------
   procedure SetValue (Msg : in     MsgT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Msg,
                                               State),
                      State                =>+ Msg);

   ------------------------------------------------------------------
   -- ChangeDoorUnlockedMsg
   --
   -- Description:
   --    If the current message is DoorUnlocked sets the internal
   --    display state to Msg.
   --
   -- Traceunit : C.Display.ChangeDoorUnlockedMsg
   -- TraceTo   : FD.Interfac.DisplayPollUpdate
   ------------------------------------------------------------------
   procedure ChangeDoorUnlockedMsg (Msg : in     MsgT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Msg,
                                               State),
                      State                =>+ Msg);

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Updates the physical display to match the internal display
   --    state.
   --
   -- Traceunit : C.Display.UpdateDevice
   -- Traceto   : FD.Interfac.UpdateDisplay
   ------------------------------------------------------------------
   procedure UpdateDevice
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 Output,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               State),
                      Output               =>+ State,
                      State                =>+ null);

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the internal display state
   --
   -- Traceunit : C.Display.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------
   procedure Init (IsEnrolled : in Boolean)
     with Global  => (Output => State),
          Depends => (State => IsEnrolled);

end Display;
