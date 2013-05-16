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

--# inherit AuditLog,
--#         AuditTypes,
--#         BasicTypes,
--#         Clock,
--#         ConfigData;

package Display
--# own State;
--#     out Output;
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
                 DoorUnlocked
                 );


   -- MsgLineT represents a line of the message text
   subtype MsgTextCount is Natural range 0..23;
   subtype MsgTextI is MsgTextCount range 1..MsgTextCount'Last;
   subtype MsgTextT is String(MsgTextI);

   type MsgLineT is record
      Text : MsgTextT;
      Len  : MsgTextCount;
   end record;

   BlankLine : constant MsgLineT := MsgLineT'(
                                       Text => "                       ",
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

   procedure SetValue(Msg : in     MsgT);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Msg,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State              from *,
   --#                                 Msg;


   ------------------------------------------------------------------
   -- ChangeDoorUnlockedMsg
   --
   -- Description:
   --    If the current message is DoorUnlocked sets the internal
   --    display state to Msg.
   --
   -- Traceunit : C.Display.ChangeDoorUnlockedMsg
   -- TraceTo   : FD.Interface.DisplayPollUpdate
   ------------------------------------------------------------------

   procedure ChangeDoorUnlockedMsg(Msg : in     MsgT);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Msg,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State              from *,
   --#                                 Msg;


   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Updates the physical display to match the internal display
   --    state.
   --
   -- Traceunit : C.Display.UpdateDevice
   -- Traceto   : FD.Interface.UpdateDisplay
   ------------------------------------------------------------------

   procedure UpdateDevice;
   --# global in out State;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State,
   --#         Output             from State;


   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes the internal display state
   --
   -- Traceunit : C.Display.Init
   -- Traceto   : FD.TIS.TISStartup
   ------------------------------------------------------------------

   procedure Init(IsEnrolled : in Boolean);
   --# global out State;
   --# derives State from IsEnrolled;


end Display;
