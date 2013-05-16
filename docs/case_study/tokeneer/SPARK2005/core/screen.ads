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
-- Screen
--
-- Description:
--    Maintains the Administrators Screen
--
------------------------------------------------------------------

with Stats;
with Admin;
--# inherit
--#    AlarmTypes,
--#    AuditLog,
--#    Clock,
--#    PrivTypes,
--#    AuditTypes,
--#    Door,
--#    ConfigData,
--#    IandATypes,
--#    Admin,
--#    Stats;

package Screen
--# own State,
--#     out Output;

is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   type MsgTextT is (Clear,
                     WelcomeAdmin,
                     Busy,
                     RemoveAdminToken,
                     CloseDoor,
                     RequestAdminOp,
                     DoingOp,
                     InvalidRequest,
                     InvalidData,
                     ArchiveFailed,
                     InsertEnrolmentData,
                     ValidatingEnrolmentData,
                     EnrolmentFailed,
                     InsertBlankFloppy,
                     InsertConfigData);

   ------------------------------------------------------------------
   -- SetMessage
   --
   -- Description:
   --    Sets the new value of the screen message.
   --
   -- Traceunit: C.Screen.SetMessage
   -- Traceto: FD.RealWorld.State
   --
   ------------------------------------------------------------------

   procedure SetMessage (Msg : in     MsgTextT);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 Msg,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         State              from *,
   --#                                 Msg;


   ------------------------------------------------------------------
   -- UpdateScreen
   --
   -- Description:
   --    Updates the physical screen.
   --    May raise a system fault.
   --
   -- Traceunit: C.Screen.UpdateScreen
   -- Traceto: FD.Interface.UpdateScreen
   -- Traceto: FD.Interface.TISUpdates
   ------------------------------------------------------------------

   procedure UpdateScreen
     (TheStats : in    Stats.T;
      TheAdmin : in    Admin.T);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     Door.State;
   --#        in out State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from State,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheStats,
   --#                                 Door.State,
   --#                                 TheAdmin &
   --#         State              from *,
   --#                                 AuditLog.State,
   --#                                 ConfigData.State,
   --#                                 TheStats,
   --#                                 Door.State,
   --#                                 TheAdmin &
   --#         Output             from State,
   --#                                 AuditLog.State,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 TheStats,
   --#                                 Door.State,
   --#                                 TheAdmin;

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the screen, the message presented will depend on
   --    whether the system is enrolled or not.
   --    May raise a system fault.
   --
   -- Traceunit: C.Screen.UpdateScreen
   -- Traceto: FD.TIS.TISStartup
   --
   ------------------------------------------------------------------

   procedure Init
     (IsEnrolled : in    Boolean);
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out State;
   --#           out Output;
   --# derives State,
   --#         Output             from IsEnrolled &
   --#         AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 IsEnrolled;


end Screen;
