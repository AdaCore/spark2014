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

with Admin,
     AlarmTypes,
     AuditLog,
     AuditTypes,
     Clock,
     ConfigData,
     Door,
     IandATypes,
     PrivTypes,
     Stats;

package Screen
  with Abstract_State => (State,
                          (Output with External => Async_Readers))
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
   procedure SetMessage (Msg : in     MsgTextT)
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
   -- UpdateScreen
   --
   -- Description:
   --    Updates the physical screen.
   --    May raise a system fault.
   --
   -- Traceunit: C.Screen.UpdateScreen
   -- Traceto: FD.Interfac.UpdateScreen
   -- Traceto: FD.Interfac.TISUpdates
   ------------------------------------------------------------------
   procedure UpdateScreen
     (TheStats : in    Stats.T;
      TheAdmin : in    Admin.T)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Door.State),
                      Output => Output,
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State,
                                 State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Door.State,
                                               State,
                                               TheAdmin,
                                               TheStats),
                      Output               => (AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Door.State,
                                               State,
                                               TheAdmin,
                                               TheStats),
                      State                =>+ (AuditLog.State,
                                                ConfigData.State,
                                                Door.State,
                                                TheAdmin,
                                                TheStats));

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
   procedure Init (IsEnrolled : in    Boolean)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State),
                      Output => (Output,
                                 State),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => ((AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               IsEnrolled),
                      (Output,
                       State)              => IsEnrolled);

end Screen;
