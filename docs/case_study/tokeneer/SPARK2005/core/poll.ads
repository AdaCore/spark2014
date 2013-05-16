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
-- Poll
--
-- Description:
--    Utility package providing the polling functions of the TIS core.
--
------------------------------------------------------------------
--# inherit
--#    AdminToken,
--#    AlarmTypes,
--#    AuditLog,
--#    Clock,
--#    ConfigData,
--#    Display,
--#    Door,
--#    Keyboard,
--#    Latch,
--#    PrivTypes,
--#    UserEntry,
--#    UserToken;

package Poll
is

   ------------------------------------------------------------------
   -- Activity
   --
   -- Description:
   --    Performs the TIS poll activity
   --
   -- Traceunit: C.Poll.Activity
   -- Traceto: FD.Interface.Poll
   ------------------------------------------------------------------

   procedure Activity (SystemFault :    out Boolean);
   --# global in     Door.Input;
   --#        in     Clock.Now;
   --#        in     UserEntry.State;
   --#        in     ConfigData.State;
   --#        in     Keyboard.Input;
   --#        in     UserToken.Input;
   --#        in     AdminToken.Input;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out Display.State;
   --#        in out Door.State;
   --#        in out Latch.State;
   --#        in out UserToken.Status;
   --#        in out AdminToken.State;
   --#        in out AdminToken.Status;
   --#        in out UserToken.State;
   --#           out Clock.CurrentTime;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Display.State,
   --#                                 Door.State,
   --#                                 Door.Input,
   --#                                 Clock.Now,
   --#                                 Latch.State,
   --#                                 AdminToken.Status,
   --#                                 AdminToken.State,
   --#                                 UserToken.Status,
   --#                                 UserToken.State,
   --#                                 UserEntry.State,
   --#                                 ConfigData.State &
   --#         Display.State      from *,
   --#                                 Clock.Now,
   --#                                 Latch.State,
   --#                                 UserEntry.State &
   --#         Door.State         from *,
   --#                                 Door.Input,
   --#                                 Clock.Now,
   --#                                 Latch.State &
   --#         Latch.State        from *,
   --#                                 Clock.Now &
   --#         UserToken.Status   from * &
   --#         UserToken.State    from *,
   --#                                 UserToken.Status,
   --#                                 UserToken.Input &
   --#         AdminToken.Status  from * &
   --#         AdminToken.State   from *,
   --#                                 AdminToken.Status,
   --#                                 AdminToken.Input &
   --#         SystemFault        from Door.Input &
   --#         Clock.CurrentTime  from Clock.Now &
   --#         null               from Keyboard.Input;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to Activity, the security property --
   --#      -- holds.                                             --
   --#      --------------------------------------------------------
   --#      ( ( Latch.IsLocked(Latch.State) and
   --#          Door.TheCurrentDoor(Door.State) = Door.Open and
   --#          Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                                   Door.prf_alarmTimeout(Door.State)) ) <->
   --#        Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ) and
   --#
   --#      ( AdminToken.prf_isGood(AdminToken.State~) <->
   --#           AdminToken.prf_isGood(AdminToken.State) ) and
   --#      ( AdminToken.prf_authCertValid(AdminToken.State~) <->
   --#           AdminToken.prf_authCertValid(AdminToken.State) ) and
   --#      ( AdminToken.TheAuthCertRole(AdminToken.State~) = PrivTypes.Guard <->
   --#           AdminToken.TheAuthCertRole(AdminToken.State) = PrivTypes.Guard ) and
   --#
   --#      ( Latch.IsLocked(Latch.State) <->
   --#        Clock.GreaterThanOrEqual(Clock.TheCurrentTime(Clock.CurrentTime),
   --#                               Latch.prf_LatchTimeout(Latch.State)) ) and
   --#      ( Latch.IsLocked(Latch.State~) ->
   --#                   ( Latch.State = Latch.State~ and Latch.IsLocked(Latch.State) ) ) and
   --#      Latch.prf_LatchTimeout(Latch.State) = Latch.prf_LatchTimeout(Latch.State~);


end Poll;













