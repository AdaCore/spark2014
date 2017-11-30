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
with AdminToken,
     AlarmTypes,
     AuditLog,
     Clock,
     ConfigData,
     Display,
     Door,
     Keyboard,
     Latch,
     PrivTypes,
     UserEntry,
     UserToken;

use AdminToken,
    AlarmTypes,
    Clock,
    Door,
    Latch,
    PrivTypes;

package Poll is

   ------------------------------------------------------------------
   -- Activity
   --
   -- Description:
   --    Performs the TIS poll activity
   --
   -- Traceunit: C.Poll.Activity
   -- Traceto: FD.Interfac.Poll
   ------------------------------------------------------------------
   procedure Activity (SystemFault :    out Boolean)
     with Global  => (Input  => (AdminToken.Input,
                                 Clock.Now,
                                 ConfigData.State,
                                 Door.Input,
                                 Keyboard.Inputs,
                                 UserEntry.State,
                                 UserToken.Input),
                      Output => Clock.CurrentTime,
                      In_Out => (AdminToken.State,
                                 AdminToken.Status,
                                 AuditLog.FileState,
                                 AuditLog.State,
                                 Display.State,
                                 Door.State,
                                 Latch.State,
                                 UserToken.State,
                                 UserToken.Status)),
          Depends => (AdminToken.State =>+ (AdminToken.Input,
                                            AdminToken.Status),

                      (AdminToken.Status,
                       UserToken.Status) =>+ null,

                      (AuditLog.FileState,
                       AuditLog.State) => (AdminToken.State,
                                           AdminToken.Status,
                                           AuditLog.FileState,
                                           AuditLog.State,
                                           Clock.Now,
                                           ConfigData.State,
                                           Display.State,
                                           Door.Input,
                                           Door.State,
                                           Latch.State,
                                           UserEntry.State,
                                           UserToken.State,
                                           UserToken.Status),

                      Clock.CurrentTime => Clock.Now,

                      Display.State =>+ (Clock.Now,
                                         Latch.State,
                                         UserEntry.State),

                      Door.State =>+ (Clock.Now,
                                      Door.Input,
                                      Latch.State),

                      Latch.State =>+ Clock.Now,

                      SystemFault => Door.Input,

                      UserToken.State =>+ (UserToken.Input,
                                           UserToken.Status),

                      null => Keyboard.Inputs),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to Activity, the security property --
          -- holds.                                             --
          --------------------------------------------------------
          Post    =>
            ((Latch.IsLocked and
              Door.TheCurrentDoor = Door.Open and
              Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                       Door.Alarm_Timeout)) =
               (Door.TheDoorAlarm = AlarmTypes.Alarming)) and
            AdminToken.IsGood'Old = AdminToken.IsGood and
            AdminToken.AuthCertValid'Old = AdminToken.AuthCertValid and
            ((AdminToken.TheAuthCertRole'Old = PrivTypes.Guard) =
               (AdminToken.TheAuthCertRole = PrivTypes.Guard)) and
            (Latch.IsLocked = Clock.GreaterThanOrEqual(Clock.TheCurrentTime,
                                                       Latch.Latch_Timeout)) and
            Latch.Latch_Timeout = Latch.Latch_Timeout'Old;

end Poll;
