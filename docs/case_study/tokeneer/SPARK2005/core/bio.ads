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
-- Bio
--
-- Description:
--    The TIS core interface to the biometric device.
--
------------------------------------------------------------------
with BasicTypes,
     IandATypes;
use type IandATypes.TemplateT;
--# inherit AuditLog,
--#         AuditTypes,
--#         BasicTypes,
--#         Clock,
--#         ConfigData,
--#         IandATypes;

package Bio
--# own in Input;
is


   ------------------------------------------------------------------
   -- Poll
   --
   -- Description:
   --    Determines whether a finger is present at the biometric reader.
   --    Only logs system fault - does not log a 'FingerDetected' or
   --    'FingerTimeout' element.
   --
   -- Traceunit : C.Bio.Poll
   -- Traceto   : FD.Interface.TISPoll
   ------------------------------------------------------------------

   procedure Poll(FingerPresent :    out BasicTypes.PresenceT);
   --# global in Input;
   --# derives FingerPresent from Input;


   ------------------------------------------------------------------
   -- Verify
   --
   -- Description:
   --    Attempts to verify the current sample against the template.
   --    Only logs system fault - does not log a 'Finger(Not)Matched' element.
   --
   -- Traceunit : C.Bio.Verify
   -- Traceto   : FD.Types.Fingerprint
   ------------------------------------------------------------------
   procedure Verify(Template       : in     IandATypes.TemplateT;
                    MaxFAR         : in     IandATypes.FarT;
                    MatchResult    :    out IandATypes.MatchResultT;
                    AchievedFAR    :    out IandATypes.FarT);
   --# global in     Input;
   --#        in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from Input,
   --#                                 AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Template,
   --#                                 Clock.Now,
   --#                                 ConfigData.State &
   --#         MatchResult        from Input,
   --#                                 Template,
   --#                                 MaxFAR &
   --#         AchievedFAR        from Input,
   --#                                 Template;


   ------------------------------------------------------------------
   -- Flush
   --
   -- Description:
   --    Flushes the Bio device of stale data.
   --
   -- Traceunit : C.Bio.Flush
   -- Traceto   : FD.Interface.FlushFingerData
   ------------------------------------------------------------------
   procedure Flush;
   --# global in Input;
   --# derives null from Input;

end Bio;
