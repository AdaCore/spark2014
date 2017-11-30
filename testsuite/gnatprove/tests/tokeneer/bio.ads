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
with AuditLog,
     AuditTypes,
     CommonTypes,
     Clock,
     ConfigData,
     IandATypes;

package Bio
  with Abstract_State => (Input with External => Async_Writers)
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
   -- Traceto   : FD.Interfac.TISPoll
   ------------------------------------------------------------------
   procedure Poll (FingerPresent :    out CommonTypes.PresenceT)
     with Global  => Input,
          Depends => (FingerPresent => Input);

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
   procedure Verify (Template    : in     IandATypes.TemplateT;
                     MaxFAR      : in     IandATypes.FarT;
                     MatchResult :    out IandATypes.MatchResultT;
                     AchievedFAR :    out IandATypes.FarT)
     with Global  => (Input  => (Clock.Now,
                                 ConfigData.State,
                                 Input),
                      In_Out => (AuditLog.FileState,
                                 AuditLog.State)),
          Depends => (AchievedFAR          => (Input,
                                               Template),
                      (AuditLog.FileState,
                       AuditLog.State)     => (AuditLog.FileState,
                                               AuditLog.State,
                                               Clock.Now,
                                               ConfigData.State,
                                               Input,
                                               Template),
                      MatchResult          => (Input,
                                               MaxFAR,
                                               Template));

   ------------------------------------------------------------------
   -- Flush
   --
   -- Description:
   --    Flushes the Bio device of stale data.
   --
   -- Traceunit : C.Bio.Flush
   -- Traceto   : FD.Interfac.FlushFingerData
   ------------------------------------------------------------------
   procedure Flush
     with Global  => Input,
          Depends => (null => Input);

end Bio;
