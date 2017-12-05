with Door; use Door;
with AlarmTypes; use AlarmTypes;
------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency.All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd.under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Alarm
--
-- Description:
--    Provides interface to the alarm
--
------------------------------------------------------------------

with AuditLog;

package Alarm
  with SPARK_Mode,
       Abstract_State => (Output with External => Async_Readers),
       Initializes => Output
is

   ---------------------------------------------------------
   -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3           --
   --=====================================================--
   -- A proof function is required to model the proof     --
   -- function Interfac.prf_isAlarming(Interfac.Output)   --
   -- (which is not visible outside the package body).    --
   -- Interfac.Output is a refinement of Output, so       --
   -- need to take Output as a parameter of the           --
   -- function.To do this, need to define an abstract     --
   -- type for Output.                                    --
   -- The Interfac.prf_isAlarming proof function is       --
   -- effectively a refinement of this proof function.    --
   ---------------------------------------------------------
   function IsAlarming return Boolean
     with Global     => null,
          Ghost;

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Updates the physical alarm depending on the state of the
   --    Door alarm and the AuditLog alarm.
   --
   -- Traceunit : C.Alarm.UpdateDevice
   -- Traceto   : FD.Interfac.UpdateAlarm
   ------------------------------------------------------------------
   procedure UpdateDevice
     with Global  => (Input  => (AuditLog.State,
                                 Door.State),
                      Output => Output),
          Depends => (Output => (AuditLog.State,
                                 Door.State)),
          --------------------------------------------------------
          -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
          --====================================================--
          -- After each call to UpdateDevice, the Alarm is      --
          -- alarming if the conditions of the security         --
          -- property hold.Note that from the Door package      --
          -- annotation, Door.TheDoorAlarm = Alarming is        --
          -- equivalent to the security property conditions     --
          --------------------------------------------------------
          Post    => (if Door.TheDoorAlarm = AlarmTypes.Alarming then IsAlarming);

end Alarm;
