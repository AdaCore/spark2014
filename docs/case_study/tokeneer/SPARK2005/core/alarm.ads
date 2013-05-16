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
-- Alarm
--
-- Description:
--    Provides interface to the alarm
--
------------------------------------------------------------------

--# inherit AlarmTypes,
--#         AuditLog,
--#         AuditTypes,
--#         Clock,
--#         ConfigData,
--#         Door;


package Alarm
--# own out Output : OutType;
is

   ---------------------------------------------------------
   -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3           --
   --=====================================================--
   -- A proof function is required to model the proof     --
   -- function Interface.prf_isAlarming(Interface.Output) --
   -- (which is not visible outside the package body).    --
   -- Interface.Output is a refinement of Output, so      --
   -- need to take Output as a parameter of the           --
   -- function. To do this, need to define an abstract    --
   -- type for Output.                                    --
   -- The Interface.prf_isAlarming proof function is      --
   -- effectively a refinement of this proof function.    --
   ---------------------------------------------------------
   --# type OutType is Abstract;
   --#
   --# function prf_isAlarming(Output : OutType)
   --#    return Boolean;

   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Description:
   --    Updates the physical alarm depending on the state of the
   --    Door alarm and the AuditLog alarm.
   --
   -- Traceunit : C.Alarm.UpdateDevice
   -- Traceto   : FD.Interface.UpdateAlarm
   ------------------------------------------------------------------

   procedure UpdateDevice;
   --# global    out Output;
   --#        in     Door.State;
   --#        in     AuditLog.State;
   --# derives Output from Door.State,
   --#                     AuditLog.State;
   --# post
   --#      --------------------------------------------------------
   --#      -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --#      --====================================================--
   --#      -- After each call to UpdateDevice, the Alarm is      --
   --#      -- alarming if the conditions of the security         --
   --#      -- property hold. Note that from the Door package     --
   --#      -- annotation, Door.TheDoorAlarm = Alarming is        --
   --#      -- equivalent to the security property conditions     --
   --#      --------------------------------------------------------
   --#      Door.TheDoorAlarm(Door.State) = AlarmTypes.Alarming ->
   --#      prf_isAlarming(Output);

end Alarm;
