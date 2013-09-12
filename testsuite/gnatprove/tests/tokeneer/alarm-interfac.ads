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
-- Alarm.Interfac
--
-- Description:
--    private child of Alarm, providing the interface the the physical
--    alarm
--
------------------------------------------------------------------

private package Alarm.Interfac
--# own out Output : OutType;
is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   --------------------------------------------------------
   -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --====================================================--
   -- A proof function is required to model the state    --
   -- of the alarm (Interfac.Output, which is not       --
   -- visible outside the alarm package body).           --
   -- The function is true iff Alarm.Activate is called. --
   --------------------------------------------------------
   --# type OutType is Abstract;
   --#
   --# function prf_isAlarming(Output : OutType)
   --#    return Boolean;
   function IsAlarming return Boolean;

   ------------------------------------------------------------------
   -- Activate
   --
   -- Description:
   --    Sets the alarm to Alarming
   --
   ------------------------------------------------------------------

   procedure Activate;
   --# global Output;
   --# derives Output from ;
   --# post prf_isAlarming(Output);
   pragma Postcondition (IsAlarming);



   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Description:
   --    Silences the alarm
   --
   ------------------------------------------------------------------

   procedure Deactivate;
   --# global Output;
   --# derives Output from ;
   --# post not prf_isAlarming(Output);
   pragma Postcondition (not IsAlarming);

end Alarm.Interfac;
