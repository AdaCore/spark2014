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
-- Alarm.Interfac
--
-- Description:
--    private child of Alarm, providing the interface the physical
--    alarm
--
------------------------------------------------------------------

private package Alarm.Interfac
  with Abstract_State => (Output with External => Async_Readers,
                                      Part_Of  => Alarm.Output)
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   --------------------------------------------------------
   -- PROOF ANNOTATIONS FOR SECURITY PROPERTY 3          --
   --====================================================--
   -- A proof function is required to model the state    --
   -- of the alarm (Interfac.Output, which is not        --
   -- visible outside the alarm package body).           --
   -- The function is true if Alarm.Activate is called.  --
   --------------------------------------------------------
   function IsAlarming return Boolean
     with Global     => null,
          Ghost;

   ------------------------------------------------------------------
   -- Activate
   --
   -- Description:
   --    Sets the alarm to Alarming
   --
   ------------------------------------------------------------------
   procedure Activate
     with Global  => (Output => Output),
          Depends => (Output => null),
          Post    => IsAlarming;

   ------------------------------------------------------------------
   -- Deactivate
   --
   -- Description:
   --    Silences the alarm
   --
   ------------------------------------------------------------------
   procedure Deactivate
     with Global  => (Output => Output),
          Depends => (Output => null),
          Post    => not IsAlarming;

end Alarm.Interfac;
