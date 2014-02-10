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
-- Updates
--
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------

package body Updates is

   ------------------------------------------------------------------
   -- EarlyActivity
   --
   -- Implementation Notes:
   --    Alarm is updated last so as to ensure it is completely up to
   --    date with the audit alarm.
   ------------------------------------------------------------------
   procedure EarlyActivity (SystemFault :    out Boolean)
   is
   begin
      Latch.UpdateDevice(SystemFault => SystemFault);
      Alarm.UpdateDevice;
   end EarlyActivity;

   ------------------------------------------------------------------
   -- Activity
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Activity (TheStats    : in     Stats.T;
                       TheAdmin    : in     Admin.T;
                       SystemFault :    out Boolean)
   is
   begin
      Display.UpdateDevice;
      Screen.UpdateScreen
        (TheStats => TheStats,
         TheAdmin => TheAdmin);
      EarlyActivity( SystemFault => SystemFault);
   end Activity;


end Updates;
