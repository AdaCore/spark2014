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
-- Stats
--
-- Implementation Notes:
--    INFORMED Design states that the TIS will stop incrementing
--    the stats once their respective maximum value has been reached.
--
------------------------------------------------------------------

package body Stats
is

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure Init(TheStats :    out T)
   is
   begin
      TheStats.FailEntry := StatsCount'Last;
      TheStats := T'(SuccessEntry => StatsCount'First,
                     FailEntry    => StatsCount'First,
                     SuccessBio   => StatsCount'First,
                     FailBio      => StatsCount'First);
   end Init;


end Stats;
