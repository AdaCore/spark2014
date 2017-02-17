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
-- Description:
--    Provides abstract type and operations for storing and
--    retrieving TIS statistics.
--
------------------------------------------------------------------

package Stats
is

   MaxStatsCount : constant := 2**31-1;
   type StatsCount is range 0..MaxStatsCount;

      type T is
         record
            SuccessEntry : StatsCount;
            FailEntry    : StatsCount;
            SuccessBio   : StatsCount;
            FailBio      : StatsCount;
         end record;

      procedure Init(TheStats :    out T);

end Stats;
