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

   type T is private;

   MaxStatsCount : constant := 2**31-1;
   type StatsCount is range 0..MaxStatsCount;


   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes all stats to zero
   --
   -- traceunit : C.Stats.Init
   -- traceto   : FD.TIS.InitIDStation
   ------------------------------------------------------------------

   procedure Init(TheStats :    out T);
   --# derives TheStats from ;


   ------------------------------------------------------------------
   -- AddSuccessfulEntry
   --
   -- Description:
   --    Increments number of successful entries
   --
   -- traceunit : C.Stats.AddSuccessfulEntry
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------

   procedure AddSuccessfulEntry(TheStats : in out T);
   --# derives TheStats from TheStats;


   ------------------------------------------------------------------
   -- AddFailedEntry
   --
   -- Description:
   --    Increments number of failed entries
   --
   -- traceunit : C.Stats.AddFailedEntry
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------

   procedure AddFailedEntry(TheStats : in out T);
   --# derives TheStats from TheStats;


   ------------------------------------------------------------------
   -- AddSuccessfulBio
   --
   -- Description:
   --    Increment number of successful bio verifications
   --
   -- traceunit : C.Stats.AddSuccessfulBio
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------

   procedure AddSuccessfulBio(TheStats : in out T);
   --# derives TheStats from TheStats;


   ------------------------------------------------------------------
   -- AddFailedBio
   --
   -- Description:
   --    Increment number of failed bio verifications
   --
   -- traceunit : C.Stats.AddFailedBio
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------

   procedure AddFailedBio(TheStats : in out T);
   --# derives TheStats from TheStats;


   ------------------------------------------------------------------
   -- DisplayStats
   --
   -- Description:
   --    Returns the component parts of TheStats.
   --
   -- traceunit : C.Stats.DisplayStats
   -- traceto   : FD.TIS.State
   ------------------------------------------------------------------

   procedure DisplayStats(TheStats     : in     T;
                          SuccessEntry :    out StatsCount;
                          FailEntry    :    out StatsCount;
                          SuccessBio   :    out StatsCount;
                          FailBio      :    out StatsCount);
   --# derives SuccessEntry,
   --#         FailEntry,
   --#         SuccessBio,
   --#         FailBio       from TheStats;


private

      type T is
         record
            SuccessEntry : StatsCount;
            FailEntry    : StatsCount;
            SuccessBio   : StatsCount;
            FailBio      : StatsCount;
         end record;

end Stats;
