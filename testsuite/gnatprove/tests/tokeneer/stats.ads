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

with CommonTypes;

package Stats is

   type T is private;

   MaxStatsCount : constant := 2**31-1;
   type StatsCount is range 0..MaxStatsCount;

   function StatsCount_Image (X : StatsCount) return CommonTypes.StringF1L1000 is
      (StatsCount'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of integers of type StatsCount are short strings starting at index 1");

   ------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initializes all stats to zero
   --
   -- traceunit : C.Stats.Init
   -- traceto   : FD.TIS.InitIDStation
   ------------------------------------------------------------------
   procedure Init (TheStats :    out T)
     with Depends => (TheStats => null);

   ------------------------------------------------------------------
   -- AddSuccessfulEntry
   --
   -- Description:
   --    Increments number of successful entries
   --
   -- traceunit : C.Stats.AddSuccessfulEntry
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------
   procedure AddSuccessfulEntry (TheStats : in out T)
     with Depends => (TheStats =>+ null);

   ------------------------------------------------------------------
   -- AddFailedEntry
   --
   -- Description:
   --    Increments number of failed entries
   --
   -- traceunit : C.Stats.AddFailedEntry
   -- traceto   : FD.Stats.Update
   -----------------------------------------------------------------
   procedure AddFailedEntry (TheStats : in out T)
     with Depends => (TheStats =>+ null);

   ------------------------------------------------------------------
   -- AddSuccessfulBio
   --
   -- Description:
   --    Increment number of successful bio verifications
   --
   -- traceunit : C.Stats.AddSuccessfulBio
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------
   procedure AddSuccessfulBio (TheStats : in out T)
     with Depends => (TheStats =>+ null);

   ------------------------------------------------------------------
   -- AddFailedBio
   --
   -- Description:
   --    Increment number of failed bio verifications
   --
   -- traceunit : C.Stats.AddFailedBio
   -- traceto   : FD.Stats.Update
   ------------------------------------------------------------------
   procedure AddFailedBio (TheStats : in out T)
     with Depends => (TheStats =>+ null);

   ------------------------------------------------------------------
   -- DisplayStats
   --
   -- Description:
   --    Returns the component parts of TheStats.
   --
   -- traceunit : C.Stats.DisplayStats
   -- traceto   : FD.TIS.State
   ------------------------------------------------------------------
   procedure DisplayStats (TheStats     : in     T;
                           SuccessEntry :    out StatsCount;
                           FailEntry    :    out StatsCount;
                           SuccessBio   :    out StatsCount;
                           FailBio      :    out StatsCount)
     with Depends => ((FailBio,
                       FailEntry,
                       SuccessBio,
                       SuccessEntry) => TheStats);

private
   type T is record
      SuccessEntry : StatsCount;
      FailEntry    : StatsCount;
      SuccessBio   : StatsCount;
      FailBio      : StatsCount;
   end record;
end Stats;
