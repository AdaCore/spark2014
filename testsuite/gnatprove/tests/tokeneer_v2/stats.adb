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

package body Stats is

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure Init (TheStats :    out T)
   is
   begin
      TheStats := T'(SuccessEntry => StatsCount'First,
                     FailEntry    => StatsCount'First,
                     SuccessBio   => StatsCount'First,
                     FailBio      => StatsCount'First);
   end Init;

   ------------------------------------------------------------------
   -- AddSuccessfulEntry
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure AddSuccessfulEntry (TheStats : in out T)
   is
   begin
      if TheStats.SuccessEntry /= StatsCount'Last then
         TheStats.SuccessEntry := TheStats.SuccessEntry + 1;
      end if;
   end AddSuccessfulEntry;

   ------------------------------------------------------------------
   -- AddFailedEntry
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure AddFailedEntry (TheStats : in out T)
   is
   begin
      if TheStats.FailEntry /= StatsCount'Last then
         TheStats.FailEntry := TheStats.FailEntry + 1;
      end if;
   end AddFailedEntry;

   ------------------------------------------------------------------
   -- AddSuccessfulBio
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure AddSuccessfulBio (TheStats : in out T)
   is
   begin
      if TheStats.SuccessBio /= StatsCount'Last then
         TheStats.SuccessBio := TheStats.SuccessBio + 1;
      end if;
   end AddSuccessfulBio;

   ------------------------------------------------------------------
   -- AddFailedBio
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure AddFailedBio (TheStats : in out T)
   is
   begin
      if TheStats.FailBio /= StatsCount'Last then
         TheStats.FailBio := TheStats.FailBio + 1;
      end if;
   end AddFailedBio;

   ------------------------------------------------------------------
   -- DisplayStats
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure DisplayStats (TheStats     : in     T;
                           SuccessEntry :    out StatsCount;
                           FailEntry    :    out StatsCount;
                           SuccessBio   :    out StatsCount;
                           FailBio      :    out StatsCount)
   is
   begin
      SuccessEntry := TheStats.SuccessEntry;
      FailEntry    := TheStats.FailEntry;
      SuccessBio   := TheStats.SuccessBio;
      FailBio      := TheStats.FailBio;
   end DisplayStats;
end Stats;
