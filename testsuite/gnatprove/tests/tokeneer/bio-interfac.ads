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
-- Bio.Interfac
--
-- Description:
--    Makes the calls to the BioAPI.
--
------------------------------------------------------------------
--# inherit BasicTypes,
--#         IandATypes;

private package Bio.Interfac
--# own in Input;
is pragma SPARK_Mode (On);

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- SamplePresent
   --
   -- Description:
   --    Used in Bio.Poll
   --
   ------------------------------------------------------------------
   function IsSamplePresent return BasicTypes.PresenceT with Global => null;
   --# global in     Input;


   ------------------------------------------------------------------
   -- Verify
   --
   -- Description:
   --    Used in Bio.Verify. Returns the match result, the achieved
   --    FAR and a return value stating any error occurrence.
   --
   ------------------------------------------------------------------
   procedure Verify (Template       : in     IandATypes.TemplateT;
                     MaxFAR         : in     IandATypes.FarT;
                     MatchResult    :    out IandATypes.MatchResultT;
                     AchievedFAR    :    out IandATypes.FarT;
                     BioReturn      :    out BasicTypes.Unsigned32T);
   --# global in     Input;
   --# derives MatchResult from Input,
   --#                          Template,
   --#                          MaxFAR &
   --#         AchievedFAR,
   --#         BioReturn   from Input,
   --#                          Template;


   ------------------------------------------------------------------
   -- Flush
   --
   -- Description:
   --    Flushes the Bio device of stale data.
   --
   ------------------------------------------------------------------
   procedure Flush;
   --# global in     Input;
   --# derives null from Input;

end Bio.Interfac;
