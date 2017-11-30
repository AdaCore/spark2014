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
with CommonTypes,
     IandATypes;

private package Bio.Interfac
  with Abstract_State => (Input with External => Async_Writers,
                                     Part_Of  => Bio.Input)
is

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
   function IsSamplePresent return CommonTypes.PresenceT
     with Volatile_Function,
          Global => Input;

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
                     BioReturn      :    out CommonTypes.Unsigned32T)
     with Global  => Input,
          Depends => ((AchievedFAR,
                       BioReturn)   => (Input,
                                        Template),
                      MatchResult   => (Input,
                                        MaxFAR,
                                        Template));

   ------------------------------------------------------------------
   -- Flush
   --
   -- Description:
   --    Flushes the Bio device of stale data.
   --
   ------------------------------------------------------------------
   procedure Flush
     with Global  => Input,
          Depends => (null => Input);

end Bio.Interfac;
