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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with BioApi,
     CommonTypes;

package body Bio.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- IsSamplePresent
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsSamplePresent return CommonTypes.PresenceT is
     (if BioApi.SamplePresent then CommonTypes.Present
      else CommonTypes.Absent);

   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    Convert to and from BioAPI types.
   --
   ------------------------------------------------------------------
   procedure Verify (Template       : in     IandATypes.TemplateT;
                     MaxFAR         : in     IandATypes.FarT;
                     MatchResult    :    out IandATypes.MatchResultT;
                     AchievedFAR    :    out IandATypes.FarT;
                     BioReturn      :    out CommonTypes.Unsigned32T)
   is
      Matched          : Boolean;
      LocalFARAchieved : BioApi.RateT;
      LocalReturn      : CommonTypes.Unsigned32T;
   begin
      BioApi.Verify(Template       => BioApi.TemplateT'(
                                         TemplateLength =>
                                            CommonTypes.Unsigned32T(
                                               Template.Length),
                                         RequiredMaxFAR =>
                                            BioApi.RateT(
                                               Template.RequiredMaxFAR),
                                         ID  => Template.ID,
                                         Pad => BioApi.NullTemplatePad),
                    MaxFAR         => BioApi.RateT(MaxFAR),
                    Matched        => Matched,
                    FARAchieved    => LocalFARAchieved,
                    BioReturn      => LocalReturn);
      if Matched then
         MatchResult := IandATypes.Match;
      else
         MatchResult := IandATypes.NoMatch;
      end if;

      AchievedFAR := IandATypes.FarT(LocalFARAchieved);
      BioReturn   := CommonTypes.Unsigned32T(LocalReturn);

   end Verify;

   ------------------------------------------------------------------
   -- Flush
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Flush
   is
   begin
      BioAPI.Reset;
   end Flush;

end Bio.Interfac;
