------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- BioAPI
--
-- Description:
--    This API has been modeled on the BioAPI specification.
--
------------------------------------------------------------------

with CommonTypes;

package BioAPI is

   ------------------------------------------------------------------
   --
   -- Types
   --
   ------------------------------------------------------------------
   -- FAR (False Accept Rate) is used to determine how similar a fingerprint
   -- needs to be to 'match' a template. The higher the value, the larger the
   -- allowed deviation from the template.
   type RateT is range - (2**31) .. 2**31 - 1;
   for RateT'Size use 32;

   -- The biometric template contains fictional fields to simplify the
   -- Test Driver API. Includes a TemplateLength field, a RequiredMaxFAR
   -- field and padding to bring up to the maximum size currently allowed by
   -- the Identicator format (500 bytes).
   type TemplatePadI is range 1..123;
   type TemplatePadT is array(TemplatePadI) of CommonTypes.Unsigned32T;

   NullTemplatePad : constant TemplatePadT :=
     TemplatePadT'(others => CommonTypes.Unsigned32T'First);

   subtype TemplateLengthT is CommonTypes.Unsigned32T;

   subtype IDT is String(1..40);

   type TemplateT is record
      TemplateLength : TemplateLengthT;
      RequiredMaxFAR : RateT;
      ID             : IDT;
      Pad            : TemplatePadT;
   end record;

   NullTemplate : constant TemplateT := TemplateT'
     (TemplateLength => TemplateLengthT'First,
      RequiredMaxFAR => RateT'First,
      ID             => (others => ' '),
      Pad            => NullTemplatePad);

   ------------------------------------------------------------------
   -- SamplePresent
   --
   -- Description:
   --    A means of 'polling' the reader, to determine whether there is a
   --    finger present to sample, and is called prior to attempting a Verify.
   --
   ------------------------------------------------------------------
   function SamplePresent return Boolean
     with Global => null;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Description:
   --    Called by TIS when it is ready to check the user's fingerprint against
   --    the template held on the user's card. Performs a comparison of the
   --    latest livescan data against the Template. Indicates the closeness of
   --    the match in FARAchieved.
   --
   ------------------------------------------------------------------
   procedure Verify (Template       : in     TemplateT;
                     MaxFAR         : in     RateT;
                     Matched        :    out Boolean;
                     FARAchieved    :    out RateT;
                     BioReturn      :    out CommonTypes.Unsigned32T)
     with Global => null;

   ------------------------------------------------------------------
   -- Reset
   --
   -- Description:
   --    Flushes the Bio device of stale data.
   --
   ------------------------------------------------------------------
   procedure Reset
     with Global => null;

end BioAPI;
