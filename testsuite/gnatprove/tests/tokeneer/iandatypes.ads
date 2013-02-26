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
-- IandATypes
--
-- Description:
--    Types that appear within the context of an I&A certificate
--
------------------------------------------------------------------
with BasicTypes,
     CryptoTypes;

--# inherit BasicTypes,
--#         CryptoTypes;

package IandATypes
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------


   -- FAR (False Accept Rate) is used to determine how similar a fingerprint
   -- needs to be to 'match' a template. The higher the value, the larger the
   -- allowed deviation from the template.
   type FarT is range 0 .. 2**31 - 1;
   for FarT'Size use 32;

   type MatchResultT is (Match, NoMatch);

   -- The biometric template contains fictional fields to simplify the
   -- Test Driver API. Includes a TemplateLength field, a RequiredMaxFAR
   -- field, an ID field and padding to bring up to the maximum size currently
   -- allowed by the Identicator format (500 bytes).
   type TemplatePadI is range 1..452;
   type TemplatePadT is array(TemplatePadI) of BasicTypes.ByteT;

   NullTemplatePad : constant TemplatePadT
     := TemplatePadT'(others => BasicTypes.ByteT'First);

   subtype TemplateLengthT is BasicTypes.Unsigned32T;

   subtype TemplateIDI is Positive range 1..40;
   subtype TemplateIDT is String(TemplateIDI);

   type TemplateT is
      record
         Length         : TemplateLengthT;
         RequiredMaxFAR : FarT;
         ID             : TemplateIDT;
         Pad            : TemplatePadT;
      end record;

   NullTemplate : constant TemplateT := TemplateT'
     ( Length         => TemplateLengthT'First,
       RequiredMaxFAR => FarT'First,
       ID             => TemplateIDT'(others => ' '),
       Pad            => NullTemplatePad);


end IandATypes;
