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
-- CommonTypes
--
-- Description:
--    A library of base types, and commonly used types.
--
------------------------------------------------------------------

package CommonTypes is

   type Unsigned32T is range 0 .. 2**32 - 1;
   type Unsigned8T is range 0 .. 2**8 - 1;

   type Signed32T is range - (2**31) .. 2**31 - 1;


   ------------------------------------------------------------------
   --
   -- Strings
   --
   ------------------------------------------------------------------

   -- String50T is used to represent all possible messages on the display

   subtype String50I is Integer range 1..50;
   subtype String50T is String(String50I);

   -- String40T is used to represent textual names of entities within
   -- certificates.

   subtype String40I is Integer range 1..40;
   subtype String40T is String(String40I);

   -- String8T is used to represent all possible card reader names.

   subtype String8I is Integer range 1..8;
   subtype String8T is String(String8I);

   subtype String8ArrayI is Integer range 1..10;
   type String8ArrayT is Array(String8ArrayI) of String8T;


end CommonTypes;
