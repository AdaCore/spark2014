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

   type Unsigned32T is range 0..2**32 - 1;
   for Unsigned32T'Size use 32;

   type Signed32T is range - (2**31)..2**31 - 1;
   for Signed32T'Size use 32;

   type Unsigned8T is range 0 .. 2**8 - 1;

   type ByteT is range 0..255;
   for ByteT'Size use 8;

   type PresenceT is (Present, Absent);

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

   subtype StringF1 is String with
     Predicate => StringF1'First = 1 and StringF1'Last >= 0;
   subtype StringF1L20 is StringF1 with
     Predicate => StringF1L20'Last <= 20;
   subtype StringF1L12 is StringF1 with
     Predicate => StringF1L12'Last <= 12;
   subtype StringF1L1000 is StringF1 with
     Predicate => StringF1L1000'Last <= 1000;
   subtype StringF1L2to1000 is StringF1L1000 with
     Predicate => StringF1L2to1000'Length >= 2;
   subtype StringF1L3to1000 is StringF1L1000 with
     Predicate => StringF1L3to1000'Length >= 3;
   subtype StringF1L1000NE is StringF1L1000 with
     Predicate => StringF1L1000NE'Length >= 1;

   function Unsigned32T_Image (X : Unsigned32T) return StringF1L1000 is
      (Unsigned32T'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of integers of type Unsigned32T are short strings starting at index 1");

   function Integer_Image (X : Integer) return StringF1L1000 is
      (Integer'Image (X));
   pragma Annotate (GNATprove, False_Positive,
                    "predicate check might fail",
                    "Image of integers of type Integer are short strings starting at index 1");

end CommonTypes;
