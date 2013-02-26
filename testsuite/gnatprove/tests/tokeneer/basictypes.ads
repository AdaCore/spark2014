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
-- BasicTypes
--
-- Description:
--    A library of commonly used types.
--
------------------------------------------------------------------

package BasicTypes is

   type Unsigned32T is range 0 .. 2**32 - 1;
   for Unsigned32T'Size use 32;

   type Signed32T is range - (2**31) .. 2**31 - 1;
   for Signed32T'Size use 32;

   type ByteT is range 0..255;
   for ByteT'Size use 8;

   type PresenceT is (Present, Absent);

end BasicTypes;
