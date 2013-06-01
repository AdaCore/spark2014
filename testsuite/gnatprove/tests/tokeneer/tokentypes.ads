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
-- TokenTypes
--
-- Description:
--    Types that appear within the context of tokens
--
------------------------------------------------------------------
with BasicTypes,
     CryptoTypes;

--# inherit BasicTypes,
--#         CryptoTypes;

package TokenTypes
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   subtype TokenIDT is BasicTypes.Unsigned32T;

   type TryT is (NoToken, BadToken, GoodToken);

end TokenTypes;
