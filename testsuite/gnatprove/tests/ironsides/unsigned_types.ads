----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

package Unsigned_Types IS
   type Unsigned8  is mod 2**8; --SPARK caught missing * here, impressive!
   type Unsigned16 is mod 2**16;
   type Unsigned32 is mod 2**32;

   Max_8Bit_Val  : constant Natural           := 2**8-1;
   Max_16Bit_Val : constant Natural           := 2**16-1;
   Max_32Bit_Val : constant Long_Long_Integer := 2**32-1;
end Unsigned_Types;
