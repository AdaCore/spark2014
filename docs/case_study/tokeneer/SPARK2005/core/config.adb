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
-- Auto-generated SPARK target configuration file
--
-- This is suitable for GNAT Pro, GPL and GAP editions
-- runnning on 32-bit Windows.
------------------------------------------------------------------

package Standard is
   type Integer is range -2147483648 ..  2147483647;
   type Float is digits  6 range -3.40282E+38 ..  3.40282E+38;
end Standard;

package System is
   type Address is private;
   Min_Int : constant := -9223372036854775808;
   Max_Int : constant :=  9223372036854775807;
   Max_Binary_Modulus : constant :=  18446744073709551615 + 1;
   Max_Digits : constant :=  18;
   Max_Base_Digits : constant :=  18;
   Max_Mantissa : constant :=  63;
   Storage_Unit : constant :=  8;
   Word_Size : constant :=  32;
   Fine_Delta : constant :=  1.08420217248550443E-19;
   subtype Any_Priority is Integer range  0 ..  31;
   subtype Priority is Any_Priority range  0 ..  30;
   subtype Interrupt_Priority is Any_Priority range  31 ..  31;
end System;
