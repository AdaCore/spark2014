---------------------------------------------------------------------------
-- FILE    : aco-bit_operations.ads
-- SUBJECT : Bit manipulation operations that currently can't be proven by SPARK.
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin
--
-- This package is necessary because currently (June 2014) SPARK doesn't have much knowledge of Ada's bit manipulation
-- operators. Thus it has trouble proving freedom from runtime errors in expressions involving shifts, rotates, masking, etc.
-- This package pushes those operations into a non-SPARK body where they won't interfer with the proofs of code that uses them.
--
-- Eventually SPARK may be upgraded to allow direct proof of more bit manipulations. When that occurs the subprograms defined
-- here could be inline expanded into the code that uses them. To check if SPARK is ready, try setting the SPARK_Mode of this
-- package's body to "On" and seeing if SPARK can prove the bodies of these subprograms.
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package ACO.Bit_Operations is

   -- Breaks out the 8 bit words from a 32 bit value.
   procedure Split32_To_Word8(Value : in ACO.Quadruple_Octet; Most, Middle_High, Middle_Low, Least : out ACO.Octet)
     with
       Inline,
       Global => null,
       Depends => ((Most, Middle_High, Middle_Low, Least) => Value);


   -- Breaks out the 32 bit words from a 64 bit value.
   procedure Split64_To_Word32(Value : in ACO.Octuple_Octet; Most, Least : out ACO.Quadruple_Octet)
     with
       Inline,
       Global  => null,
       Depends => ((Most, Least) => Value);


   -- Returns the least significant byte in a 16 bit value.
   function TakeLSB_From16(Value : in ACO.Double_Octet) return ACO.Octet
     with
       Inline,
       Global => null;

end ACO.Bit_Operations;
