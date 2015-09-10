---------------------------------------------------------------------------
-- FILE    : check_der_encode.ads
-- SUBJECT : Package containing tests of ASN.1 DER encoding.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit;
with AUnit.Test_Cases;

package Check_DER_Encode is

   type DER_Encode_Test is new AUnit.Test_Cases.Test_Case with null record;

   procedure Register_Tests(T : in out DER_Encode_Test);
   function Name(T : DER_Encode_Test) return AUnit.Message_String;

end Check_DER_Encode;
