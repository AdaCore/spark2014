---------------------------------------------------------------------------
-- FILE    : check_crypto.ads
-- SUBJECT : Package containing tests of the cryptographic services.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit;
with AUnit.Test_Cases;

package Check_Crypto is

   type Crypto_Test is new AUnit.Test_Cases.Test_Case with null record;

   procedure Register_Tests(T : in out Crypto_Test);
   function Name(T : Crypto_Test) return AUnit.Message_String;

end Check_Crypto;
