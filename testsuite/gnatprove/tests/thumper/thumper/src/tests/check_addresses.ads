---------------------------------------------------------------------------
-- FILE    : check_addresses.ads
-- SUBJECT : Package containing tests of network address handling.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit;
with AUnit.Test_Cases;

package Check_Addresses is

   type Address_Test is new AUnit.Test_Cases.Test_Case with null record;

   procedure Register_Tests(T : in out Address_Test);
   function Name(T : Address_Test) return AUnit.Message_String;

end Check_Addresses;
