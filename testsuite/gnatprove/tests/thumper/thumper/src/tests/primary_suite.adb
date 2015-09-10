---------------------------------------------------------------------------
-- FILE    : primary_suite.adb
-- SUBJECT : The main test suite of the Thumper unit test program.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Check_Addresses;
with Check_Crypto;
with Check_Trivial;

package body Primary_Suite is
   use AUnit.Test_Suites;

   -- The suite itself.
   Suite_Object : aliased Test_Suite;

   -- The various tests in this suite. Low level tests should be done first.
   Test_0 : aliased Check_Trivial.Trivial_Test;
   Test_1 : aliased Check_Addresses.Address_Test;
   Test_2 : aliased Check_Crypto.Crypto_Test;

   -- Function to return an access to the configured suite
   function Suite return Access_Test_Suite is
   begin
      Add_Test(Suite_Object'Access, Test_0'Access);
      Add_Test(Suite_Object'Access, Test_1'Access);
      Add_Test(Suite_Object'Access, Test_2'Access);
      return Suite_Object'Access;
   end Suite;

end Primary_Suite;
