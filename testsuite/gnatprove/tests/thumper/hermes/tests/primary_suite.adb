---------------------------------------------------------------------------
-- FILE    : primary_suite.adb
-- SUBJECT : The main test suite of the ASN.1 unit test program.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Check_DER_Decode;
with Check_DER_Encode;
with Check_OID;
with Check_Trivial;

package body Primary_Suite is
   use AUnit.Test_Suites;

   -- The suite itself.
   Suite_Object : aliased Test_Suite;

   -- The various tests in this suite. Low level tests should be done first.
   Test_0 : aliased Check_Trivial.Trivial_Test;
   Test_1 : aliased Check_DER_Decode.DER_Decode_Test;
   Test_2 : aliased Check_DER_Encode.DER_Encode_Test;
   Test_3 : aliased Check_OID.OID_Test;

   -- Function to return an access to the configured suite
   function Suite return Access_Test_Suite is
   begin
      Add_Test(Suite_Object'Access, Test_0'Access);
      Add_Test(Suite_Object'Access, Test_1'Access);
      Add_Test(Suite_Object'Access, Test_2'Access);
      Add_Test(Suite_Object'Access, Test_3'Access);
      return Suite_Object'Access;
   end Suite;

end Primary_Suite;
