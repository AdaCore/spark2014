---------------------------------------------------------------------------
-- FILE    : check_oid.ads
-- SUBJECT : Package containing object identifier tests.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit;
with AUnit.Test_Cases;

package Check_OID is

   type OID_Test is new AUnit.Test_Cases.Test_Case with null record;

   procedure Register_Tests(T : in out OID_Test);
   function Name(T : OID_Test) return AUnit.Message_String;

end Check_OID;
