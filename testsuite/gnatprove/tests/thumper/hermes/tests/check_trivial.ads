---------------------------------------------------------------------------
-- FILE    : check_trivial.ads
-- SUBJECT : Package containing tests of nothing in particular.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- The "trivial" test is just a place holder. It can be used as a template for other tests.
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit;
with AUnit.Test_Cases;

package Check_Trivial is

   type Trivial_Test is new AUnit.Test_Cases.Test_Case with null record;

   procedure Register_Tests(T : in out Trivial_Test);
   function Name(T : Trivial_Test) return AUnit.Message_String;

end Check_Trivial;
