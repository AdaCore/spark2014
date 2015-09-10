---------------------------------------------------------------------------
-- FILE    : check_oid.adb
-- SUBJECT : Package containing object identifier tests.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
-- with AUnit.Assertions; use AUnit.Assertions;

package body Check_OID is

   -- This test should create several object identifiers using To_Object_Identifier and then
   -- split them back up into components using To_Separates and verify that the resulting
   -- components are the same as originally. The function Component_Count could be checked here
   -- as well.
   --
   procedure Test_Round_Trip(T : in out AUnit.Test_Cases.Test_Case'Class) is
   begin
      -- This is arbitrary code. Use Assert to verify that an expected condition is actually
      -- true. The message is displayed if the test fails.
      -- Assert(0 = 0, "Zero is not zero!");
      -- Assert(true = true, "True is the same as false!");
      raise Program_Error;
   end Test_Round_Trip;


   -- This test should convert several object identifiers to octet arrays and verify that the
   -- resulting octet arrays have the right (bit-by-bit) contents.
   --
   procedure Test_Format(T : in out AUnit.Test_Cases.Test_Case'Class) is
   begin
      -- This is arbitrary code. Use Assert to verify that an expected condition is actually
      -- true. The message is displayed if the test fails.
      -- Assert(0 = 0, "Zero is not zero!");
      -- Assert(true = true, "True is the same as false!");
      raise Program_Error;
   end Test_Format;


   procedure Register_Tests(T : in out OID_Test) is
   begin
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Round_Trip'Access, "Round Trip");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Format'Access, "Format");
   end Register_Tests;


   function Name(T : OID_Test) return AUnit.Message_String is
      pragma Unreferenced(T);
   begin
      return AUnit.Format("Object Identifier");
   end Name;

end Check_OID;
