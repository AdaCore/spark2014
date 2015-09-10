---------------------------------------------------------------------------
-- FILE    : check_addresses.adb
-- SUBJECT : Package containing tests of network address handling.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit.Assertions; use AUnit.Assertions;
with Network.Addresses;
with Network.Addresses.Test;

package body Check_Addresses is
   use Network.Addresses;
   use Network.Addresses.Test;

   procedure Test_To_IPv4_Address(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      Address : IPv4;
      Status  : Status_Type;

      -- TODO: Create a table of test cases!
   begin
      -- Good addresses should be accepted.
      To_IPv4_Address("155.42.234.60", Address, Status);
      Assert(Status  = Success, "Failed to convert 155.42.234.60 to an address");
      Assert(Address = (155, 42, 234, 60), "Incorrectly converted 155.42.234.60 to an address");

      To_IPv4_Address("0.0.0.0", Address, Status);
      Assert(Status  = Success, "Failed to convert 0.0.0.0 to an address");
      Assert(Address = (0, 0, 0, 0), "Incorrectly converted 0.0.0.0 to an address");

      To_IPv4_Address("255.255.255.255", Address, Status);
      Assert(Status  = Success, "Failed to convert 255.255.255.255 to an address");
      Assert(Address = (255, 255, 255, 255), "Incorrectly converted 255.255.255.255 to an address");

      -- Bad addresses should be rejected.
      To_IPv4_Address("", Address, Status);
      Assert(Status = Invalid_Address, "Converted the empty string");
      To_IPv4_Address("256.0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 256.0.0.0");
      To_IPv4_Address("1234.0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 1234.0.0.0");
      To_IPv4_Address("0.0.0.256", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.256");
      To_IPv4_Address("0.0.0.1234", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.1234");
      To_IPv4_Address("0.0..0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0..0");
      To_IPv4_Address("0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0");
      To_IPv4_Address(".0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted .0.0.0");
      To_IPv4_Address("0.0.0.", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.");
      To_IPv4_Address("0.0.0.0.", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.0.");
      To_IPv4_Address("0.0.0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.0.0");
      To_IPv4_Address(" 0.0.0.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.0 with leading space");
      To_IPv4_Address("0.0.0.0 ", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0.0 with trailing space");
      To_IPv4_Address("0.0.0x.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.0x.0");
      To_IPv4_Address("0.0.x.0", Address, Status);
      Assert(Status = Invalid_Address, "Converted 0.0.x.0");
   end Test_To_IPv4_Address;


   procedure Test_To_IPv4_String(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      Address    : IPv4;
      Status     : Status_Type;
      Text       : Address_String_Type;
      Count      : Natural;

      -- TODO: Create a table of test cases!
      -- TODO: Can these tests be combined with the "To Address" tests above in a useful way?
   begin
      -- Do round trip processing on a few good addresses.
      To_IPv4_Address("155.42.234.60", Address, Status);
      Assert(Status = Success, "Failed to convert 155.42.234.60 to an address");
      To_IPv4_String(Address, Text, Count);
      Assert(Count  = 13, "Incorrect count returned during conversion of [155.42.234.60] to a String");
      Assert(Text(1 .. Count) = "155.42.234.60", "Incorrect conversion of [155.42.234.60] to a String");

      To_IPv4_Address("0.0.0.0", Address, Status);
      Assert(Status = Success, "Failed to convert 0.0.0.0 to an address");
      To_IPv4_String(Address, Text, Count);
      Assert(Count  = 7, "Incorrect count returned during conversion of [0.0.0.0] to a String");
      Assert(Text(1 .. Count) = "0.0.0.0", "Incorrect conversion of [0.0.0.0] to a String");

      To_IPv4_Address("255.255.255.255", Address, Status);
      Assert(Status = Success, "Failed to convert 255.255.255.255 to an address");
      To_IPv4_String(Address, Text, Count);
      Assert(Count  = 15, "Incorrect count returned during conversion of [255.255.255.255] to a String");
      Assert(Text(1 .. Count) = "255.255.255.255", "Incorrect conversion of [255.255.255.255] to a String");
   end Test_To_IPv4_String;


   procedure Register_Tests(T : in out Address_Test) is
   begin
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_To_IPv4_Address'Access, "To IPv4 Address");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_To_IPv4_String'Access, "To IPv4 String");
   end Register_Tests;


   function Name(T : Address_Test) return AUnit.Message_String is
      pragma Unreferenced(T);
   begin
      return AUnit.Format("Address");
   end Name;

end Check_Addresses;
