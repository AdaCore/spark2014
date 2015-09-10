---------------------------------------------------------------------------
-- FILE    : network-addresses-test.adb
-- SUBJECT : Body of a package that supports testing network addresses.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

package body Network.Addresses.Test is

   function "="(Address : IPv4; Raw : Network.Octet_Array) return Boolean is
   begin
      return
        Address(1) = Raw(Raw'First + 0) and
        Address(2) = Raw(Raw'First + 1) and
        Address(3) = Raw(Raw'First + 2) and
        Address(4) = Raw(Raw'First + 3);
   end "=";

end Network.Addresses.Test;
