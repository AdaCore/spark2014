---------------------------------------------------------------------------
-- FILE    : network-addresses-test.ads
-- SUBJECT : Specification of a package that supports testing network addresses.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

package Network.Addresses.Test is

  function "="(Address : IPv4; Raw : Network.Octet_Array) return Boolean;

end Network.Addresses.Test;
