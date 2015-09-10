---------------------------------------------------------------------------
-- FILE    : network.ads
-- SUBJECT : Specification of a network handling package.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
package Network is
   pragma Pure;

   -- Type for handling raw data on the network.
   type Octet is mod 2**8;
   type Octet_Array is array(Natural range <>) of Octet;

end Network;
