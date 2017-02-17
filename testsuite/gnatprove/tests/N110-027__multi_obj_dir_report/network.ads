---------------------------------------------------------------------------
-- FILE    : network.ads
-- SUBJECT : Specification of a network handling package.
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode;

package Network is
   pragma Pure;

   -- Type for handling raw data on the network.
   type Octet is mod 2**8;
   type Octet_Array is array(Natural range <>) of Octet;
   for Octet_Array'Component_Size use 8;
   pragma Pack(Octet_Array);

end Network;
