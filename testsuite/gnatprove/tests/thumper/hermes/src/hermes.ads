---------------------------------------------------------------------------
-- FILE    : hermes.ads
-- SUBJECT : Top level package of the Hermes ASN.1 library.
-- AUTHOR  : (C) Copyright 2015 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Hermes is
   pragma Pure;

   type Octet is mod 2**8;
   type Octet_Array is array(Natural range <>) of Octet;

end Hermes;
