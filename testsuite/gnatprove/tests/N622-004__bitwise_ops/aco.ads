---------------------------------------------------------------------------
-- FILE    : aco.ads
-- SUBJECT : Parent package for the Ada Cryptograhic Objects library.
-- AUTHOR  : (C) Copyright 2008 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package ACO is

   -- Raw data types types.
   type Octet           is mod 2**8;
   type Double_Octet    is mod 2**16;
   type Quadruple_Octet is mod 2**32;
   type Octuple_Octet   is mod 2**64;

   -- Unconstrained arrays of raw data.
   type Octet_Array is array(Natural range <>) of Octet
     with
       Pack,
       Component_Size => 8;

   type Double_Octet_Array is array(Natural range <>) of Double_Octet
     with
       Pack,
       Component_Size => 16;

   type Quadruple_Octet_Array is array(Natural range <>) of Quadruple_Octet
     with
       Pack,
       Component_Size => 32;

   type Octuple_Octet_Array is array(Natural range <>) of Octuple_Octet
     with
       Pack,
       Component_Size => 64;

end ACO;
