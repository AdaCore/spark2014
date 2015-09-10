---------------------------------------------------------------------------
-- FILE    : client_timestamp_maker.ads
-- SUBJECT : Specification of a package that encapsulates the work of creating a timestamp.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;

package Client_Timestamp_Maker is

   -- TODO: Add SPARK aspects and return a status indication.
   procedure Create_Timestamp
     (Hash           : in  Hermes.Octet_Array;
      Timestamp      : out Hermes.Octet_Array;
      Timestamp_Size : out Natural);


   function Verify_Timestamp
     (Hash : Hermes.Octet_Array; Timestamp : Hermes.Octet_Array) return Boolean;

end Client_Timestamp_Maker;
