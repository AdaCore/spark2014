---------------------------------------------------------------------------
-- FILE    : messages.ads
-- SUBJECT : Specification of a package that defines the basic message type exchanged.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;
with Network;

package Messages is
   use type Hermes.Octet;
   use type Network.Octet;

   subtype Index_Type is Positive range 1 .. 512;
   subtype Count_Type is Natural  range 0 .. Index_Type'Last;

   -- Type Network_Message represents the raw data sent/received on the network.
   type Network_Message is
      record
         Data : Network.Octet_Array(Index_Type); -- The data.
         Size : Count_Type;                      -- Number of data elements actually used.
      end record;

   -- Type Message represents the ASN.1 data.
   type Message is
      record
         Data : Hermes.Octet_Array(Index_Type); -- The data.
         Size : Count_Type;                     -- Number of data elements actually used.
      end record;

   -- The functions below guarantee that unused octets in the result message are zeroed. I'm not
   -- sure how important that behavior really is, but it might be useful at some point. Maybe?

   function From_Network(Low_Level : Network_Message) return Message
     with Post => From_Network'Result.Size = Low_Level.Size and
                  (for all I in Index_Type =>
                     (if I in Index_Type'First .. Low_Level.Size
                          then From_Network'Result.Data(I) = Hermes.Octet(Low_Level.Data(I))
                          else From_Network'Result.Data(I) = 0));

   function To_Network(High_Level : Message) return Network_Message
     with Post => To_Network'Result.Size = High_Level.Size and
                  (for all I in Index_Type =>
                     (if I in Index_Type'First .. High_Level.Size
                          then To_Network'Result.Data(I) = Network.Octet(High_Level.Data(I))
                          else To_Network'Result.Data(I) = 0));

end Messages;
