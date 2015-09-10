---------------------------------------------------------------------------
-- FILE    : timestamp_messages-client.ads
-- SUBJECT : Specification of a package for encoding/decoding timestamps on the client side.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;
with Hermes.DER;

package Timestamp_Messages.Client is

   -- Decodes a Timestamp from a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER decoding procedures.
   procedure Get_Timestamp_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Stamp   : out Timestamp;
      Status  : out Hermes.DER.Status_Type)
     with
       Global => null,
       Depends => ( (Stop, Stamp, Status) => (Message, Start) ),
       Pre => Start in Message'Range;


   -- Encodes a Request to a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER encoding procedures.
   function Put_Request_Value(Req : Request) return Hermes.Octet_Array;


   -- Decodes a Response from a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER decoding procedures.
   procedure Get_Response_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Resp    : out Response;
      Status  : out Hermes.DER.Status_Type)
     with
       Global => null,
       Depends => ( (Stop, Resp, Status) => (Message, Start) ),
       Pre => Start in Message'Range;

end Timestamp_Messages.Client;
