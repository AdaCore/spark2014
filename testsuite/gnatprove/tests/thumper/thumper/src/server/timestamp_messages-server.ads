---------------------------------------------------------------------------
-- FILE    : timestamp_messages-server.ads
-- SUBJECT : Specification of a package for encoding/decoding timestamps on the server side.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Hermes;
with Hermes.DER;

package Timestamp_Messages.Server is

   -- Encodes a Timestamp to a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER encoding procedures.
   function Put_Timestamp_Value(Stamp : Timestamp) return Hermes.Octet_Array;


   -- Decodes a Request from a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER decoding procedures.
   procedure Get_Request_Value
     (Message : in  Hermes.Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Req     : out Request;
      Status  : out Hermes.DER.Status_Type)
     with
       Global => null,
       Depends => ( (Stop, Req, Status) => (Message, Start) ),
       Pre => Start in Message'Range;


   -- Encodes a Response to a DER encoded octet sequence.
   -- The behavior is the same as for the other Hermes.DER encoding procedures.
   function Put_Response_Value(Resp : Response) return Hermes.Octet_Array;

end Timestamp_Messages.Server;
