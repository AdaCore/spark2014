---------------------------------------------------------------------------
-- FILE    : network-socket-reader.ads
-- SUBJECT : Boundary variable package representing the input stream.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Messages;
with Network.Addresses;

package Network.Socket.Reader
  with Abstract_State =>
    (Input_Message_Stream with External => (Async_Writers, Effective_Reads => False))
is
   type Status_Type is (Success, Failure);

   -- This procedure receives a datagram. It also returns the source address.
   procedure Receive
     (Message : out Messages.Network_Message;
      From    : out Addresses.UDPv4;
      Status  : out Status_Type)
     with
       Global => (Input => Input_Message_Stream),
       Depends => ((Message, From, Status) => Input_Message_Stream);

end Network.Socket.Reader;
