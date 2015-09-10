---------------------------------------------------------------------------
-- FILE    : network-socket-writer.ads
-- SUBJECT : Boundary variable package representing the output stream.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Messages;
with Network.Addresses;

package Network.Socket.Writer
  with Abstract_State =>
    (Output_Message_Stream with External => (Async_Readers, Effective_Writes))
is
   type Status_Type is (Success, Failure);

   -- This procedure sends a datagram to the given destination address.
   procedure Send
     (Message : in  Messages.Network_Message;
      To      : in  Addresses.UDPv4;
      Status  : out Status_Type)
     with
       Global => (In_Out => Output_Message_Stream),
       Depends =>
         (Output_Message_Stream =>+ (Message, To),
          Status => (Output_Message_Stream, Message));

end Network.Socket.Writer;
