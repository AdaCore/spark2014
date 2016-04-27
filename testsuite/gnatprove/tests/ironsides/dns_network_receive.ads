----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with DNS_Types,
     DNS_Network;

use type DNS_Types.Packet_Length_Range;

package DNS_Network_Receive is

   procedure Receive_DNS_Packet_TCP
     (Packet        :   out DNS_Types.DNS_TCP_Packet;
      Number_Bytes :    out DNS_Types.Packet_Length_Range;
      Socket       : in     DNS_Network.DNS_Socket;
      Failure      :    out Boolean)
   with Global  => (In_Out => DNS_Network.Network),
        Depends => ((DNS_Network.Network,
                     Failure,
                     Number_Bytes,
                     Packet) => (DNS_Network.Network,
                                 Socket)),
        Post    =>
          (if not Failure then
             Number_Bytes >= DNS_Types.Packet_Length_Range
                               (1 + DNS_Types.Header_Bits / 8) and
             Number_Bytes <= DNS_Network.Max_Query_Size);

   -- Reads a single UDP packet from network on port 53
   -- Last is the number of bytes read (assuming no failure)
   procedure Receive_DNS_Packet
     (Packet        : out DNS_Types.DNS_Packet;
      Number_Bytes  : out DNS_Types.Packet_Length_Range;
      Reply_Address : out DNS_Network.Network_Address_and_Port;
      Failure       : out Boolean)
   with Global  => (In_Out => DNS_Network.Network),
        Depends => ((DNS_Network.Network,
                     Failure,
                     Number_Bytes,
                     Packet,
                     Reply_Address) => DNS_Network.Network),
        Post    =>
          (if not Failure then
             Number_Bytes >= DNS_Types.Packet_Length_Range
                               (1 + DNS_Types.Header_Bits / 8) and
             Number_Bytes <= DNS_Network.MAX_QUERY_SIZE);
end DNS_Network_Receive;
