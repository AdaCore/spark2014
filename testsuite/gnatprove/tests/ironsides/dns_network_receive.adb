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

with DNS_Types;
use type DNS_Types.Packet_Length_Range;

package body DNS_Network_Receive is
   ----------------------------
   -- Receive_DNS_Packet_TCP --
   ----------------------------

   procedure Receive_DNS_Packet_TCP
     (Packet       :    out DNS_Types.DNS_Tcp_Packet;
      Number_Bytes :    out DNS_Types.Packet_Length_Range;
      Socket       : in     DNS_Network.DNS_Socket;
      Failure      :    out Boolean)
   is
   begin
      DNS_Network.Receive_DNS_Packet_TCP
        (Packet       => Packet,
         Number_Bytes => Number_Bytes,
         Socket       => Socket,
         Failure      => Failure);
      if not Failure then
         Failure := Number_Bytes < DNS_Types.Packet_Length_Range
                                     (1 + DNS_Types.Header_Bits/8) or
                    Number_Bytes > DNS_Network.MAX_QUERY_SIZE;
      end if;
   end Receive_DNS_Packet_TCP;

   ------------------------
   -- Receive_DNS_Packet --
   ------------------------

   procedure Receive_DNS_Packet
     (Packet        : out DNS_Types.DNS_Packet;
      Number_Bytes  : out DNS_Types.Packet_Length_Range;
      Reply_Address : out DNS_Network.Network_Address_and_Port;
      Failure       : out Boolean)
   is
   begin
      DNS_Network.Receive_DNS_Packet
        (Packet        => Packet,
         Number_Bytes  => Number_Bytes,
         Reply_Address => Reply_Address,
         Failure       => Failure);
      if not Failure then
         Failure := Number_Bytes < DNS_Types.Packet_Length_Range
                                     (1 + DNS_Types.Header_Bits/8) or
                    Number_Bytes > DNS_Network.Max_Query_Size;
      end if;
   end Receive_DNS_Packet;

end Dns_Network_Receive;
