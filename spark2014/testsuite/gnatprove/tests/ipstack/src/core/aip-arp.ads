------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  RFC826 - Address Resolution Protocol

with AIP.Buffers;
with AIP.IPaddrs;
with AIP.NIF;

package AIP.ARP is

private

   procedure ARP_Input
     (Nid           : NIF.Netif_Id;
      Netif_Address : IPTR_T;
      Buf           : Buffers.Buffer_Id);
   pragma Export (C, ARP_Input, "AIP_arp_input");
   --  Process ARP packet in Buf received on interface Nid. Netif_Address is
   --  Nid's hardware address.

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id);
   pragma Export (C, IP_Input, "AIP_arpip_input");
   --  Process IP packet in Buf received on Nid

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr);
   pragma Export (C, ARP_Output, "AIP_arp_output");
   --  Send packet in Buf to Dst_Address through Nid

end AIP.ARP;
