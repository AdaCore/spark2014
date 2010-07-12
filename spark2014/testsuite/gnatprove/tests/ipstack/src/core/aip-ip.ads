------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP layer

with AIP.IPaddrs, AIP.NIF, AIP.Buffers;

package AIP.IP is

   --  IP_PCB is the common part of the PCB for all IP-based protocols

   type IP_PCB is record
      Local_IP  : IPaddrs.IPaddr;
      Remote_IP : IPaddrs.IPaddr;

      SOO : AIP.U16_T;  -- Socket Options
      TOS : AIP.U8_T;   -- Type Of Service
      TTL : AIP.U8_T;   -- Time To Live
   end record;

   procedure IP_Route
     (Dst_IP : IPaddrs.IPaddr; Netif : out NIF.Netif_Id);

   procedure IP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);

   procedure IP_Output_If
     (Buf    : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      TTL    : AIP.U8_T;
      TOS    : AIP.U8_T;
      Proto  : AIP.U8_T;
      Netif  : NIF.Netif_Id;
      Err    : out AIP.Err_T);

   IP_HLEN : constant := 20;
   --  What if there are options???

private

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);
   --  Decrement TTL and forward packet to next hop

end AIP.IP;
