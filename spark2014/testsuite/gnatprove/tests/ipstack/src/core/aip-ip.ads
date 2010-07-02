------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP layer

with AIP.IPaddrs, AIP.NIF, AIP.Buffers;

package AIP.IP is

   --  ??? not yet clear if we really need an IP PCB abstraction per se

   type IP_PCB is record
      Local_IP  : IPaddrs.IPaddr;
      Remote_IP : IPaddrs.IPaddr;

      So_Options : AIP.U16_T;
      TOS : AIP.U8_T;
      TTL : AIP.U8_T;
   end record;

   procedure IP_Route
     (Dst_IP : IPaddrs.IPaddr; Netif : out NIF.Netif_Id);

   procedure IP_Output_If
     (Buf : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      TTL : AIP.U8_T;
      TOS : AIP.U8_T;
      Proto : AIP.U8_T;
      Netif : NIF.Netif_Id;
      Err : out AIP.Err_T);

end AIP.IP;
