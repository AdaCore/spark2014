------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.IP is

   procedure IP_Route
     (Dst_IP : IPaddrs.IPaddr; Netif : out NIF.Netif_Id) is
   begin
      Netif := NIF.Netif_Id'First;
   end IP_Route;

   procedure IP_Output_If
     (Buf : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      TTL : AIP.U8_T;
      TOS : AIP.U8_T;
      Proto : AIP.U8_T;
      Netif : NIF.Netif_Id;
      Err : out AIP.Err_T) is
   begin
      Err := AIP.ERR_USE;
   end IP_Output_If;

end AIP.IP;
