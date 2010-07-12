------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.Conversions;

with AIP.IPH;
with AIP.UDP;

package body AIP.IP is

   ----------------
   -- IP_Forward --
   ----------------

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
   begin
      --  ??? TBD
      raise Program_Error;
   end IP_Forward;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      Err  : Err_T := AIP.NOERR;

      Ihdr_Ptr : constant IPTR_T := Buffers.Buffer_Payload (Buf);

      Ihdr : IPH.IP_Header;
      for Ihdr'Address use Conversions.To_ADDR (Ihdr_Ptr);
      pragma Import (Ada, Ihdr);

      Local : Boolean;
      --  Set True for a packet bound for the local node

   begin
      --  Perform various sanity checks prior to accepting the packet:
      --    short packets
      --    IP version
      --    checksum

      if True
           or else Buffers.Buffer_Tlen (Buf) < IP_HLEN
           or else Buffers.Buffer_Tlen (Buf) < U16_T (IPH.IPH_IHL (Ihdr) * 4)
           or else IPH.IPH_Version (Ihdr) /= 4
           or else (IPH.IPH_Checksum (Ihdr) /= 0
                     and then Checksum.Checksum
                                (Packet => Ihdr_Ptr,
                                 Length => Natural (IPH.IPH_IHL (Ihdr)) * 4)
                                /= 16#ffff#)
      then
         Err := AIP.ERR_USE;
      end if;

      --  Check TTL

      if No (Err) and then IPH.IPH_TTL (Ihdr) = 0 then
         --  Generate ICMP TTL exceeded???

         Err := AIP.ERR_USE;
      end if;

      --  Check destination address

      if No (Err) then
         if NIF.Is_Local_Address (Netif, IPH.IPH_Dst_Address (Ihdr))
              or else
            NIF.Is_Broadcast_Address (Netif, IPH.IPH_Dst_Address (Ihdr))
         --  ??? multicast
         --  ??? case of a packet for one of my IP addresses but arriving
         --  on another interface?
         then
            Local := True;

         elsif Config.Enable_Forwarding then
            Local := False;

         else
            --  Discard packet that is not for this node if forwarding is not
            --  enabled.

            Err := AIP.ERR_USE;
         end if;
      end if;

      --  Dispatch to upper layer or forward to next hop

      if No (Err) then
         if Local then
            case IPH.IPH_Protocol (Ihdr) is
               when IPH.IP_Proto_UDP =>
                  UDP.UDP_Input (Buf, Netif);

--             when IPH.IP_Proto_TCP =>
--                TCP.TCP_Input (Buf, Netif);

--             when IPH.IP_Proto_ICMP =>
--                ICMP.ICMP_Input (Buf, Netif);

               when others =>
                  --  Discard IP packet with unknown protocol

                  Err := AIP.ERR_USE;
            end case;
         else
            IP_Forward (Buf, Netif);
         end if;
      end if;
   end IP_Input;

   ------------------
   -- IP_Output_If --
   ------------------

   procedure IP_Output_If
     (Buf    : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      TTL    : AIP.U8_T;
      TOS    : AIP.U8_T;
      Proto  : AIP.U8_T;
      Netif  : NIF.Netif_Id;
      Err    : out AIP.Err_T)
   is
      pragma Unreferenced (Buf, Src_IP, Dst_IP, TTL, TOS, Proto, Netif);
   begin
      Err := AIP.ERR_USE;
   end IP_Output_If;

   procedure IP_Route (Dst_IP : IPaddrs.IPaddr; Netif : out NIF.Netif_Id) is
      pragma Unreferenced (Dst_IP);
   begin
      --  ??? Only one route known: the default interface
      --  ??? Next hop should be a couple (next-hop-if, next-hop-addr)
      Netif := NIF.Netif_Id'First;
   end IP_Route;

end AIP.IP;
