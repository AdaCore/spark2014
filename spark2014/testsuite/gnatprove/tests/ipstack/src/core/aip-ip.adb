------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;

with AIP.Checksum;
with AIP.Config;

with AIP.ICMP;
with AIP.IPH;
with AIP.UDP;

package body AIP.IP is

   Default_Router : IPaddrs.IPaddr := IPaddrs.IP_ADDR_ANY;

   IP_Serial : M16_T := 0;

   ----------------
   -- IP_Forward --
   ----------------

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      pragma Unreferenced (Netif);
   begin
      --  ??? TBD

      Buffers.Buffer_Blind_Free (Buf);
   end IP_Forward;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input (Netif : NIF.Netif_Id; Buf : Buffers.Buffer_Id) is
      Err  : Err_T := AIP.NOERR;

      Ihdr : constant System.Address := Buffers.Buffer_Payload (Buf);

      Dst_Netif : EID;
      --  Local netif whose address is the destination address of the datagram

      Local : Boolean;
      --  Set True for a packet bound for the local node

   begin
      --  Perform various sanity checks prior to accepting the packet:
      --    short packets
      --    IP version
      --    checksum

      if False
           or else Buffers.Buffer_Tlen (Buf) < IP_HLEN
           or else Buffers.Buffer_Tlen (Buf) < U16_T (IPH.IPH_IHL (Ihdr)) * 4
           or else IPH.IPH_Version (Ihdr) /= 4
           or else (IPH.IPH_Checksum (Ihdr) /= 0
                     and then Checksum.Sum
                                (Buf     => Buf,
                                 Length  => Natural (IPH.IPH_IHL (Ihdr)) * 4)
                                /= 16#Ffff#)
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
         NIF.Get_Netif_By_Address
           (IPH.IPH_Dst_Address (Ihdr), Mask => False, Nid => Dst_Netif);

         if Dst_Netif /= NIF.IF_NOID then
         --  case of multicast???
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

               when IPH.IP_Proto_ICMP =>
                  ICMP.ICMP_Input (Buf, Netif);

               when others =>
                  --  Discard IP packet with unknown protocol

                  Err := AIP.ERR_USE;
            end case;
         else
            IP_Forward (Buf, Netif);
         end if;
      end if;

      if Any (Err) then
         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end IP_Input;

   ------------------
   -- IP_Output_If --
   ------------------

   procedure IP_Output_If
     (Buf    : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      NH_IP  : IPaddrs.IPaddr;
      TTL    : AIP.U8_T;
      TOS    : AIP.U8_T;
      Proto  : AIP.U8_T;
      Netif  : NIF.Netif_Id;
      Err    : out AIP.Err_T)
   is
      Ihdr : System.Address;
   begin
      Buffers.Buffer_Header (Buf, IPH.IP_Header'Size / 8, Err);
      if No (Err) then
         IP_Serial := IP_Serial + 1;

         Ihdr := Buffers.Buffer_Payload (Buf);
         IPH.Set_IPH_Version     (Ihdr, 4);
         IPH.Set_IPH_IHL         (Ihdr, 5);
         IPH.Set_IPH_TOS         (Ihdr, TOS);
         IPH.Set_IPH_Length      (Ihdr, Buffers.Buffer_Tlen (Buf));
         IPH.Set_IPH_Ident       (Ihdr, IP_Serial);
         IPH.Set_IPH_Flags       (Ihdr, 0);
         IPH.Set_IPH_Frag_Offset (Ihdr, 0);
         IPH.Set_IPH_TTL         (Ihdr, TTL);
         IPH.Set_IPH_Protocol    (Ihdr, Proto);
         IPH.Set_IPH_Checksum    (Ihdr, 0);
         if Src_IP /= IPaddrs.IP_ADDR_ANY then
            IPH.Set_IPH_Src_Address (Ihdr, Src_IP);
         else
            IPH.Set_IPH_Src_Address (Ihdr, NIF.NIF_Addr (Netif));
         end if;
         IPH.Set_IPH_Dst_Address (Ihdr, Dst_IP);

         IPH.Set_IPH_Checksum    (Ihdr,
           not Checksum.Sum (Buf, 4 * Natural (IPH.IPH_IHL (Ihdr))));

         NIF.Output (Netif, Buf, NH_IP);
      end if;
   end IP_Output_If;

   --------------
   -- IP_Route --
   --------------

   procedure IP_Route
     (Dst_IP   : IPaddrs.IPaddr;
      Next_Hop : out IPaddrs.IPaddr;
      Netif    : out EID)
   is
   begin
      --  Currently we support only direct interface routes and the default
      --  route???

      NIF.Get_Netif_By_Address (Dst_IP, Mask => True, Nid => Netif);
      if Netif /= NIF.IF_NOID then
         Next_Hop := Dst_IP;

      elsif Default_Router /= IPaddrs.IP_ADDR_ANY then
         NIF.Get_Netif_By_Address (Default_Router, Mask => True, Nid => Netif);
         Next_Hop := Default_Router;
      end if;
   end IP_Route;

   ------------------------
   -- Set_Default_Router --
   ------------------------

   procedure Set_Default_Router (IPA : IPaddrs.IPaddr) is
   begin
      Default_Router := IPA;
   end Set_Default_Router;

end AIP.IP;
