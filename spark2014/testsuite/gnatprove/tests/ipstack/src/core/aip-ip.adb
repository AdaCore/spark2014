------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;
with AIP.Conversions;

with AIP.IPH;
with AIP.UDP;

package body AIP.IP is

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
   begin
      --  ??? TBD
      raise Program_Error;
   end IP_Forward;

   procedure IP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      Err : Err_T := AIP.NOERR;
      Ihdr : IPH.IP_Header;
      for Ihdr'Address use Conversions.To_ADDR (Buffers.Buffer_Payload (Buf));
      pragma Import (Ada, Ihdr);

      Local : Boolean;
      --  Set True for a packet bound for the local node

   begin
      --  Discard short packet

      if Buffers.Buffer_Tlen (Buf) < 20 then
         --  Discard short packet

         Err := AIP.ERR_USE;
      end if;

      --  Verify IP version

      if No (Err) then
         --  TBD???
         null;
      end if;
      --  Verify IP checksum

      if No (Err) then
         --  TBD???
         null;
      end if;

      --  Check TTL

      if No (Err) then
         --  TBD???
         null;
      end if;

      --  Check destination address

      if No (Err) then
         if NIF.Is_Local_Address (Netif, IPH.IPH_Dst_Address (Ihdr))
              or else
            NIF.Is_Broadcast_Address (Netif, IPH.IPH_Dst_Address (Ihdr))
--  ??? multicast
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
