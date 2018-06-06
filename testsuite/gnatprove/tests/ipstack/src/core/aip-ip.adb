------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;

with AIP.IPH;
with AIP.ICMPH;

with AIP.ICMP;
with AIP.UDP;
with AIP.TCP;

package body AIP.IP with
  Refined_State => (State => IP_Serial,
                    FIB   => Default_Router)
is

   Default_Router : IPaddrs.IPaddr := IPaddrs.IP_ADDR_ANY;

   IP_Serial : AIP.M16_T := 0;

   ---------------------
   -- Get_Next_Header --
   ---------------------

   procedure Get_Next_Header
     (Buf  : Buffers.Buffer_Id;
      Nlen : AIP.U16_T;
      Nhdr : out System.Address;
      Err  : out AIP.Err_T)
   is
      Ihdr : System.Address;
      --  Address of the IP header in BUF

      IPhlen : AIP.U16_T;
      --  Length of this header
   begin
      pragma Assert (Buffers.Buffer_Len (Buf) >= IPH.IP_Header_Size / 8);

      Ihdr := Buffers.Buffer_Payload (Buf);
      IPhlen := AIP.U16_T (IPH.IPH_IHL (Ihdr)) * 4;

      --  ERR_MEM if the buffer length is such that this couldn't possibly be a
      --  UDP datagram, when there's not even room for the UDP & IP headers.
      --  Otherwise, move payload to the UDP header by hiding the IP one.

      if Buffers.Buffer_Len (Buf) < IPhlen + Nlen then
         Err := AIP.ERR_MEM;
      else
         Buffers.Buffer_Header (Buf, -AIP.S16_T (IPhlen), Err);
      end if;

      --  If the length check and the payload move went fine, we have the upper
      --  layer protocol header at hand.

      if AIP.No (Err) then
         Nhdr := Buffers.Buffer_Payload (Buf);
      else
         Nhdr := System.Null_Address;
      end if;
   end Get_Next_Header;

   ----------------
   -- IP_Forward --
   ----------------

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) with
     SPARK_Mode => Off
   is
      pragma Unreferenced (Netif);
   begin
      --  ??? TBD

      Buffers.Buffer_Blind_Free (Buf);
   end IP_Forward;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input (Netif : NIF.Netif_Id; Buf : Buffers.Buffer_Id)
   is
      Err  : AIP.Err_T := AIP.NOERR;

      Ihdr : System.Address;

      Dst_Netif : AIP.EID;
      --  Local netif whose address is the destination address of the datagram

      Local : Boolean := False;
      --  Set True for a packet bound for the local node

      procedure Dispatch_Upper
        (Proto : AIP.U8_T;
         Buf   : Buffers.Buffer_Id;
         Netif : NIF.Netif_Id;
         Err   : out AIP.Err_T)
      --  Dispatch packet in Buf received on Netif to upper protocol layer
      --  according to IP protocol identifier Proto.
      with
        Global => (Input  => (UDP.State, Default_Router),
                   In_Out => (Buffers.State, TCP.State, IP_Serial));

      --------------------
      -- Dispatch_Upper --
      --------------------

      procedure Dispatch_Upper
        (Proto : AIP.U8_T;
         Buf   : Buffers.Buffer_Id;
         Netif : NIF.Netif_Id;
         Err   : out AIP.Err_T)
      is
      begin
         Err := NOERR;

         case Proto is
            when IPH.IP_Proto_UDP =>
               UDP.UDP_Input (Buf, Netif);

            when IPH.IP_Proto_TCP =>
               TCP.TCP_Input (Buf, Netif);

            when IPH.IP_Proto_ICMP =>
               ICMP.ICMP_Input (Buf, Netif);

            when others =>
               --  Discard IP packet with unknown protocol

               ICMP.ICMP_Reject
                 (Buf,
                  I_Type => ICMPH.ICMP_Type_Dest_Unreachable,
                  Code   => ICMPH.ICMP_Unreach_Code_Proto_Unreachable);

               Err := AIP.ERR_USE;
         end case;
      end Dispatch_Upper;

   --  Start of processing for IP_Input

   begin
      Ihdr := Buffers.Buffer_Payload (Buf);

      --  Perform various sanity checks prior to accepting the packet:
      --    short packets
      --    IP version
      --    checksum

      if False
        or else Buffers.Buffer_Tlen (Buf) < IPH.IP_Header_Size / 8
        or else Buffers.Buffer_Tlen (Buf)
                  < AIP.U16_T (IPH.IPH_IHL (Ihdr)) * 4
        or else IPH.IPH_Version (Ihdr) /= 4
        or else (IPH.IPH_Checksum (Ihdr) /= 0
                   and then not NIF.Offload (Netif, NIF.IP_CS)
                   and then Checksum.Sum
                            (Buf     => Buf,
                             Length  => AIP.U16_T (IPH.IPH_IHL (Ihdr)) * 4)
                             /= 16#Ffff#)
      then
         Err := AIP.ERR_USE;
      end if;

      --  Check TTL

      if AIP.No (Err) and then IPH.IPH_TTL (Ihdr) = 0 then
         --  Generate ICMP TTL exceeded???

         Err := AIP.ERR_USE;
      end if;

      --  Check destination address

      if AIP.No (Err) then
         NIF.Get_Netif_By_Address
           (Addr => IPH.IPH_Dst_Address (Ihdr),
            Mask => False,
            Nid  => Dst_Netif);

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

      if AIP.No (Err) then
         if Local then
            pragma Warnings (Off, "unused assignment to ""Err""");
            --  Discard error from upper layer
            Dispatch_Upper (IPH.IPH_Protocol (Ihdr), Buf, Netif, Err);
            pragma Warnings (On, "unused assignment to ""Err""");
         else
            IP_Forward (Buf, Netif);
         end if;
      end if;

      Buffers.Buffer_Blind_Free (Buf);
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
   with
     Refined_Global => (In_Out => (Buffers.State, IP_Serial))
   is
      Ihdr : System.Address;
   begin
      Buffers.Buffer_Header (Buf, IPH.IP_Header_Size / 8, Err);
      if AIP.No (Err) then
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

         if not NIF.Offload (Netif, NIF.IP_CS) then
            IPH.Set_IPH_Checksum    (Ihdr,
              not Checksum.Sum (Buf, 4 * AIP.U16_T (IPH.IPH_IHL (Ihdr))));
         end if;

         NIF.Output (Netif, Buf, NH_IP);
      end if;
   end IP_Output_If;

   --------------
   -- IP_Route --
   --------------

   procedure IP_Route
     (Dst_IP   : IPaddrs.IPaddr;
      Next_Hop : out IPaddrs.IPaddr;
      Netif    : out AIP.EID)
   with
     Refined_Global => (Input => Default_Router)
   is
   begin
      --  Currently we support only direct interface routes and the default
      --  route???

      NIF.Get_Netif_By_Address (Addr => Dst_IP, Mask => True, Nid => Netif);
      if Netif /= NIF.IF_NOID then
         Next_Hop := Dst_IP;

      elsif Default_Router /= IPaddrs.IP_ADDR_ANY then
         NIF.Get_Netif_By_Address
           (Addr => Default_Router, Mask => True, Nid => Netif);
         Next_Hop := Default_Router;

      else
         --  Netif is IF_NOID, no route to destination, so no next hop address

         Next_Hop := IPaddrs.IP_ADDR_ANY;
      end if;
   end IP_Route;

   ------------------------
   -- Set_Default_Router --
   ------------------------

   procedure Set_Default_Router (IPA : IPaddrs.IPaddr) with
     Refined_Global => (Output => Default_Router)
   is
   begin
      Default_Router := IPA;
   end Set_Default_Router;

end AIP.IP;
