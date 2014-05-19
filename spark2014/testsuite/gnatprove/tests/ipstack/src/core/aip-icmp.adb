------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with System;

with AIP.Checksum;
with AIP.ICMPH;
with AIP.Inet;
with AIP.IP;
with AIP.IPaddrs;
with AIP.IPH;

package body AIP.ICMP with
  SPARK_Mode => Off
is

   ICMP_Default_TTL : constant := 32;
   --  Make configurable???

   ----------------
   -- ICMP_Input --
   ----------------

   procedure ICMP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      Ihdr  : System.Address;
      IChdr : System.Address;
      Err   : Err_T;

      NH_Nif : EID;
      Remote_IP, NH_IP : IPaddrs.IPaddr;

   begin
      --  Latch address of IP header and retrieve an ICMP view of the incoming
      --  message.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP.Get_Next_Header
        (Buf,
         ICMPH.ICMP_Header_Size / 8,
         IChdr,
         Err);

      if not NIF.Offload (Netif, NIF.ICMP_CS)
           and then Checksum.Sum (Buf, Buffers.Buffer_Tlen (Buf)) /= 16#ffff#
      then
         Err := AIP.ERR_VAL;
      end if;

      if No (Err) then
         case ICMPH.ICMPH_I_Type (IChdr) is
            when ICMPH.ICMP_Type_Echo =>

               --  Should we reply with the original dest address as source???

               Remote_IP := IPH.IPH_Src_Address (Ihdr);

               --  Resolve next hop (discard if unreachable)

               IP.IP_Route (Remote_IP, NH_IP, NH_Nif);

               if NH_Nif /= NIF.IF_NOID then

                  --  Switch ICMP type to Echo reply

                  ICMPH.Set_ICMPH_I_Type (IChdr, ICMPH.ICMP_Type_Echo_Reply);

                  --  Recompute ICMP checksum

                  ICMPH.Set_ICMPH_Checksum (IChdr, 0);

                  if not NIF.Offload (NH_Nif, NIF.ICMP_CS) then
                     ICMPH.Set_ICMPH_Checksum (IChdr,
                       not Checksum.Sum (Buf, Buffers.Buffer_Tlen (Buf)));
                  end if;

                  --  Send out reply

                  IP.IP_Output_If
                    (Buf    => Buf,
                     Src_IP => IPaddrs.IP_ADDR_ANY,
                     Dst_IP => Remote_IP,
                     NH_IP  => NH_IP,
                     TTL    => ICMP_Default_TTL,
                     TOS    => 0,
                     Proto  => IPH.IP_Proto_ICMP,
                     Netif  => NH_Nif,
                     Err    => Err);
               end if;

            when others =>

               --  Discard

               null;
         end case;
      end if;
   end ICMP_Input;

   -----------------
   -- ICMP_Reject --
   -----------------

   procedure ICMP_Reject
     (IP_Buf : Buffers.Buffer_Id;
      I_Type : U8_T;
      Code   : U8_T)
   is
      Buf   : Buffers.Buffer_Id;
      Err   : Err_T;
      IChdr : System.Address;

      IP_Ihdr : constant System.Address := Buffers.Buffer_Payload (IP_Buf);

      Payload_Length : U16_T;

      Remote_IP : IPaddrs.IPaddr;
      NH_IP     : IPaddrs.IPaddr;
      NH_Nif    : EID;
   begin
      --  Continue only if we at least have a valid IP header in IP_Buf

      if Buffers.Buffer_Len (IP_Buf) >= IPH.IP_Header_Size / 8 then
         Payload_Length :=
           U16_T'Min (IPH.IPH_Length (IP_Ihdr),
                      4 * U16_T (IPH.IPH_IHL (IP_Ihdr)) + 8);

         Buffers.Buffer_Alloc
           (Offset => Inet.HLEN_To (Inet.IP_LAYER),
            Size   => ICMPH.ICMP_Generic_Header_Size / 8 + Payload_Length,
            Kind   => Buffers.SPLIT_BUF,
            Buf    => Buf);

         if Buf /= Buffers.NOBUF then
            IChdr := Buffers.Buffer_Payload (Buf);
            ICMPH.Set_ICMPH_I_Type   (IChdr, I_Type);
            ICMPH.Set_ICMPH_Code     (IChdr, Code);
            ICMPH.Set_ICMP_Generic_H_Pointer (IChdr, 0);

            Buffers.Buffer_Header
              (Buf, -ICMPH.ICMP_Generic_Header_Size / 8, Err);
            pragma Assert (No (Err));

            Buffers.Buffer_Copy
              (Dst => Buf,
               Src => IP_Buf,
               Len => Payload_Length,
               Err => Err);

            Buffers.Buffer_Header
              (Buf, ICMPH.ICMP_Generic_Header_Size / 8, Err);

            if No (Err) then
               Remote_IP := IPH.IPH_Src_Address (IP_Ihdr);
               IP.IP_Route (Remote_IP, NH_IP, NH_Nif);

               if NH_Nif /= NIF.IF_NOID then

                  --  Initialize checksum to 0 to compute actual value

                  ICMPH.Set_ICMPH_Checksum (IChdr, 0);

                  if not NIF.Offload (NH_Nif, NIF.ICMP_CS) then

                     --  Compute and set checksum

                     ICMPH.Set_ICMPH_Checksum (IChdr,
                       not Checksum.Sum (Buf, Buffers.Buffer_Tlen (Buf)));
                  end if;

                  IP.IP_Output_If
                    (Buf    => Buf,
                     Src_IP => IPaddrs.IP_ADDR_ANY,
                     Dst_IP => Remote_IP,
                     NH_IP  => NH_IP,
                     TTL    => ICMP_Default_TTL,
                     TOS    => 0,
                     Proto  => IPH.IP_Proto_ICMP,
                     Netif  => NH_Nif,
                     Err    => Err);
               end if;
            end if;

            Buffers.Buffer_Blind_Free (Buf);
         end if;
      end if;
   end ICMP_Reject;

end AIP.ICMP;
