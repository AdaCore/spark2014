------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;

with AIP.Checksum;
with AIP.ICMPH;
with AIP.Inet;
with AIP.IP;
with AIP.IPaddrs;
with AIP.IPH;

package body AIP.ICMP is

   ICMP_Default_TTL : constant := 32;
   --  Make configurable???

   ----------------
   -- ICMP_Input --
   ----------------

   procedure ICMP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      pragma Unreferenced (Netif);

      Ihdr  : System.Address;
      IChdr : System.Address;
      Err   : Err_T;

      NH_Nif : EID;
      Remote_IP, NH_IP : IPaddrs.IPaddr;

   begin
      Ihdr := Buffers.Buffer_Payload (Buf);

      --  Skip IP header

      Buffers.Buffer_Header (Buf, -(4 * S16_T (IPH.IPH_IHL (Ihdr))), Err);
      IChdr := Buffers.Buffer_Payload (Buf);

      if No (Err) then
         case ICMPH.ICMPH_I_Type (IChdr) is
            when ICMPH.ICMP_Type_Echo =>

               --  Switch ICMP type to Echo reply

               ICMPH.Set_ICMPH_I_Type (IChdr, ICMPH.ICMP_Type_Echo_Reply);

               --  Recompute ICMP checksum

               ICMPH.Set_ICMPH_Checksum (IChdr, 0);
               ICMPH.Set_ICMPH_Checksum (IChdr,
                 not Checksum.Sum (Buf, Buffers.Buffer_Tlen (Buf)));

               --  Send out reply
               --  Should we reply with the original dest address as source???

               Remote_IP := IPH.IPH_Src_Address (Ihdr);
               IP.IP_Route (Remote_IP, NH_IP, NH_Nif);

               if NH_Nif /= NIF.IF_NOID then
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

      Buffers.Buffer_Blind_Free (Buf);
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
           (Inet.HLEN_To (Inet.IP_LAYER),
            ICMPH.ICMP_Generic_Header_Size / 8 + Payload_Length,
            Buffers.SPLIT_BUF,
            Buf);

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

            ICMPH.Set_ICMPH_Checksum (IChdr, 0);
            ICMPH.Set_ICMPH_Checksum (IChdr,
              not Checksum.Sum (Buf, Buffers.Buffer_Tlen (Buf)));

            if No (Err) then
               Remote_IP := IPH.IPH_Src_Address (IP_Ihdr);
               IP.IP_Route (Remote_IP, NH_IP, NH_Nif);

               if NH_Nif /= NIF.IF_NOID then
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
