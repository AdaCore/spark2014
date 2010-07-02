------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Inet is

   --  Network byte ordering is big endian.  Swap value as needed.

   --------------
   -- htonlm/u --
   --------------

   function htonlm (V : AIP.M32_T) return AIP.M32_T is
      NetV : AIP.M32_T;
   begin
      --# accept F, 22, "Value of expression is invariant";
      if AIP.HOST_BIG_ENDIAN then
      --# end accept;
         NetV := V;
      else
         NetV := ((V and 16#000000FF#) * (2 ** 24))
              or ((V and 16#0000FF00#) * (2 ** 8))
              or ((V and 16#00FF0000#) / (2 ** 8))
              or ((V and 16#FF000000#) / (2 ** 24));
      end if;

      return NetV;

   end htonlm;

   function htonlu (V : AIP.U32_T) return AIP.U32_T is
   begin
      return U32_T (htonlm (AIP.M32_T (V)));
   end htonlu;

   --------------
   -- htonsm/u --
   --------------

   function htonsm (V : AIP.M16_T) return AIP.M16_T is
      NetV : AIP.M16_T;
   begin
      --# accept F, 22, "Value of expression is invariant";
      if AIP.HOST_BIG_ENDIAN then
      --# end accept;
         NetV := V;
      else
         NetV := ((V and 16#00FF#) * (2 ** 8))
              or ((V and 16#FF00#) / (2 ** 8));
      end if;

      return NetV;
   end htonsm;

   function htonsu (V : AIP.U16_T) return AIP.U16_T is
   begin
      return U16_T (htonsm (AIP.M16_T (V)));
   end htonsu;

   --------------
   -- ntohlm/u --
   --------------

   function ntohlm (V : AIP.M32_T) return AIP.M32_T is
   begin
      return htonlm (V);
   end ntohlm;

   function ntohlu (V : AIP.U32_T) return AIP.U32_T is
   begin
      return htonlu (V);
   end ntohlu;

   --------------
   -- ntohsm/u --
   --------------

   function ntohsm (V : AIP.M16_T) return AIP.M16_T is
   begin
      return htonsm (V);
   end ntohsm;

   function ntohsu (V : AIP.U16_T) return AIP.U16_T is
   begin
      return htonsu (V);
   end ntohsu;

   -------------
   -- HLEN_To --
   -------------

   TRANSPORT_BUF_HLEN : constant := 20;
   IP_BUF_HLEN : constant := 20;
   LINK_BUF_HLEN : constant := 16;

   function HLEN_To (L : Inet_Layer) return U16_T is
      Room : U16_T := 0;
   begin
      if L >= TRANSPORT_LAYER then
         Room := Room + TRANSPORT_BUF_HLEN;
      end if;
      if L >= IP_LAYER then
         Room := Room + IP_BUF_HLEN;
      end if;
      Room := Room + LINK_BUF_HLEN;

      return Room;
   end HLEN_To;

end AIP.Inet;
