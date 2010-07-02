------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Conversions;

package body AIP.IPH is

   --------------------
   -- Read accessors --
   --------------------

   function IPH_HLEN (Ihdr : AIP.IPTR_T) return U4_T is
      H : IP_Header;
      for H'Address use Conversions.To_ADDR (Ihdr);
   begin
      return H.Hlen;
   end IPH_HLEN;

   function IPH_SRC (Ihdr : AIP.IPTR_T) return IPaddrs.IPaddr is
      H : IP_Header;
      for H'Address use Conversions.To_ADDR (Ihdr);
   begin
      return H.Src_IP;  -- nothl ?
   end IPH_SRC;

   function IPH_DST (Ihdr : AIP.IPTR_T) return IPaddrs.IPaddr is
      H : IP_Header;
      for H'Address use Conversions.To_ADDR (Ihdr);
   begin
      return H.Dst_IP;  -- nothl ?
   end IPH_DST;

end AIP.IPH;
