------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Inet, AIP.Conversions;

package body AIP.UDPH is

   --------------------
   -- Read accessors --
   --------------------

   function UDPH_SRC (Uhdr : AIP.IPTR_T) return M16_T is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      return Inet.ntohsm (H.Src_Port);
   end UDPH_SRC;

   function UDPH_DST (Uhdr : AIP.IPTR_T) return M16_T is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      return Inet.ntohsm (H.Dst_Port);
   end UDPH_DST;

   function UDPH_LEN (Uhdr : AIP.IPTR_T) return U16_T is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      return Inet.ntohsu (H.Len);
   end UDPH_LEN;

   function UDPH_SUM (Uhdr : AIP.IPTR_T) return U16_T is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      return Inet.ntohsu (H.Sum);
   end UDPH_SUM;

   ---------------------
   -- Write accessors --
   ---------------------

   procedure UDPH_Set_SRC (Uhdr : AIP.IPTR_T; V : M16_T) is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      H.Src_Port := Inet.htonsm (V);
   end UDPH_Set_SRC;

   procedure UDPH_Set_DST (Uhdr : AIP.IPTR_T; V : M16_T) is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      H.Dst_Port := Inet.htonsm (V);
   end UDPH_Set_DST;

   procedure UDPH_Set_LEN (Uhdr : AIP.IPTR_T; V : U16_T) is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      H.Len := Inet.htonsu (V);
   end UDPH_Set_LEN;

   procedure UDPH_Set_SUM (Uhdr : AIP.IPTR_T; V : U16_T) is
      H : UDP_Header;
      for H'Address use Conversions.To_ADDR (Uhdr);
   begin
      H.Sum := Inet.htonsu (V);
   end UDPH_Set_SUM;

end AIP.UDPH;
