------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  UDP Header definition and accessors (internal)

--# inherit AIP.Inet, AIP.Conversions;

package AIP.UDPH is

   type UDP_Header is record
      Src_Port : M16_T;  -- UDP source port
      Dst_Port : M16_T;  -- UDP destination port
      Len : U16_T;       -- UDP datagram length
      Sum : U16_T;       -- UDP dataram checksum
   end record;

   function UDPH_SRC (Uhdr : AIP.IPTR_T) return M16_T;
   function UDPH_DST (Uhdr : AIP.IPTR_T) return M16_T;
   function UDPH_LEN (Uhdr : AIP.IPTR_T) return U16_T;
   function UDPH_SUM (Uhdr : AIP.IPTR_T) return U16_T;

   procedure UDPH_Set_SRC (Uhdr : AIP.IPTR_T; V : M16_T);
   procedure UDPH_Set_DST (Uhdr : AIP.IPTR_T; V : M16_T);
   procedure UDPH_Set_LEN (Uhdr : AIP.IPTR_T; V : U16_T);
   procedure UDPH_Set_SUM (Uhdr : AIP.IPTR_T; V : U16_T);

private

   pragma Inline (UDPH_SRC);
   pragma Inline (UDPH_DST);
   pragma Inline (UDPH_LEN);
   pragma Inline (UDPH_SUM);

   pragma Inline (UDPH_Set_SRC);
   pragma Inline (UDPH_Set_DST);
   pragma Inline (UDPH_Set_LEN);
   pragma Inline (UDPH_Set_SUM);

end AIP.UDPH;
