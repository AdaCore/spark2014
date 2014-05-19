------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with System;

package AIP.Conversions is

   pragma Preelaborate;

   function Ofs (A : System.Address; Offset : Integer) return System.Address;
   --  Return A + Offset

   function Diff (A : System.Address; B : System.Address) return Integer;
   --  Return A - B

   procedure Memcpy
     (Dst : System.Address;
      Src : System.Address;
      Len : Integer)
   with
     Depends => (null => (Dst, Src, Len));
   pragma Export (C, Memcpy, "aip_memcpy");
   --  Copies N storage units from area starting at Src to area starting at
   --  Dest. The memory areas must not overlap, or the result of this call is
   --  undefined.

end AIP.Conversions;
