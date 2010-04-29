------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP address definition and related operations

--# inherit AIP.Inet;

package AIP.IPaddrs is

   subtype IPaddr is AIP.U32_T;
   subtype IPaddr_Id is AIP.IPTR_T;

   IP_ADDR_ANY : constant IPaddr_Id := AIP.NULID;

   function IP4 (A, B, C, D : AIP.U8_T) return IPaddr;
   --  Return the network ordered IP address value corresponding to A.B.C.D in
   --  dotted notation.

end AIP.IPaddrs;
