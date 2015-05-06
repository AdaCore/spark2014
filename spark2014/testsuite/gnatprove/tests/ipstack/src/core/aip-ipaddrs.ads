------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  IP address definition and related operations

package AIP.IPaddrs is

   pragma Pure;

   --  We only support IPV4, so represent IP addresses as 32bit modular types,
   --  which is efficient and allows easy bit shifting and masking operations.

   subtype IPaddr is AIP.M32_T;

   IP_ADDR_ANY      : constant IPaddr := 0;
   IP_ADDR_LOOPBACK : constant IPaddr := 16#7f000001#;
   IP_ADDR_BCAST    : constant IPaddr := 16#ffffffff#;

   function IP4 (A, B, C, D : AIP.U8_T) return IPaddr;
   --  Return the IP address value corresponding to A.B.C.D in dotted notation

   function Any (IP : IPaddr) return Boolean;
   --  If IP is IP_ADDR_ANY

   function Same (IP1, IP2 : IPaddr) return Boolean;
   --  If IP1 is exactly identical to IP2

   function Match (IP1, IP2 : IPaddr) return Boolean;
   --  If IP1 encompasses IP2 or the other way around (Same or one is Any)

end AIP.IPaddrs;
