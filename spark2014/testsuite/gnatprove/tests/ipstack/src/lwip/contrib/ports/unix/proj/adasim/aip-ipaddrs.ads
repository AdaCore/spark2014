------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.IPaddrs is

   type IPaddr is mod 2 ** 32;
   subtype IPaddr_Id is AIP.IPTR_T;

   IP_ADDR_ANY : constant IPaddr_Id := AIP.NULID;

end AIP.IPaddrs;
