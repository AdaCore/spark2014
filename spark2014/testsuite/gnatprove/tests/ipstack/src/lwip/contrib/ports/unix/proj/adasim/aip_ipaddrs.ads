------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package AIP_IPaddrs is

   type IPaddr_Id is private;
   IP_ADDR_ANY : constant IPaddr_Id;

private

   type IPaddr is mod 2 ** 32;
   type IPaddr_Id is access all IPaddr;

   IP_ADDR_ANY : constant IPaddr_Id := null;

end  AIP_IPaddrs;
