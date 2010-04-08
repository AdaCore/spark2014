------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP_Ctypes;

package AIP_IPaddrs is

   type IPaddr_Id is private;
   IP_ADDR_ANY : constant IPaddr_Id;

private

   type IPaddr is new AIP_Ctypes.U32_T;
   type IPaddr_Id is access all IPaddr;

   IP_ADDR_ANY : constant IPaddr_Id := null;

end  AIP_IPaddrs;
