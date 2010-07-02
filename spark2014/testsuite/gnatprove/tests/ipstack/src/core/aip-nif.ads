------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Network Interface abstraction

with AIP.IPaddrs;

package AIP.NIF is

   MAX_NETIF : constant := 20;
   --  ??? Should be defined in a central configuration/dimensioning package

   subtype Netif_Id is AIP.EID range 1 .. MAX_NETIF;
   IF_NOID : constant AIP.EID := -1;
   --  ??? What about 0?

   function NIF_IP        (Nid : Netif_Id) return IPaddrs.IPaddr;
   function NIF_MASK      (Nid : Netif_Id) return IPaddrs.IPaddr;
   --  function NIF_BCAST (Nid : Netif_Id) return IPaddrs.IPaddr; ???

private

   type Netif is record
      IPaddr  : IPaddrs.IPaddr;
      Netmask : IPaddrs.IPaddr;
   end record;

end AIP.NIF;
