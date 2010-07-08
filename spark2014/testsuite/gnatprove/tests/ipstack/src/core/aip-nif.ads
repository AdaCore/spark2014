------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Network Interface abstraction

with AIP.Callbacks;
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

   function Is_Local_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean;
   --  True if Addr is a local address for Nid

   function Is_Broadcast_Address
     (Nid  : Netif_Id;
      Addr : IPaddrs.IPaddr) return Boolean;
   --  True if Addr is a broadcast address for Nid

private

   type Netif is record
      IPaddr  : IPaddrs.IPaddr;
      Netmask : IPaddrs.IPaddr;

      Input_CB  : Callbacks.CBK_Id;
      Output_CB : Callbacks.CBK_Id;
   end record;

end AIP.NIF;
