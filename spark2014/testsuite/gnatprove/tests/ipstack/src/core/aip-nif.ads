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
   function NIF_Mask      (Nid : Netif_Id) return IPaddrs.IPaddr;
   function NIF_Broadcast (Nid : Netif_Id) return IPaddrs.IPaddr;

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
      IP        : IPaddrs.IPaddr;
      --  IP address of interface

      Mask      : IPaddrs.IPaddr;
      --  Netmask of interface

      Broadcast : IPaddrs.IPaddr;
      --  Broadcast address of interface: (IP and mask) or (not mask)

      Input_CB  : Callbacks.CBK_Id;
      --  Packet input callback

      Output_CB : Callbacks.CBK_Id;
      --  Packet output callback

      Dev       : IPTR_T;
      --  Driver private information
   end record;
   pragma Convention (C, Netif);

   function Get_Netif (Nid : Netif_Id) return IPTR_T;
   pragma Export (C, Get_Netif, "AIP_get_netif");
   --  Return pointer to Netif record for the given netif

end AIP.NIF;
