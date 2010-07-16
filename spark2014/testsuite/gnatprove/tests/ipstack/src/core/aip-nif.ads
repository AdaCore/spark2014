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

   Max_LL_Address_Length : constant := 6;
   --  Make this configurable???
   --  6 is enough for Ethernet

   type Netif_Name is new String (1 .. 2);
   type Netif_LL_Address is new String (1 .. Max_LL_Address_Length);

   type Netif is record
      Name              : Netif_Name;
      --  Unique name of interface

      LL_Address        : Netif_LL_Address;
      --  Link-level address

      LL_Address_Length : U8_T;
      --  Actual length of link level address

      MTU               : U16_T;
      --  Maximum Transmission Unit

      IP                : IPaddrs.IPaddr;
      --  IP address

      Mask              : IPaddrs.IPaddr;
      --  Netmask

      Broadcast         : IPaddrs.IPaddr;
      --  Broadcast address: (IP and mask) or (not mask)

      Input_CB          : Callbacks.CBK_Id;
      --  Packet input callback
      --  procedure I (Buf : Buffer_Id; Nid : Netif_Id);

      Output_CB         : Callbacks.CBK_Id;
      --  Packet output callback (called by network layer)
      --  procedure O (Buf : Buffer_Id; Nid : Netif_Id; Dst_Address : IPaddr);

      Link_Output_CB   : Callbacks.CBK_Id;
      --  Link level packet output callback (called by ARP layer)
      --  procedure LO (Buf : Buffer_Id; Nid : Netif_Id);

      Dev               : IPTR_T;
      --  Driver private information
   end record;
   pragma Convention (C, Netif);

   function Get_Netif (Nid : Netif_Id) return IPTR_T;
   pragma Export (C, Get_Netif, "AIP_get_netif");
   --  Return pointer to Netif record for the given netif

end AIP.NIF;
