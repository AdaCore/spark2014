------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Network Interface abstraction

with System;

with AIP.Buffers;
with AIP.Callbacks;
with AIP.IPaddrs;

--# inherit System, AIP.Buffers, AIP.Callbacks, AIP.IPaddrs;

package AIP.NIF is
   pragma Preelaborate;

   MAX_NETIF : constant := 20;
   --  ??? Should be defined in a central configuration/dimensioning package

   type Netif_State is (Invalid, Down, Up);
   pragma Convention (C, Netif_State);
   --  State of a network interface

   --  Invalid: no associated link-level driver
   --  Down:    driver present but interface inactive
   --  Up:      active interface

   subtype Netif_Id is AIP.EID range 1 .. MAX_NETIF;
   IF_NOID : constant AIP.EID := -1;
   --  ??? What about 0?

   function NIF_Addr      (Nid : Netif_Id) return IPaddrs.IPaddr;
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

   procedure Low_Level_Output
     (Nid : Netif_Id;
      Buf : Buffers.Buffer_Id);

private

   Max_LL_Address_Length : constant := 6;
   --  Make this configurable???
   --  6 is enough for Ethernet

   subtype Netif_Name_Range is Integer range 1 .. 2;
   type Netif_Name is array (Netif_Name_Range) of Character;

   subtype Netif_LL_Address_Range is Integer range 1 .. Max_LL_Address_Length;
   type Netif_LL_Address is array (Netif_LL_Address_Range) of AIP.U8_T;

   procedure Allocate_Netif (Nid : out AIP.EID);
   pragma Export (C, Allocate_Netif, "AIP_allocate_netif");
   --  Allocate a new netif Id. Return IF_NOID if none is available

   function Get_Netif (Nid : Netif_Id) return System.Address;
   pragma Export (C, Get_Netif, "AIP_get_netif");
   --  Return pointer to Netif record for the given netif

end AIP.NIF;
