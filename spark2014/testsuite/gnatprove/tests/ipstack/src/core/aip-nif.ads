------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Network Interface abstraction

with System;

with AIP.Config;
with AIP.Buffers;
with AIP.IPaddrs;

--# inherit System, AIP, AIP.Config, AIP.Buffers, AIP.Callbacks, AIP.IPaddrs;

package AIP.NIF is
   pragma Preelaborate;

   procedure Initialize;
   --  Initialize NIF subsystem

   type Netif_State is (Invalid, Down, Up);
   pragma Convention (C, Netif_State);
   --  State of a network interface

   --  Invalid: no associated link-level driver
   --  Down:    driver present but interface inactive
   --  Up:      active interface

   subtype Netif_Id is AIP.EID range 1 .. Config.MAX_NETIF;
   IF_NOID : constant AIP.EID := 0;

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

   procedure Get_LL_Address
     (Nid               : Netif_Id;
      LL_Address        : out AIP.LL_Address;
      LL_Address_Length : out AIP.LL_Address_Range);
   --  Copy Nid's link level address into LL_Address, and set LL_Address_Length
   --  to the amount of data copied.
   --  LL_Address'First is expected to be 1.

   procedure Output
     (Nid         : Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr);
   --  Call Nid's Ouptut_CB callback with Buf

   procedure Link_Output
     (Nid : Netif_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T);
   --  Call Nid's Link_Output_CB callback with Buf

private

   subtype Netif_Name_Range is Integer range 1 .. 2;
   type Netif_Name is array (Netif_Name_Range) of Character;

   procedure Allocate_Netif (Nid : out AIP.EID);

   pragma Export (C, Allocate_Netif, "AIP_allocate_netif");
   --  Allocate a new netif Id. Return IF_NOID if none is available

   function Get_Netif (Nid : Netif_Id) return System.Address;
   pragma Export (C, Get_Netif, "AIP_get_netif");
   --  Return pointer to Netif record for the given netif

end AIP.NIF;
