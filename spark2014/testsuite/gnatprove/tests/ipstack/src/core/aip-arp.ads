------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  RFC826 - Address Resolution Protocol

with AIP.Time_Types;

with AIP.Buffers;
with AIP.IPaddrs;
with AIP.NIF;

package AIP.ARP is

   procedure ARP_Initialize;
   --  Initialize ARP subsystem and empty ARP table

private

   Max_ARP_Entries : constant := 20;
   subtype Any_ARP_Entry_Id is EID range 0 .. Max_ARP_Entries;
   --  Make upper bound configurable???
   No_ARP_Entry : constant Any_ARP_Entry_Id := Any_ARP_Entry_Id'First;
   subtype ARP_Entry_Id is Any_ARP_Entry_Id range 1 .. Any_ARP_Entry_Id'Last;

   type ARP_Entry_State is (Unused, Incomplete, Active);

   type ARP_Entry is record
      State           : ARP_Entry_State := Unused;
      Permanent       : Boolean         := False;
      --  Publish         : Boolean         := False;
      Timestamp       : Time_Types.Time;

      Dst_IP_Address  : IPaddrs.IPaddr;
      Dst_MAC_Address : Ethernet_Address;

      Prev, Next      : Any_ARP_Entry_Id;
   end record;

   procedure ARP_Input
     (Nid           : NIF.Netif_Id;
      Netif_Address : IPTR_T;
      Buf           : Buffers.Buffer_Id);
   pragma Export (C, ARP_Input, "AIP_arp_input");
   --  Process ARP packet in Buf received on interface Nid. Netif_Address is
   --  Nid's hardware address.

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id);
   pragma Export (C, IP_Input, "AIP_arpip_input");
   --  Process IP packet in Buf received on Nid

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr);
   pragma Export (C, ARP_Output, "AIP_arp_output");
   --  Send packet in Buf to Dst_Address through Nid

   ------------------------------------
   -- Low-level ARP table management --
   ------------------------------------

   procedure ARP_Reset (AE : in out ARP_Entry);
   --  Clear all information in AE and reset it to Incomplete state

   procedure ARP_Find
     (Addr : IPaddrs.IPaddr;
      Id   : out Any_ARP_Entry_Id);
   --  Find existing entry for Addr, or allocate a new one if not found.
   --  Note: May recycle old non-permanent entries.
   --  Id is No_ARP_Entry on return if no storage is available for the
   --  requested allocation.

   procedure ARP_Prepend
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id);
   --  Prepend AEID to List

   procedure ARP_Unlink
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id);
   --  Remove AEID from list

end AIP.ARP;
