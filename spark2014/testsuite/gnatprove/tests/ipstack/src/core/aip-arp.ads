------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2015, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  RFC826 - Address Resolution Protocol

with System;

with AIP.Buffers;
with AIP.IPaddrs;
with AIP.NIF;

with AIP.Time_Types;
use type AIP.Time_Types.Time;

package AIP.ARP with
  Abstract_State => State
is

   procedure Initialize
   --  Initialize ARP subsystem and empty ARP table
   with
     Global => (Output => State);

   procedure ARP_Timer
   --  Called periodically to expire old, unused entries
   with
     Global => (In_Out => (Buffers.State, State));

   procedure ARP_Clear
   --  Remove all non-permanent entries
   with
     Global => (In_Out => (Buffers.State, State));

private

   Max_ARP_Entries : constant := 20;
   subtype Any_ARP_Entry_Id is AIP.EID range 0 .. Max_ARP_Entries;
   --  Make upper bound configurable???
   No_ARP_Entry : constant Any_ARP_Entry_Id := Any_ARP_Entry_Id'First;
   subtype ARP_Entry_Id is Any_ARP_Entry_Id range 1 .. Any_ARP_Entry_Id'Last;

   type ARP_Entry_State is (Unused, Incomplete, Active);

   Max_ARP_Age_Active     : constant := 600;
   Max_ARP_Age_Incomplete : constant := 10;
   --  Maximum age or ARP entries, in seconds
   --  Make these configurable???

   type ARP_Entry is record
      State           : ARP_Entry_State;
      Permanent       : Boolean;

      Timestamp       : Time_Types.Time;

      Dst_IP_Address  : IPaddrs.IPaddr;
      Dst_MAC_Address : AIP.Ethernet_Address;

      Packet_Queue    : Buffers.Packet_Queue;
      --  For incomplete entries, chained list of pending packets to be sent
      --  once ARP lookup is completed.

      Next            : Any_ARP_Entry_Id;
   end record;

   procedure ARP_Input
     (Nid                : NIF.Netif_Id;
      Netif_MAC_Addr_Ptr : System.Address;
      Buf                : Buffers.Buffer_Id)
   --  Process ARP packet in Buf received on interface Nid. Netif_MAC_Addr_Ptr
   --  designates Nid's hardware address.
   with
     Global => (In_Out => (Buffers.State, State));
   pragma Export (C, ARP_Input, "AIP_arp_input");

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id);
   pragma Export (C, IP_Input, "AIP_arpip_input");
   --  Process IP packet in Buf received on Nid

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr)
   --  Send packet in Buf to Dst_Address through Nid
   with
     Global => (In_Out => (Buffers.State, State));
   pragma Export (C, ARP_Output, "AIP_arp_output");

   ------------------------------------
   -- Low-level ARP table management --
   ------------------------------------

   procedure ARP_Reset (AE : in out ARP_Entry);
   --  Clear all information in AE and reset it to Incomplete state

   procedure ARP_Find
     (Addr     : IPaddrs.IPaddr;
      Id       : out Any_ARP_Entry_Id;
      Allocate : Boolean)
   --  Find existing entry for Addr, or allocate a new one if not found and
   --  Allocate is True.
   --  Note: May recycle old non-permanent entries.
   --  Id is No_ARP_Entry on return if no storage is available for the
   --  requested allocation.
   with
     Global => (In_Out => State);

   procedure ARP_Update
     (Nid         : NIF.Netif_Id;
      Eth_Address : AIP.Ethernet_Address;
      IP_Address  : IPaddrs.IPaddr;
      Allocate    : Boolean;
      Err         : out AIP.Err_T)
   --  Update entry for the given (Eth_Address, IP_Address) couple seen on Nid.
   --  If Allocate is True, create new entry if none exists.
   with
     Global => (In_Out => (Buffers.State, State));

   procedure ARP_Prepend
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   --  Prepend AEID to List
   with
     Global => (In_Out => State);

   procedure ARP_Unlink
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   --  Remove AEID from list
   with
     Global => (In_Out => State);

   procedure Send_Request
     (Nid            : NIF.Netif_Id;
      Dst_IP_Address : IPaddrs.IPaddr)
   --  Send ARP request for Dst_IP_Address on Nid
   with
     Global => (In_Out => Buffers.State);

   procedure Send_Packet
     (Nid             : NIF.Netif_Id;
      Frame_Type      : AIP.U16_T;
      Buf             : Buffers.Buffer_Id;
      Dst_MAC_Address : AIP.Ethernet_Address)
   --  Send payload Buf to Dst_MAC_Address on Nid, as the payload of a frame
   --  with the given Frame_Type.
   with
     Global => (In_Out => Buffers.State);

   -----------------------
   -- Utility functions --
   -----------------------

   function Get_MAC_Address (Nid : NIF.Netif_Id) return AIP.Ethernet_Address;
   --  Return Nid's MAC address, assuming it is an Ethernet address

end AIP.ARP;
