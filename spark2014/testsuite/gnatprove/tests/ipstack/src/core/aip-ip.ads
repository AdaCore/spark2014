------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP layer

with System;

with AIP.IPaddrs, AIP.NIF, AIP.Buffers;

--# inherit System, AIP.Buffers, AIP.Checksum, AIP.Config, AIP.ICMPH,
--#         AIP.IPaddrs, AIP.IPH, AIP.NIF;

package AIP.IP
--# own State, FIB;
--# initializes State, FIB;
is

   procedure Set_Default_Router (IPA : IPaddrs.IPaddr);
   --# global out FIB;
   --  Set the default route to the given value

   procedure IP_Route
     (Dst_IP   : IPaddrs.IPaddr;
      Next_Hop : out IPaddrs.IPaddr;
      Netif    : out AIP.EID);
   --# global in FIB;
   --  Find next hop IP address and outbound interface for Dst_IP

   procedure IP_Input (Netif : NIF.Netif_Id; Buf : Buffers.Buffer_Id);
   --# global in out Buffers.State;
   pragma Export (C, IP_Input, "AIP_ip_input");

   procedure IP_Output_If
     (Buf    : Buffers.Buffer_Id;
      Src_IP : IPaddrs.IPaddr;
      Dst_IP : IPaddrs.IPaddr;
      NH_IP  : IPaddrs.IPaddr;
      TTL    : AIP.U8_T;
      TOS    : AIP.U8_T;
      Proto  : AIP.U8_T;
      Netif  : NIF.Netif_Id;
      Err    : out AIP.Err_T);
   --# global in out State, Buffers.State;
   --  Output IP datagram

   IP_HLEN : constant := 20;
   --  What if there are options???

   procedure Get_Next_Header
     (Buf  : Buffers.Buffer_Id;
      Nlen : AIP.U16_T;
      Nhdr : out System.Address;
      Err  : out AIP.Err_T);
   --# global in out Buffers.State;
   --  Given an IP buffer, verify that at least Nlen bytes of data are present
   --  in the payload (accomodating data for the next-level protocol header).
   --  If so, move Buf's payload pointer to the start of the next header, and
   --  return it in Nhdr, else set Err.

private

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);
   --# global in out Buffers.State;
   --  Decrement TTL and forward packet to next hop

end AIP.IP;
