------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  IP layer

with System;

with AIP.IPaddrs, AIP.NIF, AIP.Buffers;
limited with AIP.UDP, AIP.TCP;

package AIP.IP with
  Abstract_State => (FIB, State),
  Initializes    => (FIB, State)
is

   procedure Set_Default_Router (IPA : IPaddrs.IPaddr)
   --  Set the default route to the given value
   with
     Global => (Output => FIB);

   procedure IP_Route
     (Dst_IP   : IPaddrs.IPaddr;
      Next_Hop : out IPaddrs.IPaddr;
      Netif    : out AIP.EID)
   --  Find next hop IP address and outbound interface for Dst_IP
   with
     Global => (Input  => FIB);

   procedure IP_Input (Netif : NIF.Netif_Id; Buf : Buffers.Buffer_Id) with
     Global => (Input  => (UDP.State, FIB),
                In_Out => (Buffers.State, TCP.State, State));
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
      Err    : out AIP.Err_T)
   --  Output IP datagram
   with
     Global => (In_Out => (Buffers.State, State));

   procedure Get_Next_Header
     (Buf  : Buffers.Buffer_Id;
      Nlen : AIP.U16_T;
      Nhdr : out System.Address;
      Err  : out AIP.Err_T)
   --  Given an IP buffer, verify that at least Nlen bytes of data are present
   --  in the payload (accomodating data for the next-level protocol header).
   --  If so, move Buf's payload pointer to the start of the next header, and
   --  return it in Nhdr, else set Err.
   with
     Global => (In_Out => Buffers.State);

private

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --  Decrement TTL and forward packet to next hop
   with
     Global => (In_Out => Buffers.State);

end AIP.IP;
