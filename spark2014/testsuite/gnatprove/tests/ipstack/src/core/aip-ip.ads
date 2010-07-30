------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP layer

with AIP.IPaddrs, AIP.NIF, AIP.Buffers;

--# inherit AIP.IPaddrs, AIP.NIF, AIP.Buffers,
--#         System, AIP.Checksum, AIP.Config, AIP.IPH, AIP.ICMPH;

package AIP.IP
--# own State;
--# initializes State;
is

   procedure Set_Default_Router (IPA : IPaddrs.IPaddr);
   --# global in out State;
   --  Set the default route to the given value

   --  IP_PCB is the common part of the PCB for all IP-based protocols

   type IP_PCB is record
      Local_IP  : IPaddrs.IPaddr;
      Remote_IP : IPaddrs.IPaddr;

      SOO : AIP.U16_T;
      --  Socket options
      --  Should use boolean components instead???

      TOS : AIP.U8_T;
      --  Type Of Service

      TTL : AIP.U8_T;
      --  Time To Live
   end record;

   IP_PCB_Initializer : constant IP_PCB
     := IP_PCB'(Local_IP  => IPaddrs.IP_ADDR_ANY,
                Remote_IP => IPaddrs.IP_ADDR_ANY,
                SOO       => 0,
                TOS       => 0,
                TTL       => 0);

   procedure IP_Route
     (Dst_IP   : IPaddrs.IPaddr;
      Next_Hop : out IPaddrs.IPaddr;
      Netif    : out AIP.EID);
   --# global in State;
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

private

   procedure IP_Forward (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);
   --# global in out Buffers.State;
   --  Decrement TTL and forward packet to next hop

end AIP.IP;
