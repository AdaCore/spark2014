------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Callback oriented low level access to the UDP services. At this point,
--  this is a binding to the C implementation of LWIP.

with AIP.Callbacks, AIP.IPaddrs, AIP.Pbufs;
--# inherit AIP.Callbacks, AIP.IPaddrs, AIP.Pbufs;

package AIP.UDP is

   --  UDP connections materialize through "UDP Control Block" entities:

   subtype UCB_Id is AIP.IPTR_T;
   NOUCB : constant UCB_Id := AIP.NULIPTR;

   function Udp_New return UCB_Id;
   pragma Import (C, Udp_New, "udp_new");
   --  Allocate and return a new UCB

   subtype Recv_Cb_Id is Callbacks.Callback_Id;
   procedure Udp_Recv
     (Pcb : UCB_Id;
      Cb  : Recv_Cb_Id;
      Arg : AIP.IPTR_T);
   pragma Import (C, Udp_Recv, "udp_recv");
   --  Request that CB is called with ARG when a datagram to be processed
   --  by PCB arrives. CB's profile is expected to be:
   --
   --     procedure UDP_Recv_Cb
   --       (Arg : AIP.IPTR_T;
   --        Ucb : AIP.UDP.UCB_Id;
   --        Pbu : AIP.Pbufs.Pbuf_Id;
   --        Ipa : AIP.IPaddrs.IPaddr_Id;
   --        Pno : AIP.U16_T);
   --
   --  ARG designates the application argument block registered together with
   --  the callback. UCB is the UDP PCB which is to process the datagram. The
   --  datagram is provided in the PBU pbuf, sent from the IPA/PNO IP address
   --  / UDP port number endpoint.

   procedure Udp_Bind
     (Pcb : UCB_Id;
      Addr : IPaddrs.IPaddr_Id;
      Port : AIP.U16_T);
   pragma Import (C, Udp_Bind, "udp_bind");
   --  Bind PCB to a local IP ADDRess and PORT, after which datagrams received
   --  for this endpoint are passed to the registered reception callback. ADDR
   --  may be IP_ADDR_ANY.

   function Udp_Connect
     (Pcb : UCB_Id;
      Addr : IPaddrs.IPaddr_Id;
      Port : AIP.U16_T) return AIP.Err_T;
   pragma Import (C, Udp_Connect, "udp_connect");
   --  Connect PCB to remote IP ADDRess and PORT, destination endpoint for
   --  datagrams sent later with Udp_Send. Until disconnected, packets from
   --  this endpoint only are processed by PCB. This subprogram doesn't
   --  generate any network trafic.

   function Udp_Send (Pcb : UCB_Id; Pbu : Pbufs.Pbuf_Id) return AIP.Err_T;
   pragma Import (C, Udp_Send, "udp_send");
   --  Send data in PBU to the current destination endpoint of PCB, as
   --  established by Udp_Connect. PBU is not deallocated.

   procedure Udp_Disconnect (Pcb : UCB_Id);
   pragma Import (C, Udp_Disconnect, "udp_disconnect");
   --  Disconnect PCB from its current destination endpoint, which leaves
   --  it open to its initial binding again.

   procedure Udp_Remove (Pcb : UCB_Id);
   pragma Import (C, Udp_Remove, "udp_remove");
   --  Release PCB, to become available for Udb_New again

end AIP.UDP;
