------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Callback oriented low level access to the UDP services.

with System;

with AIP.Callbacks;
with AIP.Buffers;
with AIP.NIF;
with AIP.IPaddrs;
with AIP.PCBs;

--# inherit System, AIP, AIP.Config, AIP.Callbacks, AIP.Buffers, AIP.PCBs,
--#         AIP.NIF, AIP.IP, AIP.IPaddrs, AIP.ICMP, AIP.ICMPH,
--#         AIP.Checksum, AIP.Inet, AIP.IPH, AIP.UDPH;

package AIP.UDP
   --# own State;
is

   --------------------
   -- User interface --
   --------------------

   procedure UDP_Init;
   --# global out State;
   --  Initialize internal datastructures. To be called once, before any of
   --  the other subprograms.

   procedure UDP_New (Id : out PCBs.PCB_Id);
   --# global in out State;
   --  Allocate and return Id of a new UDP PCB. PCB_NOID on failure.

   procedure UDP_Bind
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : PCBs.Port_T;
      Err        : out AIP.Err_T);
   --# global in out State;
   --  Bind PCB to a Local_IP address and Local_Port, after which datagrams
   --  received for this endpoint might be delivered to PCB and trigger an
   --  UDP_RECV event/callback. If Local_IP is IP_ADDR_ANY, the endpoint
   --  serves the port on all the active network interfaces. Local_Port might
   --  be NOPORT, in which case an arbitrary available one is picked.
   --
   --  ERR_USE if another PCB is already bound to this local endpoint and
   --          we are configured not to accept that.
   --  ERR_MEM if Local_Port is NOPORT and no available port could be found.

   procedure UDP_Connect
     (PCB         : PCBs.PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : PCBs.Port_T;
      Err         : out AIP.Err_T);
   --# global in out State;
   --  Register Remote_IP/Remote_Port as the destination endpoint for
   --  datagrams sent later with UDP_Send on this PCB. Until disconnected,
   --  packets from this endpoint only are processed by PCB. A forced local
   --  binding is attempted if none was established beforehand. No network
   --  trafic gets generated.
   --
   --  ERR_USE if a forced binding is attempted and no port is available.

   procedure UDP_Send
     (PCB : PCBs.PCB_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T);
   --# global in out Buffers.State, State;
   --  Send BUF data to the current destination endpoint of PCB, as
   --  established by UDP_Connect. Force a local binding on PCB if none is
   --  setup already. BUF is not deallocated and its payload pointer is
   --  preserved. However, the room available in front of the payload might
   --  be clobbered for protocol headers if it is wide enough.
   --
   --  ERR_USE if PCB isn't connected to a well defined dest endpoint
   --  ERR_RTE if no route to remote IP could be found
   --  ERR_MEM e.g.if the UDP header couldn't be allocated or an error
   --          occurred while resetting BUF's payload to its value on entry
   --  Possibly other errors from lower layers.

   procedure UDP_Disconnect (PCB : PCBs.PCB_Id);
   --# global in out State;
   --  Disconnect PCB from its current destination endpoint, which leaves
   --  it open to its initial binding again.

   procedure UDP_Release (PCB : PCBs.PCB_Id);
   --# global in out State;
   --  Release PCB, to become available for Udb_New again

   ------------------------------
   -- Event/callback interface --
   ------------------------------

   --  Event kinds and descriptor used to communicate with the
   --  applicative handler (UDP_Event).

   type UDP_Event_Kind is
     (UDP_RECV   -- UDP Datagram received
     );

   type UDP_Event_T is record
      Kind : UDP_Event_Kind;
      Buf  : Buffers.Buffer_Id;
      IP   : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
   end record;

   --  UDP_RECV triggers when a datagram is received for a destination port
   --  to which we have a bound PCB. One which in addition is UDP_Connect'ed
   --  to the datagram origin endpoint gets preference.
   --
   --  .Buf is the datagram packet buffer
   --  .IP/.Port is the datagram origin endpoint (remote source)

   procedure UDP_Callback
     (Evk : UDP_Event_Kind; PCB : PCBs.PCB_Id; Cbid : Callbacks.CBK_Id);
   --# global in out State;
   --  Register that ID should be passed back to the user defined
   --  UDP_Event hook when an event of kind EVK triggers for PCB.

   procedure UDP_Set_Udata (PCB : PCBs.PCB_Id; Udata : System.Address);
   --# global in out State;
   --  Attach application level UDATA to PCB for later retrieval
   --  on UDP_Event calls.

   function UDP_Udata (PCB : PCBs.PCB_Id) return System.Address;
   --# global in State;
   --  Retrieve Udata previously attached to PCB, System.Null_Address if none.

   procedure UDP_Event
     (Ev : UDP_Event_T; PCB : PCBs.PCB_Id; Cbid : Callbacks.CBK_Id);
   --# global in out Buffers.State; in out State;
   pragma Import (Ada, UDP_Event, "AIP_udp_event");
   --  Process UDP event EV, aimed at bound PCB, for which Cbid was
   --  registered. Expected to be provided by the applicative code.

   -----------------------
   -- IPstack interface --
   -----------------------

   procedure UDP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);
   --# global in out Buffers.State; in out State;
   --  Hook for IP.  Dispatches a UDP datagram in BUF to the user callback
   --  registered for the destination port, if any. Discards the datagram
   --  (free BUF) otherwise.

   UDP_HLEN : constant := 8;

private

   type UDP_PCB is record
      RECV_Cb     : Callbacks.CBK_Id;
      --  Callback id for UDP_RECV events
   end record;

   UDP_PCB_Initializer : constant UDP_PCB :=
                           UDP_PCB'(RECV_Cb => Callbacks.NOCB);

   --------------------------
   -- Internal subprograms --
   --------------------------

   --  All declared here because SPARK forbids forward declarations in package
   --  bodies.

   procedure PCB_Clear (PCB : PCBs.PCB_Id);
   --# global in out State;
   --  Reset/Initialize PCB fields for fresh (re)use

   procedure PCB_Unlink (PCB : PCBs.PCB_Id);
   --# global in out State;
   --  Unlink PCB from the list of bound PCBs if it is there

   procedure PCB_Force_Bind (PCB : PCBs.PCB_Id; Err : out AIP.Err_T);
   --# global in out State;
   --  Force a local binding on PCB if it isn't bound already.
   --
   --  ERR as UDP_Bind.

   ------------------------
   -- UDP_Bind internals --
   ------------------------

   function PCB_Bound_To (Port : PCBs.Port_T) return AIP.EID;
   --# global in State;
   --  From the list of bound PCBs, first one bound to the indicated local port
   --  or NOPCB if none is found.
   --  Binding IP address ignored???

   function Available_Port return PCBs.Port_T;
   --# global in State;
   --  Arbitrary local Port number to which no PCB is currently bound.
   --  NOPORT if no such port is available.

   -------------------------
   -- UDP_Input internals --
   -------------------------

   procedure IP_To_UDP
     (Buf  : Buffers.Buffer_Id;
      Uhdr : out System.Address;
      Err  : out AIP.Err_T);
   --# global in out Buffers.State;
   --  Get Uhdr to designate the UDP header of a datagram received from IP in
   --  BUF, and adjust BUF's payload accordingly.
   --
   --  ERR_MEM if BUF is found too short to possibly carry a UDP datagram.

   function UDP_PCB_For
     (Ihdr  : System.Address;
      Uhdr  : System.Address) return AIP.EID;
   --# global in State;
   --  Search bound PCBs for one taker of a datagram with IP header Ihdr and
   --  UDP header Uhdr.

   ------------------------
   -- UDP_Send internals --
   ------------------------

   procedure Prepend_UDP_Header
     (Buf  : Buffers.Buffer_Id;
      Ubuf : out Buffers.Buffer_Id;
      Err  : out AIP.Err_T);
   --# global in out Buffers.State;
   --  Setup space for a UDP header before the data in Buf. See if there is
   --  enough room preallocated for this purpose, and adjust the payload
   --  pointer in this case. Prepend a separate buffer otherwise.
   --
   --  ERR_MEM if the operation failed. BUF is unchanged in this case.

   procedure UDP_Send_To_If
     (PCB      : PCBs.PCB_Id;
      Buf      : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      NH_IP    : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;
      Netif    : NIF.Netif_Id;
      Err      : out AIP.Err_T);
   --# global in out Buffers.State, State;
   --  Send BUF to DST_IP/DST_PORT via next hop NH_IP through NETIF, acting
   --  for PCB. This involves prepending a UDP header in front of BUF.
   --
   --  ERR_VAL if PCB has a specific local IP set which differs from NETIF's.

end AIP.UDP;
