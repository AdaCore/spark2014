------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Callback oriented low level access to the UDP services. At this point,
--  this is a binding to the C implementation of LWIP.

with AIP.Callbacks, AIP.IP, AIP.IPaddrs, AIP.Buffers, AIP.NIF;
--# inherit AIP.Callbacks, AIP.IPaddrs, AIP.Buffers, AIP.NIF,
--#         AIP.IPH, AIP.UDPH;

package AIP.UDP is

   --  UDP connections materialize through "UDP Protocol Control Block"
   --  entities:

   MAX_UDP_PCB : constant := 20;
   subtype PCB_Id is AIP.EID range 1 .. MAX_UDP_PCB;

   subtype Port_T is M16_T;
   NOPORT : constant Port_T := 0;

   UDP_FLAGS_CONNECTED : constant := 16#04#;

   --------------------
   -- User interface --
   --------------------

   procedure UDP_New (Id : out PCB_Id);
   --  Allocate and return Id of a new UDP PCB

   procedure UDP_Bind
     (Pcb : PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T;
      Err  : out AIP.Err_T);
   --  Bind PCB to a Local_IP address and Local_Port. Datagrams received for
   --  this endpoint trigger an UDP_RECV event, hence a call to the associated
   --  callback is any. If Local_IP is IP_ADDR_ANY, the endpoint serves the
   --  port on all the active interfaces.

   procedure UDP_Connect
     (Pcb  : PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      Err  : out AIP.Err_T);
   --  Connect PCB to the Remote_IP/Remote_Port destination endpoint for
   --  datagrams sent later with Udp_Send. Until disconnected, packets from
   --  this endpoint only are processed by PCB. This subprogram doesn't
   --  generate any network trafic.

   procedure UDP_Send
     (Pcb : PCB_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T);
   --  Send data in BUF to the current destination endpoint of PCB, as
   --  established by UDP_Connect. BUF is not deallocated.

   procedure UDP_Disconnect (Pcb : PCB_Id);
   --  Disconnect PCB from its current destination endpoint, which leaves
   --  it open to its initial binding again.

   procedure UDP_Release (Pcb : PCB_Id);
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
      Port : Port_T;
   end record;

   --  UDP_RECV triggers when a datagram is received for a destination port
   --  to which we have a bound PCB. One which in addition is UDP_Connect'ed
   --  to the datagram origin endpoint gets preference.
   --
   --  .Buf is the datagram packet buffer
   --  IP/Port is the datagram origin endpoint

   procedure UDP_Callback
     (Evk : UDP_Event_Kind; Pcb : PCB_Id; Cbid : Callbacks.Callback_Id);
   --  Register that ID should be passed back to the user defined
   --  UDP_Event hook when an event of kind EVK triggers for PCB.

   procedure UDP_Set_Udata (Pcb : PCB_Id; Udata : AIP.IPTR_T);
   --  Attach application level UDATA to PCB for later retrieval
   --  on UDP_Event calls.

   function UDP_Udata (Pcb : PCB_Id) return AIP.IPTR_T;
   --  Retrieve UDATA from PCB

   procedure UDP_Event
     (Ev : UDP_Event_T; Pcb : PCB_Id; Cbid : Callbacks.Callback_Id);
   --  Process UDP event EV, aimed at bound PCB, for which Cbid was
   --  registered. Expected to be provided by the applicative code.

   pragma Import (Ada, UDP_Event, "aip_udp_event");

   -----------------------
   -- IPstack interface --
   -----------------------

   procedure UDP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id);
   --  Hook for IP.  Dispatches a UDP datagram in BUF to the user callback
   --  registered for the destination port, if any. Discards the datagram
   --  otherwise.

   UDP_HLEN : constant := 8;

private

   type UDP_PCB is record
      IPCB : IP.IP_PCB;
      Flags  : AIP.M8_T;
      Remote_Port, Local_Port : Port_T;
      Udata  : AIP.IPTR_T;
      --
      RECV_Cb : Callbacks.Callback_Id;
      --
      Link : AIP.EID;
   end record;

   PCB_NOID : constant AIP.EID := -1;
   --  Invalid value for PCB_Id, typically used used to indicate
   --  absence of match in PCB searches. This is also used in PCB.Link
   --  to indicate end-of-list for a PCB chained in a list, or mere use
   --  of the PCB otherwise (in-use though currently not in a list).

   PCB_NOUSE : constant AIP.EID := -1;
   --  Invalid value for PCB_Id, used in PCB.Link to indicate that the
   --  PCB is currently unused, IOW free for UDP_New.

   --------------------------
   -- Internal subprograms --
   --------------------------

   --  All declared here because SPARK forbids forward declarations
   --  in package bodies.

   procedure Init_PCBs;
   --  Initialize static pool of UDP PCBs

   procedure PCB_Allocate (Id : out AIP.EID);
   --  Find one PCB free for use from the static pool and mark it in-use

   procedure PCB_Unlink (Pcb : PCB_Id);
   --  Unlink PCB from the list of bound PCBs if it is there

   procedure PCB_Force_Bind (Pcb : PCB_Id; Err : out Err_T);
   --  Force a local binding on PCB if it isn't bound already

   ------------------------
   -- UDP_Bind internals --
   ------------------------

   function PCB_Binding_Matches
     (Pcb  : UDP_PCB;
      IP   : AIP.IPaddrs.IPaddr;
      Port : Port_T) return Boolean;
   --  Whether PCB's local IP/port binding matches the provided
   --  IP/PORT pair.

   function PCB_Bound_To (Port : Port_T) return AIP.EID;
   --  From the list of bound PCBs, first one bound to local PORT
   --  PCB_NOID if none is found.

   function Available_Port return Port_T;
   --  Arbitrary local Port number to which no PCB is currently bound.
   --  PCB_NOID if no such port is available.

   -------------------------
   -- UDP_Input internals --
   -------------------------

   procedure IP_To_UDP
     (Buf  : Buffers.Buffer_Id;
      Uhdr : out AIP.IPTR_T;
      Err  : out Err_T);
   --  Get Uhdr to designate the UDP header of a datagram received
   --  from IP in BUF, and adjust BUF's payload accordingly.
   --  ERR_MEM if BUF is found too short to possibly carry a UDP datagram.

   function UDP_PCB_For
     (Ihdr, Uhdr : AIP.IPTR_T; Netif : NIF.Netif_Id) return AIP.EID;
   --  Search bound PCBs for one taker of a datagram with IP header
   --  IHDR and UDP header Uhdr arrived on NETIF.

   ------------------------
   -- UDP_Send internals --
   ------------------------

   procedure Prepend_UDP_Header
     (Buf  : Buffers.Buffer_Id;
      Ubuf : out Buffers.Buffer_Id;
      Err  : out AIP.Err_T);
   --  Setup space for a UDP header before the data in BUF. See if there
   --  is enough room preallocated for this purpose, and adjust the payload
   --  pointer in this case. Prepend a separate buffer otherwise.
   --  ERR_MEM if the operation failed. BUF is unchanged in this case.

   procedure UDP_Send_To_If
     (Pcb   : PCB_Id;
      Buf   : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      Dst_Port : Port_T;
      Netif : AIP.NIF.Netif_Id;
      Err   : out AIP.Err_T);
   --  Send BUF to DST_IP/DST_PORT through NETIF, acting for PCB.
   --  ERR_VAL if PCB has a specific local IP set which differs from
   --  NETIF's IP.

end AIP.UDP;
