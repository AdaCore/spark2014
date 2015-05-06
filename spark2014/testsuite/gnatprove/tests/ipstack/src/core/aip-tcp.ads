------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Callback oriented low level access to the TCP services. At this point,
--  this is a binding to the C implementation of LWIP.

with System;

limited with AIP.IP;

with AIP.Buffers;
with AIP.Callbacks;
with AIP.IPaddrs;
with AIP.NIF;
with AIP.PCBs;

package AIP.TCP with
  Abstract_State => State
is

   --------------------
   -- User interface --
   --------------------

   procedure TCP_Init
   --  Initialize internal datastructures. To be called once, before any of
   --  the other subprograms.
   with Global => (Output => State);

   -------------------------
   -- Callbacks interface --
   -------------------------

   type TCP_Event_Kind is
     (TCP_EVENT_ACCEPT,
      TCP_EVENT_CONNECT,
      TCP_EVENT_SENT,
      TCP_EVENT_RECV,
      TCP_EVENT_POLL,
      TCP_EVENT_ABORT);

   type TCP_Event_T is record
      Kind : TCP_Event_Kind;

      Len : AIP.M32_T;
      --  Data length sent and acked (for SENT)

      Buf : Buffers.Buffer_Id;
      --  Data buffer (for RECV)

      Addr : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
      --  Remote socket (for ACCEPT)

      Err : AIP.Err_T;
      --  Reason of abort (for ABORT)
   end record;

   procedure TCP_Event
     (Ev   : TCP_Event_T;
      PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id;
      Err  : out AIP.Err_T)
   --  Process TCP event EV, aimed at bound PCB, for which Cbid was registered.
   --  Expected to be provided by the applicative code.
   with
     Global => (In_Out => Buffers.State);
   pragma Import (Ada, TCP_Event, "AIP_tcp_event");
   pragma Weak_External (TCP_Event);

   procedure TCP_Set_Udata (PCB : PCBs.PCB_Id; Udata : System.Address)
   --  Attach Udata to PCB, for later retrieval on event callbacks
   with
     Global => (In_Out => State);

   function TCP_Udata (PCB : PCBs.PCB_Id) return System.Address
   --  Retrieve callback Udata attached to PCB
   with
     Global => State;

   --------------------------------
   -- Setting up TCP connections --
   --------------------------------

   procedure TCP_New (PCB : out PCBs.PCB_Id)
   --  Allocate a new TCP PCB and return the corresponding id, or NOPCB on
   --  allocation failure.
   with
     Global => (In_Out => State);

   procedure TCP_Bind
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : AIP.U16_T;
      Err        : out AIP.Err_T)
   --  Bind PCB to the provided IP address (possibly IP_ADDR_ANY) and
   --  local PORT number. Return ERR_USE if the requested binding is already
   --  established for another PCB, NOERR otherwise.
   with
     Global => (In_Out => State);

   procedure TCP_Listen (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
   --  Setup PCB to listen for at most Config.TCP_DEFAULT_LISTEN_BACKLOG
   --  simultaneous connection requests and trigger the acceptation callback
   --  on such events.
   with
     Global => (In_Out => State);

   procedure TCP_Listen_BL
     (PCB     : PCBs.PCB_Id;
      Backlog : Natural;
      Err     : out AIP.Err_T)
   --  Same as TCP_Listen but with a user-specified backlog size
   with
     Global => (In_Out => State);

   procedure On_TCP_Accept
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --  Register CB as the id to pass TCP_Event on TCP_EVENT_ACCEPT for PCB.
   --
   --  TCP_EVENT_ACCEPT triggers when a connection request comes in.
   --
   --  Ev.PCB is the new pcb allocated for the established connection
   --  Ev.Addr/Port designate the connection request origin
   --
   --  The callback typically allocates an application state block, then calls
   --  TCP_Accepted and returns NOERR if all went well. If anything goes
   --  wrong, the callback returns the appropriate error code and AIP aborts
   --  the connection.
   with
     Global => (In_Out => State);

   procedure TCP_Accepted (PCB : PCBs.PCB_Id)
   --  Inform the AIP stack that a connection has just been accepted on PCB.
   --  To be called by the TCP_EVENT_ACCEPT callback for proper management of
   --  the listen backlog.
   with
     Global => (In_Out => State);

   procedure TCP_Connect
     (PCB  : PCBs.PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
      Cb   : Callbacks.CBK_Id;
      Err  : out AIP.Err_T)
   --  Setup PCB to connect to the remote ADDR/PORT and send the initial SYN
   --  segment.  Do not wait for the connection to be entirely setup, but
   --  instead arrange to have CB called when the connection is established or
   --  rejected, as indicated by the ERR argument. This function returns
   --
   --  ERR_MEM if no memory is available for enqueueing the SYN segment,
   --
   --  NOERR   if all went well.
   with
     Global => (Input  => IP.FIB,
                In_Out => (Buffers.State, IP.State, State));

   ----------------------
   -- Sending TCP data --
   ----------------------

   --  TCP data is sent by enqueueing with calls to TCP_Write, and a provided
   --  callback is called when the data has been acknowledged by the remote
   --  host. Care must be taken to respect transmission capacities.

   procedure TCP_Write
     (PCB   : PCBs.PCB_Id;
      Data  : System.Address;
      Len   : AIP.M32_T;
      Copy  : Boolean;
      Push  : Boolean;
      Err   : out AIP.Err_T)
   --  Enqueue DATA/LEN for output through PCB. COPY controls whether data is
   --  copied into AIP's memory before processing, or whether it only gets
   --  referenced from there, in which case clients should not modify it until
   --  it is known to have been acknowledged by the receiver.  PUSH controls
   --  whether PSH should be sent on the last TCP segment sent.
   --
   --  ERR_MEM if the length of the data exceeds the current send buffer size
   --          (as advertised by TCP_Sndbuf) or if the length of the outgoing
   --          segments queue is larger than the configured upper limit. The
   --          application should wait until some of the currently enqueued
   --          data has been successfully received and try again.
   --
   --  ERR_USE if the TCP connection is in an inappropriate state, that is
   --          not one of Established | Close_Wait | Syn_Sent | Syn_Received.
   --
   --  NOERR   if all went well.
   with
     Global => (In_Out => (Buffers.State, IP.State, State));

   function TCP_Sndbuf (PCB : PCBs.PCB_Id) return AIP.U16_T
   --  Room available for output data queuing.
   with
     Global => State;

   procedure On_TCP_Sent
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --  Register CB as the id to pass TCP_Event on TCP_EVENT_SENT for PCB.
   --
   --  TCP_EVENT_SENT triggers when sent data has been acknowledged by
   --  the remote host on PCB.
   --
   --  Ev.Len is the amount data just acknowledged by the remote peer.
   --
   --  NOERR is expected on return.
   with
     Global => (In_Out => State);

   ------------------------
   -- Receiving TCP data --
   ------------------------

   --  Data reception is callback based, as everything else.

   procedure On_TCP_Recv
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --  Register CB as the id to pass TCP_Event on TCP_EVENT_RECV for PCB.
   --
   --  TCP_EVENT_RECV triggers when new data or a close-connection request
   --  arrives on PCB.
   --
   --  Ev.Buf designates the packet buffer where the received data resides, or
   --         is NOBUF for a close-connection request.
   --
   --  When all goes well, NOERR is expected on return, and the packet buffer
   --  should be Buffer_Free'd by the callback if it isn't needed by the app
   --  any more. Otherwise, the callback should leave Ev.Buf untouched and
   --  return a descriptive error code.
   with
     Global => (In_Out => State);

   procedure TCP_Recved
     (PCB : PCBs.PCB_Id;
      Len : AIP.U16_T)
   --  Inform AIP that LEN bytes of data have been processed and can be
   --  acknowledged.
   with
     Global => (In_Out => State);

   -------------
   -- Polling --
   -------------

   --  AIP periodically polls idle connections by calling a callback provided
   --  for this purpose. This can be used to timeout idle connections or as an
   --  opportunity to retry failed TCP_Write attempts.

   procedure On_TCP_Poll
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id;
      Ivl : AIP.U16_T)
   --  Register CB as the id to pass TCP_Event on TCP_EVENT_POLL for PCB,
   --  and request that it triggers every IVL ticks from now on.
   with
     Global => (In_Out => State);

   ------------------------------
   --  Closing TCP connections --
   ------------------------------

   procedure TCP_Close (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
   --  Closes the connection held by the provided PCB, which may not be
   --  referenced any more.
   with
     Global => (In_Out => (Buffers.State, IP.State, State));

   procedure TCP_Drop (PCB : PCBs.PCB_Id)
   --  Aborts a connection by sending a RST to the remote host and deletes
   --  the local PCB. This is done when a connection is killed because of
   --  shortage of memory.
   with
     Global => (Input  => IP.FIB,
                In_Out => (Buffers.State, IP.State, State));

   procedure On_TCP_Abort
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --  Register CB as the id to pass TCP_Event on TCP_EVENT_ABORT for PCB.
   --
   --  TCP_EVENT_ABORT triggers when a connection gets aborted because
   --  of some error.
   --
   --  Ev.Err is the aborting error code.
   with
     Global => (In_Out => State);

   -----------------------
   -- IPstack interface --
   -----------------------

   procedure TCP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --  Hook for IP.  Process a TCP segment in BUF, and dispatch the TCP payload
   --  to the appropriate user callback. Buf is then free'd.
   with
     Global => (Input  => IP.FIB,
                In_Out => (Buffers.State, IP.State, State));

   ------------
   -- Timers --
   ------------

   procedure TCP_Fast_Timer
   --  Called every TCP_FAST_INTERVAL (250 ms) and process data previously
   --  "refused" by upper layer (application) and sends delayed ACKs.
   with
     Global => (In_Out => (Buffers.State, IP.State, State));

   procedure TCP_Slow_Timer
   --  Called every 500 ms and implements the retransmission timer and the
   --  timer that removes PCBs that have been in TIME-WAIT for enough time. It
   --  also increments various timers such as the inactivity timer in each PCB.
   with
     Global => (In_Out => (Buffers.State, IP.State, State));

end AIP.TCP;
