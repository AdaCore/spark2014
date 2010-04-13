------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Low level access to the TCP services. At this point, this is a binding to
--  the C implementation of LWIP services.

with AIP.Callbacks, AIP.IPaddrs;
--# inherit AIP.Callbacks, AIP.IPaddrs, AIP.Config;

package AIP.TCP is

   --  TCP connections materialize through "TCP Control Block" entities:

   subtype TCB_Id is AIP.IPTR_T;
   NOTCB : constant TCB_Id := AIP.NULIPTR;

   ------------------------------
   -- Preparing callback calls --
   ------------------------------

   procedure Tcp_Arg (Pcb : TCB_Id; Arg : AIP.IPTR_T);
   pragma Import (C, Tcp_Arg, "tcp_arg");
   --  Setup to pass ARG on every callback call for PCB.

   --------------------------------
   -- Setting up TCP connections --
   --------------------------------

   function Tcp_New return TCB_Id;
   pragma Import (C, Tcp_New, "tcp_new");
   --  Allocate a new TCP PCB and return the corresponding id, or NOTCB on
   --  allocation failure.

   function Tcp_Bind
     (Pcb : TCB_Id;
      Addr : IPaddrs.IPaddr_Id;
      Port : AIP.U16_T) return AIP.Err_T;
   pragma Import (C, Tcp_Bind, "tcp_bind");
   --  Bind PCB to the provided IP ADDRess (possibly IP_ADDR_ANY) and
   --  local PORT number. Return ERR_USE if the requested binding is already
   --  established for another PCB, NOERR otherwise.

   function Tcp_Listen
     (Pcb : TCB_Id) return TCB_Id;
   --  Setup PCB to listen for at most Config.TCP_DEFAULT_LISTEN_BACKLOG
   --  simultaneous connection requests and trigger the acceptation callback
   --  on such events. Unless not enough memory is available, return id of a
   --  new PCB to be used for further operations and release the provided
   --  one. If allocation is not possible, just return NULID.

   function Tcp_Listen_BL
     (Pcb : TCB_Id;
      Blog : AIP.U8_T) return TCB_Id;
   pragma Import (C, Tcp_Listen_BL, "tcp_listen_with_backlog");
   --  Same as Tcp_Listen for a user specified backlog size.

   subtype Accept_Cb_Id is Callbacks.Callback_Id;
   procedure Tcp_Accept
     (Pcb : TCB_Id;
      Cb  : Accept_Cb_Id);
   pragma Import (C, Tcp_Accept, "tcp_accept");
   --  Request CB to be called when a connection request comes in on PCB.
   --  CB's signature is expected to be:
   --
   --    function Tcp_Accept_Cb
   --      (Arg : AIP.IPTR_T; Tcb : AIP.TCP.TCB_Id; Err : AIP.Err_T)
   --    return AIP.Err_T
   --
   --  TCB is the new pcb allocated for the established connection and ERR is
   --  expected to be NOERR.
   --
   --  The callback typically allocates an application state block, then calls
   --  Tcp_Accepted and returns NOERR if all went well. If anything goes
   --  wrong, the callback returns the appropriate error code and AIP aborts
   --  the connection.

   procedure Tcp_Accepted (Pcb : TCB_Id);
   pragma Import (C, Tcp_Accepted, "tcp_accepted_w");
   --  Inform the AIP stack that a connection has just been accepted on PCB.
   --  To be called by the acceptation callback for proper management of the
   --  listening backlog.

   subtype Connect_Cb_Id is Callbacks.Callback_Id;
   function Tcp_Connect
     (Pcb : TCB_Id;
      Addr : IPaddrs.IPaddr_Id;
      Port : AIP.U16_T;
      Cb : Connect_Cb_Id) return AIP.Err_T;
   pragma Import (C, Tcp_Connect, "tcp_connect");
   --  Setup PCB to connect to the remote ADDR/PORT and send the initial SYN
   --  segment.  Do not wait for the connection to be entirely setup, but
   --  instead arrange to have CB called when the connection is established or
   --  rejected, as indicated by the ERR argument. This function returns
   --  ERR_MEM if no memory is available for enqueueing the SYN segment, or
   --  NOERR otherwise.

   ----------------------
   -- Sending TCP data --
   ----------------------

   --  TCP data is sent by enqueueing with calls to Tcp_Write, and a provided
   --  callback is called when the data has been acknowledged by the remote
   --  host. Care must be taken to respect transmission capacities.

   function Tcp_Write
     (Pcb : TCB_Id;
      Data : AIP.IPTR_T;
      Len : AIP.U16_T;
      Flags : AIP.U8_T) return AIP.Err_T;
   pragma Import (C, Tcp_Write, "tcp_write");
   --  Enqueue DATA/LEN for output through PCB. Flags is a combination of the
   --  TCP_WRITE constants below. If all goes well, this function returns
   --  NOERR. This function will fail and return ERR_MEM if the length of the
   --  data exceeds the current send buffer size (as advertised by Tcp_Sndbuf)
   --  or if the length of the outgoing segments queue is larger than the
   --  configured upper limit. On ERR_MEM, the application should wait until
   --  some of the currently enqueued data has been successfully received by
   --  the other host and try again.

   TCP_WRITE_NOFLAG : constant := 16#00#;
   TCP_WRITE_COPY : constant := 16#01#;  --  Copy data into ipstack memory
   TCP_WRITE_MORE : constant := 16#02#;  --  Set PSH on last segment sent

   function Tcp_Sndbuf (Pcb : TCB_Id) return AIP.U16_T;
   pragma Import (C, Tcp_Sndbuf, "tcp_sndbuf_w");
   --  Room available for output data queuing.

   subtype Sent_Cb_Id is Callbacks.Callback_Id;
   procedure Tcp_Sent
     (Pcb : TCB_Id;
      Cb  : Sent_Cb_Id);
   pragma Import (C, Tcp_Sent, "tcp_sent");
   --  Request that CB is called when sent data has been acknowledged by
   --  the remote host on PCB. CB's signature is expected to be:
   --
   --    function Tcp_Sent_Cb
   --      (Arg : AIP.IPTR_T;
   --       Tcb : AIP.TCP.TCB_Id;
   --       Len : AIP.U16_T) return AIP.Err_T
   --
   --  ARG and TCB are the usual app/user arg and connection control block.
   --  LEN is the amount data just acknowledged by the remote peer. NOERR is
   --  expected on return.

   ------------------------
   -- Receiving TCP data --
   ------------------------

   --  Data reception is callback based, as everything else.

   subtype Recv_Cb_Id is Callbacks.Callback_Id;
   procedure Tcp_Recv
     (Pcb : TCB_Id;
      Cb  : Recv_Cb_Id);
   pragma Import (C, Tcp_Recv, "tcp_recv");
   --  Request that CB is called when new data or a close-connection request
   --  arrives on PCB. CB's profile is expected to be;
   --
   --    function Echo_Recv_Cb
   --      (Arg : AIP.IPTR_T;
   --       Tcb : AIP.TCP.TCB_Id;
   --       Pbu : AIP.Pbufs.Pbuf_Id;
   --       Err : AIP.Err_T) return AIP.Err_T;
   --
   --  ARG and TCB are the usual app/user arg and connection control block.
   --  PBU designates the packet buffer where the received data resides, or is
   --  NOPBUF for a close-connection request.
   --
   --  When all goes well, NOERR is expected on return, and the packet buffer
   --  should be Pbuf_Free'd by the callback if it isn't needed by the app any
   --  more. Otherwise, the callback should leave PBU untouched and return a
   --  descriptive error code.

   procedure Tcp_Recved
     (Pcb : TCB_Id;
      Len : AIP.U16_T);
   pragma Import (C, Tcp_Recved, "tcp_recved");
   --  Inform AIP that LEN bytes of data have been processed and can be
   --  acknowledged.

   -------------
   -- Polling --
   -------------

   --  AIP periodically polls idle connections by calling a callback provided
   --  for this purpose. This can be used to timeout idle connections or as an
   --  opportunity to retry failed Tcp_Write attempts.

   subtype Poll_Cb_Id is Callbacks.Callback_Id;
   procedure Tcp_Poll
     (Pcb : TCB_Id;
      Cb  : Poll_Cb_Id;
      Ivl : AIP.U8_T);
   pragma Import (C, Tcp_Poll, "tcp_poll");
   --  Request CB to be called for polling purposes on PCB, every IVL ticks
   --  (where "tick" is a coarse grain TCP timer click, normally triggering
   --  about twice per second). CB's profile is expected to be:
   --
   --    function Tcp_Poll_Cb
   --      (Arg : AIP.IPTR_T;
   --       Tcb : AIP.TCP.TCB_Id) return AIP.Err_T
   --
   --  ARG and TCB are the usual app/user arg and connection control block.

   ------------------------------
   --  Closing TCP connections --
   ------------------------------

   function Tcp_Close (Pcb : TCB_Id) return AIP.Err_T;
   pragma Import (C, Tcp_Close, "tcp_close");
   --  Closes the connection held by the provided PCB, which may not be
   --  referenced any more.

   procedure Tcp_Abort (Pcb : TCB_Id);
   pragma Import (C, Tcp_Abort, "tcp_abort");
   --  Aborts a connection by sending a RST to the remote host and deletes
   --  the local PCB. This is done when a connection is killed because of
   --  shortage of memory.

   subtype Err_Cb_Id is Callbacks.Callback_Id;
   procedure Tcp_Err (Pcb : TCB_Id; Cb : Err_Cb_Id);
   pragma Import (C, Tcp_Err, "tcp_err");
   --  Request CB to be called when a connection gets aborted because
   --  of some error. CB's profile is expected to be:
   --
   --    procedure Echo_Err_Cb
   --      (Arg : AIP.IPTR_T;
   --       Err : AIP.Err_T)
   --
   --  ARG is the usual user/app argument. ERR is the aborting error code.

end AIP.TCP;
