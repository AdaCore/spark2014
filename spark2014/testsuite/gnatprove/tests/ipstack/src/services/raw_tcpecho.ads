------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  TCP echo server implementation using the RAW callback API

with AIP.TCP, AIP.Pbufs;
--# inherit AIP.Pools, AIP.Support,
--#         AIP.IPaddrs, AIP.Pbufs, AIP.Callbacks, AIP.TCP;

package RAW_Tcpecho
  --# own CB_IDENTIFIERS, ECHO_STATE_POOL;
is

   procedure Init;
   --# global out CB_IDENTIFIERS; in out ECHO_STATE_POOL;
   --  Setup server to wait for and process connections

private

   --  Callback imports/exports. See AIP.Callbacks for the rationale.

   ----------
   -- Sent --
   ----------

   procedure Echo_Sent_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Sent_Cb);

   function Echo_Sent_Cb_W
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Len : AIP.U16_T) return AIP.Err_T;
   pragma Import (C, Echo_Sent_Cb_W);

   ----------
   -- Poll --
   ----------

   procedure Echo_Poll_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Err : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Poll_Cb);

   function Echo_Poll_Cb_W
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id) return AIP.Err_T;
   pragma Import (C, Echo_Poll_Cb_W);

   ----------
   -- Recv --
   ----------

   procedure Echo_Recv_Cb
     (Sid   : AIP.IPTR_T;
      Tcb   : AIP.TCP.TCB_Id;
      Pbu   : AIP.Pbufs.Pbuf_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Recv_Cb);

   function Echo_Recv_Cb_W
     (Sid   : AIP.IPTR_T;
      Tcb   : AIP.TCP.TCB_Id;
      Pbu   : AIP.Pbufs.Pbuf_Id;
      Errin : AIP.Err_T) return AIP.Err_T;
   pragma Import (C, Echo_Recv_Cb_W);

   ------------
   -- Accept --
   ------------

   procedure Echo_Accept_Cb
     (Arg   : AIP.IPTR_T;
      Tcb   : AIP.TCP.TCB_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL; in CB_IDENTIFIERS;
   pragma Export (C, Echo_Accept_Cb);

   function Echo_Accept_Cb_W
     (Arg   : AIP.IPTR_T;
      Tcb   : AIP.TCP.TCB_Id;
      Errin : AIP.Err_T) return AIP.Err_T;
   pragma Import (C, Echo_Accept_Cb_W);

   ---------
   -- Err --
   ---------

   procedure Echo_Err_Cb
     (Sid : AIP.IPTR_T;
      Err : AIP.Err_T);
   --# global in out ECHO_STATE_POOL;
   pragma Export (C, Echo_Err_Cb);

end RAW_Tcpecho;
