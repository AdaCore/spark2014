------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  TCP echo server implementation using the RAW callback API

with AIP.LWTCP, AIP.Pbufs;
--# inherit AIP.Pools, AIP.Support,
--#         AIP.IPaddrs, AIP.Pbufs, AIP.Callbacks, AIP.LWTCP;

use type AIP.IPTR_T;

package RAW_TCPecho
   --# own CB_IDENTIFIERS, ECHO_STATE_POOL;
is

   procedure Init;
   --# global out CB_IDENTIFIERS; in out ECHO_STATE_POOL;
   --  Setup server to wait for and process connections

private

   ---------------------------
   -- Echo State management --
   ---------------------------

   --  To be able to go SPARK, we will use array indices as "pointers"
   --  in a static pool.

   subtype ES_Id is AIP.IPTR_T range 0 .. 2;
   subtype Valid_ES_Id is ES_Id range ES_Id'First + 1 .. ES_Id'Last;
   NOES : constant ES_Id := ES_Id'First;

   procedure Init_ES_Pool;
   procedure ES_Alloc   (Sid : out ES_Id);
   procedure ES_Release (Sid : ES_Id);
   procedure Echo_Close (Tcb : AIP.TCP.PCB_Id; Sid : ES_Id);
   procedure Echo_Send  (Tcb : AIP.TCP.PCB_Id; Sid : ES_Id);

   --  Callback imports/exports. See AIP.Callbacks for the rationale.

   ----------
   -- Sent --
   ----------

   procedure Echo_Sent_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Sent_Cb);

   function Echo_Sent_Cb_W
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id;
      Len : AIP.U16_T) return AIP.Err_T;
   pragma Import (C, Echo_Sent_Cb_W);

   ----------
   -- Poll --
   ----------

   procedure Echo_Poll_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id;
      Err : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Poll_Cb);

   function Echo_Poll_Cb_W
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id) return AIP.Err_T;
   pragma Import (C, Echo_Poll_Cb_W);

   ----------
   -- Recv --
   ----------

   procedure Echo_Recv_Cb
     (Sid   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
      Buf   : AIP.Buffers.Buffer_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL, AIP.Pools.PBUF_POOL;
   pragma Export (C, Echo_Recv_Cb);

   function Echo_Recv_Cb_W
     (Sid   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
      Pbu   : AIP.Buffers.Buffer_Id;
      Errin : AIP.Err_T) return AIP.Err_T;
   pragma Import (C, Echo_Recv_Cb_W);

   ------------
   -- Accept --
   ------------

   procedure Echo_Accept_Cb
     (Arg   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T);
   --# global in out ECHO_STATE_POOL; in CB_IDENTIFIERS;
   pragma Export (C, Echo_Accept_Cb);

   function Echo_Accept_Cb_W
     (Arg   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
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

end RAW_TCPecho;
