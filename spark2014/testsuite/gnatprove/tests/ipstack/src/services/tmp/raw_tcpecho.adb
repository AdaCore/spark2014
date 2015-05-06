------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Callbacks;
with AIP.Conversions;
with AIP.Pools, AIP.Support, AIP.IPaddrs, AIP.LWTCP, AIP.Pbufs, AIP.Callbacks;

use type AIP.S8_T, AIP.U8_T, AIP.U16_T;

package body RAW_TCPecho
   --# own CB_IDENTIFIERS is
   --#     Echo_Sent_Cb_Id,
   --#     Echo_Err_Cb_Id,
   --#     Echo_Poll_Cb_Id,
   --#     Echo_Recv_Cb_Id,
   --#     Echo_Accept_Cb_Id

   --#   & ECHO_STATE_POOL is ESP;
is

   --  We will be using the raw callback API, passing application
   --  state information across calls for each connection.

   type State_Kind is
     (ES_FREE, ES_NONE, ES_ACCEPTED, ES_RECEIVED, ES_CLOSING, ES_ERROR);
   type Echo_State is record
      Kind : State_Kind;
      Tcb  : AIP.LWTCP.TCB_Id;
      Buf  : AIP.Buffers.Buffer_Id;
      Err  : AIP.Err_T;
   end record;
   pragma Suppress_Initialization (Echo_State);

   type Echo_State_Array is array (Valid_ES_Id) of Echo_State;

   ESP : Echo_State_Array; -- Echo_State Pool

   --  Callback identifiers. Such declarations have to come ahead of
   --  ~anything else for SPARK.

   Echo_Sent_Cb_Id,
   Echo_Err_Cb_Id,
   Echo_Poll_Cb_Id,
   Echo_Recv_Cb_Id,
   Echo_Accept_Cb_Id : AIP.Callbacks.CBK_Id;

   ------------------
   -- Init_ES_Pool --
   ------------------

   --  Initialize the Echo_State pool, required before any other op

   procedure Init_ES_Pool
   --# global in out ESP;
   is
   begin
      for Id in Valid_ES_Id loop
         ESP (Id).Kind := ES_FREE;
      end loop;
   end Init_ES_Pool;

   --------------
   -- ES_Alloc --
   --------------

   --  Search a free for use entry in the pool. If found, move to ES_NONE
   --  and return Id. Return NOES otherwise.

   procedure ES_Alloc (Sid : out ES_Id)
   --# global in out ESP;
   is
   begin
      Sid := NOES;
      for Id in Valid_ES_Id loop
         if ESP (Id).Kind = ES_FREE then
            ESP (Id).Kind := ES_NONE;
            Sid := Id;
            exit;
         end if;
      end loop;
   end ES_Alloc;

   ----------------
   -- ES_release --
   ----------------

   --  Arrange for the Echo_State entry with SID id to be free for re-use

   procedure ES_Release (Sid : ES_Id)
   --# global in out ESP;
   is
   begin
      ESP (Sid).Kind := ES_FREE;
   end ES_Release;

   ----------------
   -- Echo_Close --
   ----------------

   procedure Echo_Close
     (Tcb : AIP.LWTCP.TCB_Id; Sid : ES_Id)
     --# global in out ESP;
   is
      Err : AIP.Err_T;
   begin
      AIP.LWTCP.Tcp_Arg  (Tcb, AIP.NULID);
      AIP.LWTCP.Tcp_Sent (Tcb, AIP.Callbacks.NOCB);
      AIP.LWTCP.Tcp_Recv (Tcb, AIP.Callbacks.NOCB);
      AIP.LWTCP.Tcp_Err  (Tcb, AIP.Callbacks.NOCB);
      AIP.LWTCP.Tcp_Poll (Tcb, AIP.Callbacks.NOCB, 0);

      ES_Release (Sid);
      Err := AIP.LWTCP.Tcp_Close (Tcb);
      AIP.Support.Verify (Err = AIP.NOERR);
   end Echo_Close;

   ---------------
   -- Echo_Send --
   ---------------

   procedure Echo_Send
     (Tcb : AIP.LWTCP.TCB_Id; Sid : ES_Id)
     --# global in out ESP; in out AIP.Pools.PBUF_POOL;
   is
      Buf : AIP.Buffers.Buffer_Id;
      Plen : AIP.U16_T;
      Err : AIP.Err_T := AIP.NOERR;
   begin

      --  Proceed as long as there's something left to send and there's room
      --  for it in the curent output buffer. Punt if something wrong happens.

      while Err = AIP.NOERR
        and then ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF
        and then AIP.Pbufs.Pbuf_Len (ESP (Sid).Pbu) <= AIP.LWTCP.Tcp_Sndbuf (Tcb)
      loop

         --  Enqueue the current Buff for transmission

         Buf := ESP (Sid).Buf;
         Err := AIP.LWTCP.Tcp_Write
                  (Tcb,
                   AIP.Buffers.Buffer_Payload (Buf),
                   AIP.Buffers.Buffer_Len (Buf),
                   1);

         --  If all went well, move to next Buff in chain

         if Err = AIP.NOERR then

            --  Grab reference to the following Buff, if any. Release
            --  the one we just processed and inform tell the other end.

            ESP (Sid).Buf := AIP.Buffers.Buffer_Next (Buf);
            if ESP (Sid).Buf /= AIP.Buffers.NOBUF then
               AIP.Buffers.Buffer_Ref (ESP (Sid).Buf);
            end if;

            --  chop first Buff from chain

            Plen := AIP.Buffers.Buffer_Len (Buf);
            AIP.Buffers.Buffer_Release (Buf);

            --  we can read more data now
            AIP.LWTCP.Tcp_Recved (Tcb, Plen);

         elsif Err = AIP.ERR_MEM then
            --  we are low on memory, try harder later, defer to poll
            ESP (Sid).Buf := Buf;
         else
            --  other problem ??
            null;
         end if;

      end loop;

   end Echo_Send;

   ------------------
   -- Echo_Sent_Cb --
   ------------------

   procedure Echo_Sent_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id;
      Len : AIP.U16_T;
      Err : out AIP.Err_T)
      --# global in out ESP, AIP.Pools.BufF_POOL;
   is
      pragma Unreferenced (Len);
   begin

      if ESP (Sid).Buf /= AIP.Buffers.NOBUF then
         Echo_Send (Tcb, Sid);
      elsif ESP (Sid).Kind = ES_CLOSING then
         Echo_Close (Tcb, Sid);
      end if;

      Err := AIP.NOERR;

      --# accept Flow, 30, Len, "unused generic callback arg";
   end Echo_Sent_Cb;

   -----------------
   -- Echo_Err_Cb --
   -----------------

   procedure Echo_Err_Cb
     (Sid : AIP.IPTR_T;
      Err : AIP.Err_T)
      --# global in out ESP;
   is
   begin
      ESP (Sid).Kind := ES_ERROR;
      ESP (Sid).Err  := Err;
   end Echo_Err_Cb;

   ------------------
   -- Echo_Poll_Cb --
   ------------------

   procedure Echo_Poll_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.LWTCP.TCB_Id;
      Err : out AIP.Err_T)
      --# global in out ESP, AIP.Pools.BufF_POOL;
   is
   begin

      if Sid = AIP.NULID then
         AIP.LWTCP.Tcp_Abort (Tcb);
         Err := AIP.ERR_ABRT;

      else
         if ESP (Sid).Buf /= AIP.Buffers.NOBUF then
            Echo_Send (Tcb, Sid);

         elsif ESP (Sid).Kind = ES_CLOSING then
            Echo_Close (Tcb, Sid);
         end if;

         Err := AIP.NOERR;
      end if;
   end Echo_Poll_Cb;

   ------------------
   -- Echo_Recv_Cb --
   ------------------

   procedure Echo_Recv_Cb
     (Sid   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
      Buf   : AIP.Buffers.Buffer_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T)
      --# global in out ESP, AIP.Pools.BufF_POOL;
   is
   begin

      if Buf = AIP.Buffers.NOBUF then

         --  Remote host closed connection. Process what is left to be
         --  sent or close on our side.

         ESP (Sid).Kind := ES_CLOSING;

         if ESP (Sid).Buf /= AIP.Buffers.NOBUF then
            Echo_Send (Tcb, Sid);
         else
            Echo_Close (Tcb, Sid);
         end if;

         Err := AIP.NOERR;

      elsif Errin /= AIP.NOERR then

         --  Cleanup request, unkown reason

         ESP (Sid).Buf := AIP.Buffers.NOBUF;
         AIP.Buffers.Buffer_Blind_Free (Buf);
         Err := Errin;

      else

         case ESP (Sid).Kind is
            when ES_ACCEPTED =>

               ESP (Sid).Kind := ES_RECEIVED;
               ESP (Sid).Buf := Buf;
               Echo_Send (Tcb, Sid);

            when ES_RECEIVED =>

               --  read some more data
               if ESP (Sid).Buf = AIP.Buffers.NOBUF then
                  ESP (Sid).Buf := Buf;
                  Echo_Send (Tcb, Sid);
               else
                  AIP.Buffers.Buffer_Chain (ESP (Sid).Buf, Buf);
               end if;

            when ES_CLOSING =>

               --  odd case, remote side closing twice, trash data
               AIP.LWTCP.Tcp_Recved (Tcb, AIP.Pbufs.Pbuf_Tlen (Pbu));
               ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;

               AIP.Buffers.Buffer_Blind_Free (Buf);

            when others =>

               AIP.LWTCP.Tcp_Recved (Tcb, AIP.Pbufs.Pbuf_Tlen (Pbu));
               ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;
               AIP.Pbufs.Pbuf_Blind_Free (Pbu);

         end case;

         Err := AIP.NOERR;

      end if;

   end Echo_Recv_Cb;

   --------------------
   -- Echo_Accept_Cb --
   --------------------

   procedure Echo_Accept_Cb
     (Arg   : AIP.IPTR_T;
      Tcb   : AIP.LWTCP.TCB_Id;
      Errin : AIP.Err_T;
      Err   : out AIP.Err_T)
      --# global in Echo_Sent_Cb_Id, Echo_Recv_Cb_Id,
      --#           Echo_Err_Cb_Id, Echo_Poll_Cb_Id;
      --#    in out ESP;
   is
      pragma Unreferenced (Arg, Errin);
      Sid : ES_Id;
   begin
      ES_Alloc (Sid);
      if Sid = NOES then
         Err := AIP.ERR_MEM;
      else

         ESP (Sid).Kind := ES_ACCEPTED;
         ESP (Sid).Tcb  := Tcb;
         ESP (Sid).Buf  := AIP.Buffers.NOBUF;

         AIP.LWTCP.Tcp_Arg  (Tcb, Sid);
         AIP.LWTCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
         AIP.LWTCP.Tcp_Recv (Tcb, Echo_Recv_Cb_Id);
         AIP.LWTCP.Tcp_Err  (Tcb, Echo_Err_Cb_Id);
         AIP.LWTCP.Tcp_Poll (Tcb, Echo_Poll_Cb_Id, 0);

         AIP.LWTCP.Tcp_Accepted (Tcb);

         Err := AIP.NOERR;
      end if;

      --# accept Flow, 30, Arg, "unused generic callback arg";
      --# accept Flow, 30, Errin, "unused generic callback arg";
   end Echo_Accept_Cb;

   ----------
   -- Init --
   ----------

   procedure Init
      --# global out Echo_Accept_Cb_Id, Echo_Sent_Cb_Id, Echo_Recv_Cb_Id,
      --#            Echo_Err_Cb_Id, Echo_Poll_Cb_Id;
      --#     in out ESP;
   is
      Tcb : AIP.LWTCP.TCB_Id;
      Err : AIP.Err_T;

      procedure Init_CB_IDENTIFIERS;

      procedure Init_CB_IDENTIFIERS
         --# global out Echo_Accept_Cb_Id, Echo_Sent_Cb_Id, Echo_Recv_Cb_Id,
         --#            Echo_Err_Cb_Id, Echo_Poll_Cb_Id;
         --  See AIP.Callbacks for the rationale
      is
         --# hide Init_CB_IDENTIFIERS
      begin
         Echo_Sent_Cb_Id :=
           AIP.Conversions.To_IPTR (Echo_Sent_Cb_W'Address);
         Echo_Poll_Cb_Id :=
           AIP.Conversions.To_IPTR (Echo_Poll_Cb_W'Address);
         Echo_Recv_Cb_Id :=
           AIP.Conversions.To_IPTR (Echo_Recv_Cb_W'Address);
         Echo_Accept_Cb_Id :=
           AIP.Conversions.To_IPTR (Echo_Accept_Cb_W'Address);
         Echo_Err_Cb_Id :=
           AIP.Conversions.To_IPTR (Echo_Err_Cb'Address);
      end Init_CB_IDENTIFIERS;

   begin
      --  Initialize callback identifiers + app state pool, then setup to
      --  accept TCP connections on the well known echo port 7.

      Init_CB_IDENTIFIERS;
      Init_ES_Pool;

      Tcb := AIP.LWTCP.Tcp_New;
      if Tcb = AIP.LWTCP.NOTCB then
         Err := AIP.ERR_MEM;
      else
         Err := AIP.LWTCP.Tcp_Bind (Tcb, AIP.IPaddrs.IP_ADDR_ANY, 7);
         if Err = AIP.NOERR then
            Tcb := AIP.LWTCP.Tcp_Listen (Tcb);
            AIP.LWTCP.Tcp_Accept (Tcb, Echo_Accept_Cb_Id);
         end if;
      end if;

   end Init;

end RAW_TCPecho;
