------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Conversions;
with AIP.Support, AIP.IPaddrs, AIP.TCP, AIP.Pbufs, AIP.Callbacks;

use type AIP.IPTR_T, AIP.S8_T, AIP.U8_T, AIP.U16_T;

package body RAW_Tcpecho is

   --  We will be using the raw callback API, passing application
   --  state information across calls for each connection.

   type State_Id is
     (ES_FREE, ES_NONE, ES_ACCEPTED, ES_RECEIVED, ES_CLOSING, ES_ERROR);
   type Echo_State is record
      Id : State_Id;
      Retries : AIP.U8_T;
      Tcb : AIP.TCP.TCB_Id;
      Pbu : AIP.Pbufs.Pbuf_Id;
   end record;
   pragma Suppress_Initialization (Echo_State);

   --  To be able to go SPARK, we will use array indices as "pointers"
   --  in a static pool.

   subtype ES_Id is AIP.IPTR_T range 0 .. 1;
   subtype Valid_ES_Id is ES_Id range ES_Id'First + 1 .. ES_Id'Last;
   type Echo_State_Array is array (Valid_ES_Id) of Echo_State;

   NOES : constant ES_Id := ES_Id'First;

   ESP : Echo_State_Array; -- Echo_State Pool

   --  Callback identifiers.  Straight pointers that the C implementation
   --  of LWIP can call at this point.  Will turn into mere identifiers for
   --  static case dispatching later on.

   ------------------
   -- Init_ES_Pool --
   ------------------

   --  Initialize the Echo_State pool, required before any other op

   procedure Init_ES_Pool is
   begin
      for Id in Valid_ES_Id loop
         ESP (Id).Id := ES_FREE;
      end loop;
   end Init_ES_Pool;

   --------------
   -- ES_Alloc --
   --------------

   --  Search a free for use entry in the pool. If found, move to ES_NONE
   --  and return Id. Return NOES otherwise.

   function ES_Alloc return ES_Id is
   begin
      for Sid in Valid_ES_Id loop
         if ESP (Sid).Id = ES_FREE then
            ESP (Sid).Id := ES_NONE;
            return Sid;
         end if;
      end loop;
      return NOES;
   end ES_Alloc;

   ----------------
   -- ES_release --
   ----------------

   --  Arrange for the Echo_State entry with SID id to be free for re-use

   procedure ES_Release (Sid : ES_Id) is
   begin
      ESP (Sid).Id := ES_FREE;
   end ES_Release;

   ----------------
   -- Echo_Close --
   ----------------

   procedure Echo_Close
     (Tcb : AIP.TCP.TCB_Id; Sid : ES_Id)
   is
      Err : AIP.Err_T;
   begin
      AIP.TCP.Tcp_Arg  (Tcb, AIP.NULID);
      AIP.TCP.Tcp_Sent (Tcb, AIP.Callbacks.NOCB);
      AIP.TCP.Tcp_Recv (Tcb, AIP.Callbacks.NOCB);
      AIP.TCP.Tcp_Err  (Tcb, AIP.Callbacks.NOCB);
      AIP.TCP.Tcp_Poll (Tcb, AIP.Callbacks.NOCB, 0);

      ES_Release (Sid);
      Err := AIP.TCP.Tcp_Close (Tcb);
      AIP.Support.Verify (Err = AIP.NOERR);
   end Echo_Close;

   ---------------
   -- Echo_Send --
   ---------------

   procedure Echo_Send
     (Tcb : AIP.TCP.TCB_Id; Sid : ES_Id)
   is
      Pbu : AIP.Pbufs.Pbuf_Id;
      Plen : AIP.U16_T;
      Err : AIP.Err_T := AIP.NOERR;
   begin

      --  Proceed as long as there's something left to send and there's room
      --  for it in the curent output buffer. Punt if something wrong happens.

      while Err = AIP.NOERR
        and then ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF
        and then AIP.Pbufs.Pbuf_Len (ESP (Sid).Pbu) <= AIP.TCP.Tcp_Sndbuf (Tcb)
      loop

         --  Enqueue the current pbuf for transmission

         Pbu := ESP (Sid).Pbu;
         Err := AIP.TCP.Tcp_Write
           (Tcb, AIP.Pbufs.Pbuf_Payload (Pbu), AIP.Pbufs.Pbuf_Len (Pbu), 1);

         --  If all went well, move to next pbuf in chain

         if Err = AIP.NOERR then

            ESP (Sid).Pbu := AIP.Pbufs.Pbuf_Next (Pbu);
            if ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF then
               AIP.Pbufs.Pbuf_Ref (ESP (Sid).Pbu);
            end if;

            --  chop first pbuf from chain

            Plen := AIP.Pbufs.Pbuf_Len (Pbu);

            while AIP.Pbufs.Pbuf_Free (Pbu) = 0 loop
               null;
            end loop;

            --  we can read more data now
            AIP.TCP.Tcp_Recved (Tcb, Plen);

         elsif Err = AIP.ERR_MEM then
            --  we are low on memory, try harder later, defer to poll
            ESP (Sid).Pbu := Pbu;
         else
            --  other problem ??
            null;
         end if;

      end loop;

   end Echo_Send;


   ------------------
   -- Echo_Sent_Cb --
   ------------------

   function Echo_Sent_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Len : AIP.U16_T) return AIP.Err_T
   is
      pragma Unreferenced (Len);
   begin

      if ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF then
         Echo_Send (Tcb, Sid);
      elsif ESP (Sid).Id = ES_CLOSING then
         Echo_Close (Tcb, Sid);
      end if;

      return AIP.NOERR;
   end Echo_Sent_Cb;

   Echo_Sent_Cb_Id   : constant AIP.Callbacks.Callback_Id
     := AIP.Conversions.To_IPTR (Echo_Sent_Cb'Address);

   -----------------
   -- Echo_Err_Cb --
   -----------------

   procedure Echo_Err_Cb
     (Sid : AIP.IPTR_T;
      Err : AIP.Err_T)
   is
      pragma Unreferenced (Err);
   begin
      ESP (Sid).Id := ES_ERROR;
   end Echo_Err_Cb;

   Echo_Err_Cb_Id    : constant AIP.Callbacks.Callback_Id
     := AIP.Conversions.To_IPTR (Echo_Err_Cb'Address);

   ------------------
   -- Echo_Poll_Cb --
   ------------------

   function Echo_Poll_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id) return AIP.Err_T
   is
   begin

      if Sid = AIP.NULID then
         AIP.TCP.Tcp_Abort (Tcb);
         return AIP.ERR_ABRT;
      end if;

      if ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF then
         Echo_Send (Tcb, Sid);

      elsif ESP (Sid).Id = ES_CLOSING then
         Echo_Close (Tcb, Sid);
      end if;

      return AIP.NOERR;
   end Echo_Poll_Cb;

   Echo_Poll_Cb_Id   : constant AIP.Callbacks.Callback_Id
     := AIP.Conversions.To_IPTR (Echo_Poll_Cb'Address);

   ------------------
   -- Echo_Recv_Cb --
   ------------------

   function Echo_Recv_Cb
     (Sid : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Pbu : AIP.Pbufs.Pbuf_Id;
      Err : AIP.Err_T) return AIP.Err_T
   is
   begin

      if Pbu = AIP.Pbufs.NOPBUF then

         --  Remote host closed connection. Process what is left to be
         --  sent or close on our side.

         ESP (Sid).Id := ES_CLOSING;

         if ESP (Sid).Pbu /= AIP.Pbufs.NOPBUF then
            Echo_Send (Tcb, Sid);
         else
            Echo_Close (Tcb, Sid);
         end if;

         return AIP.NOERR;

      end if;

      if Err /= AIP.NOERR then

         --  cleanup request, unkown reason

         if Pbu /= AIP.Pbufs.NOPBUF then
            ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;
            AIP.Pbufs.Pbuf_Blind_Free (Pbu);
         end if;

         return Err;
      end if;

      case ESP (Sid).Id is
         when ES_ACCEPTED =>

            ESP (Sid).Id := ES_RECEIVED;
            ESP (Sid).Pbu := Pbu;
            Echo_Send (Tcb, Sid);

         when ES_RECEIVED =>

            --  read some more data
            if ESP (Sid).Pbu = AIP.Pbufs.NOPBUF then
               ESP (Sid).Pbu := Pbu;
               AIP.TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
               Echo_Send (Tcb, Sid);
            else
               AIP.Pbufs.Pbuf_Chain (ESP (Sid).Pbu, Pbu);
            end if;

         when ES_CLOSING =>

            --  odd case, remote side closing twice, trash data
            AIP.TCP.Tcp_Recved (Tcb, AIP.Pbufs.Pbuf_Tlen (Pbu));
            ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;

            AIP.Pbufs.Pbuf_Blind_Free (Pbu);

         when others =>

            AIP.TCP.Tcp_Recved (Tcb, AIP.Pbufs.Pbuf_Tlen (Pbu));
            ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;
            AIP.Pbufs.Pbuf_Blind_Free (Pbu);

      end case;

      return AIP.NOERR;

   end Echo_Recv_Cb;

   Echo_Recv_Cb_Id   : constant AIP.Callbacks.Callback_Id
     := AIP.Conversions.To_IPTR (Echo_Recv_Cb'Address);

   --------------------
   -- Echo_Accept_Cb --
   --------------------

   function Echo_Accept_Cb
     (Arg : AIP.IPTR_T;
      Tcb : AIP.TCP.TCB_Id;
      Err : AIP.Err_T) return AIP.Err_T
   is
      pragma Unreferenced (Arg);
      pragma Unreferenced (Err);

      Sid : constant ES_Id := ES_Alloc;
   begin
      if Sid = NOES then
         return AIP.ERR_MEM;
      end if;

      ESP (Sid).Id := ES_ACCEPTED;
      ESP (Sid).Tcb := Tcb;
      ESP (Sid).Retries := 0;
      ESP (Sid).Pbu := AIP.Pbufs.NOPBUF;

      AIP.TCP.Tcp_Arg (Tcb, Sid);
      AIP.TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
      AIP.TCP.Tcp_Recv (Tcb, Echo_Recv_Cb_Id);
      AIP.TCP.Tcp_Err  (Tcb, Echo_Err_Cb_Id);
      AIP.TCP.Tcp_Poll (Tcb, Echo_Poll_Cb_Id, 0);
      return AIP.NOERR;
   end Echo_Accept_Cb;

   Echo_Accept_Cb_Id : constant AIP.Callbacks.Callback_Id
     := AIP.Conversions.To_IPTR (Echo_Accept_Cb'Address);

   ----------
   -- Init --
   ----------

   procedure Init is
      Tcb : AIP.TCP.TCB_Id;
      Err : AIP.Err_T;
   begin
      Init_ES_Pool;

      Tcb := AIP.TCP.Tcp_New;
      if Tcb = AIP.TCP.NOTCB then
         null;
      else
         Err := AIP.TCP.Tcp_Bind (Tcb, AIP.IPaddrs.IP_ADDR_ANY, 7);
         if Err /= AIP.NOERR then
            null;
         else
            Tcb := AIP.TCP.Tcp_Listen (Tcb);
            AIP.TCP.Tcp_Accept (Tcb, Echo_Accept_Cb_Id);
         end if;
      end if;
   end Init;

end RAW_Tcpecho;
