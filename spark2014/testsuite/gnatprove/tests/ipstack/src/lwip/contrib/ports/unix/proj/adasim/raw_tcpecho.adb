------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;

with AIP_Support, AIP_Ctypes, AIP_IPaddrs, AIP_TCP, AIP_Pbufs, AIP_Callbacks;

package body RAW_Tcpecho is

   package SU renames AIP_Support;
   package CB renames AIP_Callbacks;
   package CT renames AIP_Ctypes;
   package PB renames AIP_Pbufs;

   package TCP renames AIP_TCP;
   package IPA renames AIP_IPaddrs;

   use type PB.Pbuf_Id;
   use type TCP.TCB_Id;
   use type CT.S8_T, CT.U8_T, CT.U16_T, CT.SI_T;
   use type System.Address;

   --  We will be using the raw callback API, passing application
   --  state information across calls for each connection.

   type State_Id is
     (ES_FREE, ES_NONE, ES_ACCEPTED, ES_RECEIVED, ES_CLOSING, ES_ERROR);
   type Echo_State is record
      Id : State_Id;
      Retries : CT.U8_T;
      Tcb : TCP.TCB_Id;
      Pbu : PB.Pbuf_Id;
   end record;
   pragma Suppress_Initialization (Echo_State);

   --  To be able to go SPARK, we will use array indices as "pointers"
   --  in a static pool.

   subtype ES_Id is CT.SI_T range 0 .. 1;
   subtype Valid_ES_Id is ES_Id range ES_Id'First + 1 .. ES_Id'Last;
   type Echo_State_Array is array (Valid_ES_Id) of Echo_State;

   NOES : constant ES_Id := ES_Id'First;

   ESP : Echo_State_Array; -- Echo_State Pool

   --  Callback declarations

   function Echo_Accept_Cb
     (Arg : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Err : CT.Err_T) return CT.Err_T;

   function Echo_Recv_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Pbu : PB.Pbuf_Id;
      Err : CT.Err_T) return CT.Err_T;

   procedure Echo_Err_Cb
     (Sid : CT.SI_T;
      Err : CT.Err_T);

   function Echo_Poll_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id) return CT.Err_T;

   function Echo_Sent_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Len : CT.U16_T) return CT.Err_T;

   --  Callback identifiers.  Straight pointers that the C implementation
   --  of LWIP can call at this point.  Will turn into mere identifiers for
   --  static case dispatching later on.

   Echo_Accept_Cb_Id : constant CB.Callback_Id := Echo_Accept_Cb'Address;
   Echo_Err_Cb_Id    : constant CB.Callback_Id := Echo_Err_Cb'Address;
   Echo_Recv_Cb_Id   : constant CB.Callback_Id := Echo_Recv_Cb'Address;
   Echo_Poll_Cb_Id   : constant CB.Callback_Id := Echo_Poll_Cb'Address;
   Echo_Sent_Cb_Id   : constant CB.Callback_Id := Echo_Sent_Cb'Address;

   --  Local subprogram declarations

   procedure Echo_Send (Tcb : TCP.TCB_Id; Sid : ES_Id);

   procedure Echo_Close (Tcb : TCP.TCB_Id; Sid : ES_Id);

   --  Very simple Echo_State pool management

   procedure Init_ES_Pool;
   --  Initialize the Echo_State pool, required before any other op

   function ES_Alloc return ES_Id;
   --  Search a free for use entry in the pool. If found, move to ES_NONE
   --  and return Id. Return NOES otherwise.

   procedure ES_Release (Sid : ES_Id);
   --  Arrange for the Echo_State entry with SID id to be free for re-use

   ------------------
   -- Init_ES_Pool --
   ------------------

   procedure Init_ES_Pool is
   begin
      for Id in ESP'Range loop
         ESP (Id).Id := ES_FREE;
      end loop;
   end Init_ES_Pool;

   --------------
   -- ES_Alloc --
   --------------

   function ES_Alloc return ES_Id is
   begin
      for Sid in ESP'Range loop
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

   procedure ES_Release (Sid : ES_Id) is
   begin
      ESP (Sid).Id := ES_FREE;
   end ES_Release;

   ----------
   -- Init --
   ----------

   procedure Init is
      Tcb : TCP.TCB_Id;
      Err : CT.Err_T;
   begin
      Init_ES_Pool;

      Tcb := TCP.Tcp_New;
      if Tcb = TCP.NOTCB then
         return;
      end if;

      Err := TCP.Tcp_Bind (Tcb, IPA.IP_ADDR_ANY, 7);
      if Err /= CT.NOERR then
         return;
      end if;

      Tcb := TCP.Tcp_Listen (Tcb);
      TCP.Tcp_Accept (Tcb, Echo_Accept_Cb_Id);
   end Init;

   --------------------
   -- Echo_Accept_Cb --
   --------------------

   function Echo_Accept_Cb
     (Arg : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Err : CT.Err_T) return CT.Err_T
   is
      pragma Unreferenced (Arg);
      pragma Unreferenced (Err);

      Sid : constant ES_Id := ES_Alloc;
   begin
      if Sid = NOES then
         return CT.ERR_MEM;
      end if;

      ESP (Sid).Id := ES_ACCEPTED;
      ESP (Sid).Tcb := Tcb;
      ESP (Sid).Retries := 0;
      ESP (Sid).Pbu := PB.NOPBUF;

      TCP.Tcp_Arg (Tcb, Sid);
      TCP.Tcp_Recv (Tcb, Echo_Recv_Cb_Id);
      TCP.Tcp_Err  (Tcb, Echo_Err_Cb_Id);
      TCP.Tcp_Poll (Tcb, Echo_Poll_Cb_Id, 0);
      return CT.NOERR;
   end Echo_Accept_Cb;

   function Echo_Recv_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Pbu : PB.Pbuf_Id;
      Err : CT.Err_T) return CT.Err_T
   is
   begin

      if Pbu = PB.NOPBUF then

         --  Remote host closed connection. Process what is left to be
         --  sent or close on our side.

         ESP (Sid).Id := ES_CLOSING;

         if ESP (Sid).Pbu /= PB.NOPBUF then
            TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
            Echo_Send (Tcb, Sid);
         else
            Echo_Close (Tcb, Sid);
         end if;

         return CT.NOERR;

      end if;

      if Err /= CT.NOERR then

         --  cleanup request, unkown reason

         if Pbu /= PB.NOPBUF then
            ESP (Sid).Pbu := PB.NOPBUF;
            PB.Pbuf_Blind_Free (Pbu);
         end if;

         return Err;
      end if;

      case ESP (Sid).Id is
         when ES_ACCEPTED =>

            --  first data chunk in p->payload
            ESP (Sid).Id := ES_RECEIVED;

            --  store reference to incoming pbuf (chain)
            ESP (Sid).Pbu := Pbu;

            --  install send completion notifier and echo
            TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
            Echo_Send (Tcb, Sid);

         when ES_RECEIVED =>

            --  read some more data
            if ESP (Sid).Pbu = PB.NOPBUF then
               ESP (Sid).Pbu := Pbu;
               TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
               Echo_Send (Tcb, Sid);
            else
               PB.Pbuf_Chain (ESP (Sid).Pbu, Pbu);
            end if;

         when ES_CLOSING =>

            --  odd case, remote side closing twice, trash data
            TCP.Tcp_Recved (Tcb, PB.Tot_Len (Pbu));
            ESP (Sid).Pbu := PB.NOPBUF;

            PB.Pbuf_Blind_Free (Pbu);

         when others =>

            TCP.Tcp_Recved (Tcb, PB.Tot_Len (Pbu));
            ESP (Sid).Pbu := PB.NOPBUF;
            PB.Pbuf_Blind_Free (Pbu);

      end case;

      return CT.NOERR;

   end Echo_Recv_Cb;

   procedure Echo_Err_Cb
     (Sid : CT.SI_T;
      Err : CT.Err_T)
   is
      pragma Unreferenced (Err);
   begin
      ESP (Sid).Id := ES_ERROR;
   end Echo_Err_Cb;

   function Echo_Poll_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id) return CT.Err_T
   is
   begin

      if Sid = CT.NOSID then
         TCP.Tcp_Abort (Tcb);
         return CT.ERR_ABRT;
      end if;

      if ESP (Sid).Pbu /= PB.NOPBUF then

         --  there is a remaining pbuf (chain)
         TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
         Echo_Send (Tcb, Sid);

      elsif ESP (Sid).Id = ES_CLOSING then
         Echo_Close (Tcb, Sid);
      end if;

      return CT.NOERR;
   end Echo_Poll_Cb;

   function Echo_Sent_Cb
     (Sid : CT.SI_T;
      Tcb : TCP.TCB_Id;
      Len : CT.U16_T) return CT.Err_T
   is
      pragma Unreferenced (Len);
   begin

      if ESP (Sid).Pbu /= PB.NOPBUF then

         --  there is a remaining pbuf (chain)
         TCP.Tcp_Sent (Tcb, Echo_Sent_Cb_Id);
         Echo_Send (Tcb, Sid);

      elsif ESP (Sid).Id = ES_CLOSING then
         Echo_Close (Tcb, Sid);
      end if;

      return CT.NOERR;
   end Echo_Sent_Cb;

   ---------------
   -- Echo_Send --
   ---------------

   procedure Echo_Send
     (Tcb : TCP.TCB_Id; Sid : ES_Id)
   is
      Pbu : PB.Pbuf_Id;
      Plen : CT.U16_T;
      Err : CT.Err_T := CT.NOERR;
   begin

      --  Proceed as long as there's something left to send and there's room
      --  for it in the curent output buffer. Punt if something wrong happens.

      while Err = CT.NOERR
        and then ESP (Sid).Pbu /= PB.NOPBUF
        and then PB.Len (ESP (Sid).Pbu) <= TCP.Tcp_Sndbuf (Tcb)
      loop

         --  Enqueue the current pbuf for transmission

         Pbu := ESP (Sid).Pbu;
         Err := TCP.Tcp_Write (Tcb, PB.Payload (Pbu), PB.Len (Pbu), 1);

         --  If all went well, move to next pbuf in chain

         if Err = CT.NOERR then

            ESP (Sid).Pbu := PB.Next (Pbu);
            if ESP (Sid).Pbu /= PB.NOPBUF then
               PB.Pbuf_Ref (ESP (Sid).Pbu);
            end if;

            --  chop first pbuf from chain

            Plen := PB.Len (Pbu);

            while PB.Pbuf_Free (Pbu) = 0 loop
               null;
            end loop;

            --  we can read more data now
            TCP.Tcp_Recved (Tcb, Plen);

         elsif Err = CT.ERR_MEM then
            --  we are low on memory, try harder later, defer to poll
            ESP (Sid).Pbu := Pbu;
         else
            --  other problem ??
            null;
         end if;

      end loop;

   end Echo_Send;

   ----------------
   -- Echo_Close --
   ----------------

   procedure Echo_Close
     (Tcb : TCP.TCB_Id; Sid : ES_Id)
   is
      Err : CT.Err_T;
   begin
      TCP.Tcp_Arg  (Tcb, CT.NOSID);
      TCP.Tcp_Sent (Tcb, CB.NOCB);
      TCP.Tcp_Recv (Tcb, CB.NOCB);
      TCP.Tcp_Err  (Tcb, CB.NOCB);
      TCP.Tcp_Poll (Tcb, CB.NOCB, 0);

      ES_Release (Sid);
      Err := TCP.Tcp_Close (Tcb);
      SU.Assert (Err = CT.NOERR);
   end Echo_Close;

end RAW_Tcpecho;
