------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--         Copyright (C) 2010-2012, Free Software Foundation, Inc.          --
------------------------------------------------------------------------------

with AIP.TCP;
with AIP.Buffers;
with AIP.IPaddrs;
with AIP.PCBs;

with System, RAW_TCP_Callbacks;

use type AIP.S8_T, AIP.U8_T, AIP.U16_T, AIP.S32_T;

package body RAW_TCP_Echo
   --#  own ECHO_STATE_POOL is ESP;
is

   use type System.Address;

   ---------------------------
   -- Echo State management --
   ---------------------------

   --  We will be using the raw callback API, passing application
   --  state information across calls for each connection.

   type State_Kind is
     (ES_FREE, ES_READY, ES_ACCEPTED, ES_RECEIVED, ES_CLOSING);
   type Echo_State is record
      Kind : State_Kind;
      Pcb  : AIP.PCBs.PCB_Id;
      Buf  : AIP.Buffers.Buffer_Id;
      Err  : AIP.Err_T;
   end record;
   pragma Suppress_Initialization (Echo_State);

   subtype ES_Id is AIP.EID range 0 .. 2;
   subtype Valid_ES_Id is ES_Id range ES_Id'First + 1 .. ES_Id'Last;
   NOES : constant ES_Id := ES_Id'First;

   type Echo_State_Array is array (Valid_ES_Id) of Echo_State;

   ESP : Echo_State_Array; -- Echo_State Pool

   procedure Init_ES_Pool;
   procedure ES_Alloc   (Sid : out ES_Id);
   procedure ES_Release (Es  : in out Echo_State);

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Echo_Close
     (Pcb : AIP.PCBs.PCB_Id;
      Es  : in out Echo_State);

   procedure Echo_Send
     (Pcb : AIP.PCBs.PCB_Id;
      Es  : in out Echo_State);

   procedure ECHO_Process_Sent
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T);

   procedure ECHO_Process_Abort
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T);

   procedure ECHO_Process_Poll
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T);

   procedure ECHO_Process_Recv
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T);

   procedure ECHO_Process_Accept
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T);

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

   --  Search a free for use entry in the pool. If found, move to ES_NONE and
   --  return Id. Return NOES otherwise.

   procedure ES_Alloc (Sid : out ES_Id)
   --# global in out ESP;
   is
   begin
      Sid := NOES;
      for Id in Valid_ES_Id loop
         if ESP (Id).Kind = ES_FREE then
            ESP (Id).Kind := ES_READY;
            Sid := Id;
            exit;
         end if;
      end loop;
   end ES_Alloc;

   ----------------
   -- ES_Release --
   ----------------

   --  Arrange for the Echo_State entry ES to be free for re-use

   procedure ES_Release (Es : in out Echo_State) is
   begin
      Es.Kind := ES_FREE;
   end ES_Release;

   ----------------
   -- Echo_Close --
   ----------------

   procedure Echo_Close
     (Pcb : AIP.PCBs.PCB_Id;
      Es  : in out Echo_State)
   --# global in out ESP;
   is
      Err : AIP.Err_T;
   begin
      ES_Release (Es);
      AIP.TCP.TCP_Close (Pcb, Err);
      pragma Assert (AIP.No (Err));
   end Echo_Close;

   ---------------
   -- Echo_Send --
   ---------------

   procedure Echo_Send
     (Pcb : AIP.PCBs.PCB_Id;
      Es  : in out Echo_State)
   --# global in out ESP; in out AIP.Buffers.State;
   is
      Buf  : AIP.Buffers.Buffer_Id;
      Plen : AIP.U16_T;
      Err  : AIP.Err_T := AIP.NOERR;
   begin

      --  Proceed as long as there's something left to send and there's room
      --  for it in the curent output buffer. Punt if something wrong happens.

      while Err = AIP.NOERR
        and then Es.Buf /= AIP.Buffers.NOBUF
        and then AIP.Buffers.Buffer_Len (Es.Buf) <= AIP.TCP.TCP_Sndbuf (Pcb)
      loop
         --  Enqueue the current Buf for transmission

         Buf := Es.Buf;
         AIP.TCP.TCP_Write
           (PCB  => Pcb,
            Data => AIP.Buffers.Buffer_Payload (Buf),
            Len  => AIP.M32_T (AIP.Buffers.Buffer_Len (Buf)),
            Copy => True,
            Push => False,
            Err  => Err);

         --  If all went well, move to next Buf in chain

         if Err = AIP.NOERR then

            --  Record length of sent data

            Plen := AIP.Buffers.Buffer_Len (Buf);

            --  Grab reference to the following Buf, if any

            Es.Buf := AIP.Buffers.Buffer_Next (Buf);
            if Es.Buf /= AIP.Buffers.NOBUF then
               AIP.Buffers.Buffer_Ref (Es.Buf);
            end if;

            --  Deallocate the processed buffer

            AIP.Buffers.Buffer_Blind_Free (Buf);

            --  Signal TCP layer that we can accept more data

            AIP.TCP.TCP_Recved (Pcb, Plen);

         elsif Err = AIP.ERR_MEM then

            --  We are low on memory, defer to poll

            Es.Buf := Buf;
            --  This is a no-op???

         else
            --  other problem ??
            null;
         end if;

      end loop;

   end Echo_Send;

   -----------------------
   -- ECHO_Process_Sent --
   -----------------------

   procedure ECHO_Process_Sent
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T)
   is
      Es : Echo_State;
      for Es'Address use AIP.TCP.TCP_Udata (Pcb);
   begin
      if Es.Buf /= AIP.Buffers.NOBUF then
         --  More data to send, do it now

         Echo_Send (Pcb, Es);

      elsif Es.Kind = ES_CLOSING then
         Echo_Close (Pcb, Es);
      end if;

      Err := AIP.NOERR;
   end ECHO_Process_Sent;

   ------------------------
   -- ECHO_Process_Abort --
   ------------------------

   procedure ECHO_Process_Abort
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T)
   --# global in out ESP;
   is
      Es : Echo_State;
      for Es'Address use AIP.TCP.TCP_Udata (Pcb);
   begin
      ES_Release (Es);
      Err := AIP.NOERR;
   end ECHO_Process_Abort;

   -----------------------
   -- ECHO_Process_Poll --
   -----------------------

   procedure ECHO_Process_Poll
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T)
   is
      Es : Echo_State;
      for Es'Address use AIP.TCP.TCP_Udata (Pcb);
   begin
      if Es'Address = System.Null_Address then
         AIP.TCP.TCP_Drop (Pcb);
         Err := AIP.ERR_ABRT;
      elsif Es.Buf /= AIP.Buffers.NOBUF then
         Echo_Send (Pcb, Es);
         Err := AIP.NOERR;
      elsif Es.Kind = ES_CLOSING then
         Echo_Close (Pcb, Es);
         Err := AIP.NOERR;
      end if;
   end ECHO_Process_Poll;

   -----------------------
   -- ECHO_Process_Recv --
   -----------------------

   procedure ECHO_Process_Recv
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T)
   is
      Es : Echo_State;
      for Es'Address use AIP.TCP.TCP_Udata (Pcb);
   begin

      if Ev.Buf = AIP.Buffers.NOBUF then

         --  Remote host closed connection. Process what is left to be
         --  sent or close on our side.

         Es.Kind := ES_CLOSING;

         if Es.Buf /= AIP.Buffers.NOBUF then
            Echo_Send (Pcb, Es);
         else
            Echo_Close (Pcb, Es);
         end if;

      else
         case Es.Kind is
            when ES_ACCEPTED =>

               Es.Kind := ES_RECEIVED;
               Es.Buf  := Ev.Buf;
               AIP.Buffers.Buffer_Ref (Ev.Buf);
               Echo_Send (Pcb, Es);

            when ES_RECEIVED =>

               --  Read some more data

               if Es.Buf = AIP.Buffers.NOBUF then
                  AIP.Buffers.Buffer_Ref (Ev.Buf);
                  Es.Buf := Ev.Buf;
                  Echo_Send (Pcb, Es);

               else
                  AIP.Buffers.Buffer_Chain (Es.Buf, Ev.Buf);
               end if;

            when others =>

               --  Remote side closing twice (ES_CLOSING), or inconsistent
               --  state. Trash.

               AIP.TCP.TCP_Recved (Pcb, AIP.Buffers.Buffer_Tlen (Ev.Buf));
               Es.Buf := AIP.Buffers.NOBUF;

         end case;

      end if;

      Err := AIP.NOERR;

   end ECHO_Process_Recv;

   -------------------------
   -- ECHO_Process_Accept --
   -------------------------

   procedure ECHO_Process_Accept
     (Ev  : AIP.TCP.TCP_Event_T;
      Pcb : AIP.PCBs.PCB_Id;
      Err : out AIP.Err_T)
   is
      Sid : ES_Id;
   begin
      ES_Alloc (Sid);

      if Sid = NOES then
         Err := AIP.ERR_MEM;
      else
         ESP (Sid).Kind := ES_ACCEPTED;
         ESP (Sid).Pcb  := Pcb;
         ESP (Sid).Buf  := AIP.Buffers.NOBUF;

         AIP.TCP.TCP_Set_Udata (Pcb, ESP (Sid)'Address);

         AIP.TCP.On_TCP_Sent
           (Pcb, RAW_TCP_Callbacks.To_CBID (ECHO_Process_Sent'Access));
         AIP.TCP.On_TCP_Recv
           (Pcb, RAW_TCP_Callbacks.To_CBID (ECHO_Process_Recv'Access));
         AIP.TCP.On_TCP_Abort
           (Pcb, RAW_TCP_Callbacks.To_CBID (ECHO_Process_Abort'Access));
         AIP.TCP.On_TCP_Poll
           (Pcb, RAW_TCP_Callbacks.To_CBID (ECHO_Process_Poll'Access), 500);

         AIP.TCP.TCP_Accepted (Pcb);

         Err := AIP.NOERR;
      end if;
   end ECHO_Process_Accept;

   ----------
   -- Init --
   ----------

   procedure Init
   is
      Pcb : AIP.PCBs.PCB_Id;
      Err : AIP.Err_T;

   begin
      --  Initialize the application state pool, then setup to
      --  accept TCP connections on the well known echo port 7.

      Init_ES_Pool;

      AIP.TCP.TCP_New (Pcb);
      if Pcb = AIP.PCBs.NOPCB then
         Err := AIP.ERR_MEM;
      else
         AIP.TCP.TCP_Bind
           (PCB        => Pcb,
            Local_IP   => AIP.IPaddrs.IP_ADDR_ANY,
            Local_Port => 7,
            Err        => Err);
      end if;

      if Err = AIP.NOERR then
         AIP.TCP.TCP_Listen (Pcb, Err);
         pragma Assert (AIP.No (Err));
         AIP.TCP.On_TCP_Accept
           (Pcb, RAW_TCP_Callbacks.To_CBID (ECHO_Process_Accept'Access));
      end if;

   end Init;

end RAW_TCP_Echo;
