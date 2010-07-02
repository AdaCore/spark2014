------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config, AIP.Inet, AIP.IPH, AIP.UDPH;

package body AIP.UDP is

   UDP_SHARED_ENDPOINTS : constant Boolean := False;

   UDP_LOCAL_PORT_FIRST : constant Port_T := 1;
   UDP_LOCAL_PORT_LAST  : constant Port_T := 255;

   --------------------
   -- Datastructures --
   --------------------

   --  We maintain a static array of PCBs, together with a list of those
   --  bound to a local addr/port endpoint. This list is used to determine
   --  which PCB gets to process an incoming datagram (UDP_Input).

   type UDP_PCB_Array is array (PCB_Id) of UDP_PCB;

   PCBs : UDP_PCB_Array;
   Bound_PCBs : AIP.EID;

   -----------------
   --  Init_PCBs  --
   -----------------

   procedure Init_PCBs is
   begin
      for I in PCB_Id'First .. PCB_Id'Last loop
         PCBs (I).Link := PCB_NOUSE;
      end loop;
      Bound_PCBs := PCB_NOID;
   end Init_PCBs;

   --------------------
   --  PCB_Allocate  --
   --------------------

   procedure PCB_Allocate (Id : out AIP.EID) is
      Cid : PCB_Id;  -- Candidate Id
   begin
      Id := PCB_NOID;
      Cid := PCB_Id'First;
      loop
         if PCBs (Cid).Link = PCB_NOUSE then
            Id := Cid;
            PCBs (Id).Link := PCB_NOID;
         end if;
         exit when Id /= PCB_NOID or else Cid = PCB_Id'Last;
         Cid := Cid + 1;
      end loop;
   end PCB_Allocate;

   -------------
   -- UDP_New --
   -------------

   procedure UDP_New (Id : out PCB_Id) is
   begin
      PCB_Allocate (Id);
      PCBs (Id).IPCB.TTL := Config.UDP_TTL;
   end UDP_New;

   ---------------
   -- UDP_Udata --
   ---------------

   procedure UDP_Set_Udata (Pcb : PCB_Id; Udata : AIP.IPTR_T) is
   begin
      PCBs (Pcb).Udata := Udata;
   end UDP_Set_Udata;

   function UDP_Udata (Pcb : PCB_Id) return AIP.IPTR_T is
   begin
      return PCBs (Pcb).Udata;
   end UDP_Udata;

   -------------------------
   -- UDP_Input internals --
   -------------------------

   procedure IP_To_UDP
     (Buf  : Buffers.Buffer_Id;
      Uhdr : out AIP.IPTR_T;
      Err  : out Err_T)
   is
      Ihdr : constant AIP.IPTR_T := Buffers.Buffer_Payload (Buf);
      IPhlen : constant U16_T := U16_T (IPH.IPH_HLEN (Ihdr)) * 4;
   begin
      Err := AIP.NOERR;
      if Buffers.Buffer_Tlen (Buf) < IPhlen + UDP_HLEN then
         Err := AIP.ERR_MEM;
      else
         Buffers.Buffer_Header (Buf, -S16_T (IPhlen), Err);
      end if;
      if Err = AIP.NOERR then
         Uhdr := Buffers.Buffer_Payload (Buf);
      end if;
   end IP_To_UDP;

   function UDP_PCB_For
     (Ihdr, Uhdr : AIP.IPTR_T; Netif : NIF.Netif_Id) return AIP.EID
   is
      Cid, Pcb : AIP.EID;
      Ideal_Pcb, Good_Pcb : AIP.EID := PCB_NOID;

      Local_Match, Remote_Match : Boolean;

      Src_IP   : constant IPaddrs.IPaddr := IPH.IPH_SRC (Ihdr);
      Src_Port : constant Port_T := UDPH.UDPH_SRC (Uhdr);

      Dst_IP   : constant IPaddrs.IPaddr := IPH.IPH_DST (Ihdr);
      Dst_Port : constant Port_T := UDPH.UDPH_DST (Uhdr);

   begin
      Cid := Bound_PCBs;

      loop
         exit when Ideal_Pcb /= PCB_NOID or else Cid = PCB_NOID;

         --  See if PCB local addr+port match UDP destination addr+port

         Local_Match :=
           PCBs (Cid).Local_Port = Dst_Port
           and then
           (IPaddrs.Match (PCBs (Cid).IPCB.Local_IP, Dst_IP)
            or else
            IPaddrs.Bcast (Dst_IP, NIF.NIF_IP (Netif), NIF.NIF_MASK (Netif)));

         --  If it does, see if the PCB remote addr+port pair matches the
         --  UDP source, in which case we have an ideal taker.  Otherwise,
         --  remember that PCB as a fallback possible destination if it is
         --  unconnected.

         if Local_Match then

            Remote_Match :=
              PCBs (Cid).Remote_Port = Src_Port
              and then IPaddrs.Match (PCBs (Cid).IPCB.Remote_IP, Src_IP);

            if Remote_Match then
               Ideal_Pcb := Cid;
            elsif Good_Pcb = PCB_NOID
              and then (PCBs (Cid).Flags and UDP_FLAGS_CONNECTED) /= 0
            then
               Good_Pcb := Cid;
            end if;
         end if;

         Cid := PCBs (Cid).Link;
      end loop;

      if Ideal_Pcb /= PCB_NOID then
         Pcb := Ideal_Pcb;
      else
         Pcb := Good_Pcb;  --  which might be NOID
      end if;

      return Pcb;
   end UDP_PCB_For;

   ---------------
   -- UDP_Input --
   ---------------

   procedure UDP_Input
     (Buf : Buffers.Buffer_Id;
      Netif : NIF.Netif_Id)
   is
      Ihdr : constant AIP.IPTR_T := Buffers.Buffer_Payload (Buf);
      Uhdr : AIP.IPTR_T;

      Err : AIP.Err_T;
      Pcb : AIP.EID;
   begin

      --  Until we know otherwise ...

      Err := AIP.NOERR;

      --  Perform a couple of checks and retrieve an UDP view
      --  of the incoming datagram.

      IP_To_UDP (Buf, Uhdr, Err);

      --  Find the best UDP PCB to take it, verify the checksum and
      --  adjust the payload offset before passing up to the applicative
      --  callback.

      if No (Err) then

         Pcb := UDP_PCB_For (Ihdr, Uhdr, Netif);

         if Pcb /= PCB_NOID
           or else IPaddrs.Same (NIF.NIF_IP (Netif), IPH.IPH_DST (Ihdr))
         then
            null;  --  ??? cksum check here
         end if;

         Buffers.Buffer_Header (Buf, -UDP_HLEN, Err);

         if Pcb = PCB_NOID then
            --  icmp dest unreachable
            null;
         end if;
      end if;

      --  If we have a taker, trigger an UDP_RECV event if a callback
      --  was registered for it. Buffer release is the application's
      --  responsibility in this case.

      if No (Err) and then Pcb /= PCB_NOID
        and then PCBs (Pcb).RECV_Cb /= Callbacks.NOCB
      then
         declare
            RECV_Event : constant UDP_Event_T :=
              (Kind => UDP_RECV,
               Buf  => Buf,
               IP   => IPH.IPH_SRC (Ihdr),
               Port => UDPH.UDPH_SRC (Uhdr));
         begin
            UDP_Event (RECV_Event, Pcb, PCBs (Pcb).RECV_Cb);
         end;
      else
         Buffers.Buffer_Blind_Free (Buf);
      end if;

   end UDP_Input;

   ------------------------
   -- UDP_Bind Internals --
   ------------------------

   function PCB_Binding_Matches
     (Pcb  : UDP_PCB;
      IP   : AIP.IPaddrs.IPaddr;
      Port : Port_T) return Boolean is
   begin
      return Pcb.Local_Port = Port
        and then AIP.IPaddrs.Match (Pcb.IPCB.Local_IP, IP);
   end PCB_Binding_Matches;

   function PCB_Bound_To (Port : Port_T) return AIP.EID is
      Pid : AIP.EID;
   begin
      Pid := Bound_PCBs;
      while Pid /= PCB_NOID loop
         if PCBs (Pid).Local_Port = Port then
            return Pid;
         end if;
         Pid := PCBs (Pid).Link;
      end loop;
      return PCB_NOID;
   end PCB_Bound_To;

   function Available_Port return Port_T is
      Port : Port_T := UDP_LOCAL_PORT_FIRST;
   begin
      while Port <= UDP_LOCAL_PORT_LAST loop
         if PCB_Bound_To (Port) = PCB_NOID then
            return Port;
         else
            Port := Port + 1;
         end if;
      end loop;
      return NOPORT;
   end Available_Port;

   ----------------
   --  UDP_Bind  --
   ----------------

   procedure UDP_Bind
     (Pcb : PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T;
      Err  : out AIP.Err_T)
   is
      Rebind : Boolean;
      Pid : AIP.EID;
      Port_To_Bind : Port_T;
   begin

      Err := NOERR;

      --  See if we're rebinding an already bound PCB, and/or if
      --  we're binding to the same addr/port as another bound PCB.

      Pid := Bound_PCBs;
      while Pid /= PCB_NOID and then Err = NOERR loop
         if Pid = Pcb then
            Rebind := True;
         elsif not UDP_SHARED_ENDPOINTS
           and then PCB_Binding_Matches (PCBs (Pid), Local_IP, Local_Port)
         then
            Err := AIP.ERR_USE;
         end if;
         Pid := PCBs (Pid).Link;
      end loop;

      --  Pick an available port if none was specified

      if Err = NOERR then
         if Local_Port = NOPORT then
            Port_To_Bind := Available_Port;
            if Port_To_Bind = NOPORT then
               Err := AIP.ERR_USE;
            end if;
         else
            Port_To_Bind := Local_Port;
         end if;
      end if;

      --  Assign the local IP/port, and insert into the list of bound PCBs
      --  unless it was already there

      if Err = NOERR then
         PCBs (Pcb).Local_Port := Port_To_Bind;
         PCBs (Pcb).IPCB.Local_IP := Local_IP;

         if not Rebind then
            PCBs (Pcb).Link := Bound_PCBs;
            Bound_PCBs := Pcb;
         end if;
      end if;

   end UDP_Bind;

   ----------------------
   --  PCB_Force_Bind  --
   ----------------------

   procedure PCB_Force_Bind (Pcb : PCB_Id; Err : out Err_T) is
   begin
      if PCBs (Pcb).Local_Port = NOPORT then
         UDP_Bind (Pcb, PCBs (Pcb).IPCB.Local_IP, NOPORT, Err);
      else
         Err := AIP.NOERR;
      end if;
   end PCB_Force_Bind;

   ----------------
   -- PCB_Unlink --
   ----------------

   procedure PCB_Unlink (Pcb : PCB_Id) is
      Cur, Prev : AIP.EID;
   begin
      pragma Assert (Pcb /= PCB_NOID);

      if Pcb = Bound_PCBs then
         Bound_PCBs := PCBs (Pcb).Link;
      else
         Prev := PCB_NOID;
         Cur := Bound_PCBs;

         while Cur /= PCB_NOID and then Pcb /= Cur loop
            Prev := Cur;
            Cur := PCBs (Cur).Link;
         end loop;

         if Cur /= PCB_NOID then
            pragma Assert (Prev /= PCB_NOID);
            PCBs (Prev).Link := PCBs (Cur).Link;
            PCBs (Cur).Link := PCB_NOID;
         end if;
      end if;
   end PCB_Unlink;

   -------------------
   --  UDP_Connect  --
   -------------------

   procedure UDP_Connect
     (Pcb : PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      Err : out AIP.Err_T) is
   begin
      --  Make sure we have a local binding in place

      PCB_Force_Bind (Pcb, Err);

      --  If all went fine, assign the remote endpoint components and flag
      --  the PCB as connected. Either Pcb had a local_port set on entry,
      --  meaning bound already, or we nound it ourselves.  In both cases,
      --  it should already be present in the list of active PCBs.

      if Err = AIP.NOERR then
         PCBs (Pcb).IPCB.Remote_IP := Remote_IP;
         PCBs (Pcb).Remote_Port := Remote_Port;
         PCBs (Pcb).Flags := PCBs (Pcb).Flags or UDP_FLAGS_CONNECTED;
      end if;
   end UDP_Connect;

   -------------------------
   --  UDP_Send internals --
   -------------------------

   procedure Prepend_UDP_Header
     (Buf  : Buffers.Buffer_Id;
      Ubuf : out Buffers.Buffer_Id;
      Err  : out AIP.Err_T)
   is
   begin

      Buffers.Buffer_Header (Buf, UDP_HLEN, Err);
      if Err = NOERR then
         Ubuf := Buf;
      else
         Buffers.Buffer_Alloc
           (Inet.HLEN_To (Inet.IP_LAYER), UDP_HLEN, Buffers.MONO_BUF, Ubuf);
         if Ubuf = Buffers.NOBUF then
            Err := ERR_MEM;
         else
            Buffers.Buffer_Chain (Ubuf, Buf);
         end if;
      end if;
   end Prepend_UDP_Header;

   procedure UDP_Send_To_If
     (Pcb   : PCB_Id;
      Buf   : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      Dst_Port : Port_T;
      Netif : AIP.NIF.Netif_Id;
      Err   : out AIP.Err_T)
   is
      Ubuf : Buffers.Buffer_Id := Buffers.NOBUF;
      Uhdr : AIP.IPTR_T;
      --  Full UDP buffer with header, to be passed down to IP

      Src_IP : AIP.IPaddrs.IPaddr;
   begin
      --  Setup a local binding if we don't have one already, then
      --  make room for a UDP header in front.

      PCB_Force_Bind (Pcb, Err);

      if Err = AIP.NOERR then
         Prepend_UDP_Header (Buf, Ubuf, Err);
      end if;

      --  Fetch source IP to use from the interface. This is normally the same
      --  as the PCB local address, unless the latter is IP_ADDR_ANY, or the
      --  interface IP has changed since the routing request was issued. Bets
      --  are off in the latter case, so drop the packet.

      if Err = AIP.NOERR then

         Src_IP := NIF.NIF_IP (Netif);

         if not IPaddrs.Any (PCBs (Pcb).IPCB.Local_IP)
           and then not IPaddrs.Same (PCBs (Pcb).IPCB.Local_IP, Src_IP)
         then
            Err := ERR_VAL;
         end if;
      end if;

      --  Compute/Assign the UDP header fields, pass the whole thing to IP and
      --  release the dedicated buffer we allocated for the header, if any.

      if Err = AIP.NOERR then

         Uhdr := Buffers.Buffer_Payload (Ubuf);

         UDPH.UDPH_Set_SRC (Uhdr, PCBs (Pcb).Local_Port);
         UDPH.UDPH_Set_DST (Uhdr, Dst_Port);
         UDPH.UDPH_Set_LEN (Uhdr, Buffers.Buffer_Tlen (Ubuf));
         UDPH.UDPH_Set_SUM (Uhdr, 16#0000#);

         IP.IP_Output_If
           (Ubuf, Src_IP, Dst_IP,
            PCBs (Pcb).IPCB.TTL, PCBs (Pcb).IPCB.TOS,
            IPH.IP_PROTO_UDP, Netif, Err);

         if Ubuf /= Buf then
            Buffers.Buffer_Blind_Free (Ubuf);
         end if;
      end if;
   end UDP_Send_To_If;

   --------------
   -- UDP_Send --
   --------------

   procedure UDP_Send
     (Pcb : PCB_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T)
   is
      Dst_IP : constant IPaddrs.IPaddr := PCBs (Pcb).IPCB.Remote_IP;
      Dst_Port : constant Port_T := PCBs (Pcb).Remote_Port;

      Netif : AIP.EID;
   begin
      AIP.IP.IP_Route (Dst_IP, Netif);
      if Netif = AIP.NIF.IF_NOID then
         Err := ERR_RTE;
      else
         UDP_Send_To_If (Pcb, Buf, Dst_IP, Dst_Port, Netif, Err);
      end if;
   end UDP_Send;

   ----------------------
   --  UDP_Disconnect  --
   ----------------------

   procedure UDP_Disconnect (Pcb : PCB_Id) is
   begin
      --  Reset the remote address association and flag PCB as unconnected

      PCBs (Pcb).IPCB.Remote_IP := IPaddrs.IP_ADDR_ANY;
      PCBs (Pcb).Remote_Port := 0;
      PCBs (Pcb).Flags := PCBs (Pcb).Flags and not UDP_FLAGS_CONNECTED;
   end UDP_Disconnect;

   -------------------
   --  UDP_Release  --
   -------------------

   procedure UDP_Release (Pcb : PCB_Id) is
   begin
      PCB_Unlink (Pcb);
      PCBs (Pcb).Link := PCB_NOUSE;
   end UDP_Release;

   --------------------
   --  UDP_Callback  --
   --------------------

   procedure UDP_Callback
     (Evk  : UDP_Event_Kind;
      Pcb  : PCB_Id;
      Cbid : Callbacks.Callback_Id)
   is
   begin
      case Evk is
         when UDP_RECV => PCBs (Pcb).RECV_Cb := Cbid;
      end case;
   end UDP_Callback;

begin
   Init_PCBs;
end AIP.UDP;
