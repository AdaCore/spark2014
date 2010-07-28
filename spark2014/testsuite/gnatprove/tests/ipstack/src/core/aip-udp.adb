------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Inet;

with AIP.ICMP;
with AIP.ICMPH;
with AIP.IPH;
with AIP.UDPH;

package body AIP.UDP
   --# own State is PCBs, Bound_PCBs;
is

   ---------------------
   -- Data structures --
   ---------------------

   --  Valid PCB_Ids are indices into a static array of PCBs, maintained
   --  together with a list of those bound to a local addr/port endpoint.
   --  This list is used to determine which PCB gets to process an incoming
   --  datagram (see UDP_Input).

   subtype Valid_PCB_Ids is PCB_Id range NOPCB + 1 .. PCB_Id'Last;
   type UDP_PCB_Array is array (Valid_PCB_IDs) of UDP_PCB;

   PCBs : UDP_PCB_Array;
   Bound_PCBs : AIP.EID;

   ----------------
   --  UDP_Init  --
   ----------------

   procedure UDP_Init
      --# global out PCBs, Bound_PCBs;
   is
   begin
      --  Initialize all the PCBs, marking them unused, and initialize
      --  the list of bound PCBs as empty.

      PCBs := UDP_PCB_Array'(others => UDP_PCB_Initializer);
      Bound_PCBs := NOPCB;
   end UDP_Init;

   --------------------
   --  PCB_Allocate  --
   --------------------

   procedure PCB_Allocate (Id : out AIP.EID)
      --# global in out PCBs;
   is
      Cid : PCB_Id;  -- Candidate Id
   begin
      --  Scan the PCBs array and pick the first UNUSED entry

      Id := NOPCB;
      Cid := Valid_PCB_Ids'First;
      loop
         if PCBs (Cid).Link = PCB_UNUSED then
            Id := Cid;
            PCBs (Id).Link := NOPCB;
         end if;
         exit when Id /= NOPCB or else Cid = Valid_PCB_Ids'Last;
         Cid := Cid + 1;
      end loop;
   end PCB_Allocate;

   ---------------
   -- PCB_Clear --
   ---------------

   procedure PCB_Clear (PCB : PCB_Id)
      --# global in out PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      PCBs (PCB) := UDP_PCB_Initializer;
      PCBs (PCB).Link := NOPCB;
   end PCB_Clear;

   -------------
   -- UDP_New --
   -------------

   procedure UDP_New (Id : out PCB_Id)
      --# global in out PCBs;
   is
   begin
      PCB_Allocate (Id);
      if Id /= NOPCB then
         PCB_Clear (Id);
         PCBs (Id).IPCB.TTL := Config.UDP_TTL;
      end if;
   end UDP_New;

   -------------------------
   -- UDP_Input internals --
   -------------------------

   ---------------
   -- IP_To_UDP --
   ---------------

   procedure IP_To_UDP
     (Buf  : Buffers.Buffer_Id;
      Uhdr : out System.Address;
      Err  : out AIP.Err_T)
   is
      Ihdr : System.Address;
      --  Address of the IP header in BUF

      IPhlen : AIP.U16_T;
      --  Length of this header
   begin
      --  We expect BUF to have just been provided by the IP layer

      Ihdr := Buffers.Buffer_Payload (Buf);
      IPhlen := AIP.U16_T (IPH.IPH_IHL (Ihdr)) * 4;

      --  ERR_MEM if the buffer length is such that this couldn't possibly be a
      --  UDP datagram, when there's not even room for the UDP & IP headers.
      --  Otherwise, move payload to the UDP header by hiding the IP one.

      if Buffers.Buffer_Tlen (Buf) < IPhlen + UDP_HLEN then
         Err := AIP.ERR_MEM;
      else
         Buffers.Buffer_Header (Buf, -AIP.S16_T (IPhlen), Err);
      end if;

      --  If the length check and the payload move went fine, we have the UDP
      --  header at hand.

      if Err = AIP.NOERR then
         Uhdr := Buffers.Buffer_Payload (Buf);
      else
         Uhdr := System.Null_Address;
      end if;
   end IP_To_UDP;

   -----------------
   -- UDP_PCB_For --
   -----------------

   function UDP_PCB_For
     (Ihdr  : System.Address;
      Uhdr  : System.Address;
      Netif : NIF.Netif_Id) return AIP.EID
      --# global in PCBs, Bound_PCBs;
   is
      Cid, PCB : AIP.EID;
      Ideal_PCB, Good_PCB : AIP.EID := NOPCB;

      Local_Match, Remote_Match : Boolean;

      Src_IP, Dst_IP : IPaddrs.IPaddr;
      Src_Port, Dst_Port : Port_T;

   begin

      Src_IP   := IPH.IPH_Src_Address (Ihdr);
      Src_Port := UDPH.UDPH_Src_Port (Uhdr);

      Dst_IP   := IPH.IPH_Dst_Address (Ihdr);
      Dst_Port := UDPH.UDPH_Dst_Port (Uhdr);

      --  Scan the list of bound PCBs in search of one at least locally bound
      --  to the datagram destination endpoint, and even better also connected
      --  to the remote source.

      Cid := Bound_PCBs;

      loop
         exit when Ideal_PCB /= NOPCB or else Cid = NOPCB;

         --  See if PCB local addr+port match UDP destination addr+port

         Local_Match :=
           PCBs (Cid).Local_Port = Dst_Port
           and then
           (IPaddrs.Match (PCBs (Cid).IPCB.Local_IP, Dst_IP)
            or else
            IPaddrs.Match (NIF.NIF_Broadcast (Netif), Dst_IP));
         --  ??? case of a datagram for the broadcast address arriving on
         --  one interface, and destined to the broadcast address of another,
         --  when we are bound on the specific address of the other interface?

         --  If it does, see if the PCB remote addr+port pair matches the
         --  UDP source, in which case we have an ideal taker. Otherwise,
         --  remember that PCB as a fallback possible destination if it is
         --  unconnected.

         if Local_Match then

            Remote_Match :=
              PCBs (Cid).Remote_Port = Src_Port
              and then IPaddrs.Match (PCBs (Cid).IPCB.Remote_IP, Src_IP);

            if Remote_Match then
               Ideal_PCB := Cid;

            elsif Good_PCB = NOPCB and then not PCBs (Cid).Connected then
               Good_PCB := Cid;
            end if;
         end if;

         Cid := PCBs (Cid).Link;
      end loop;

      if Ideal_PCB /= NOPCB then
         PCB := Ideal_PCB;
      else
         PCB := Good_PCB;  --  which might be NOID
      end if;

      return PCB;
   end UDP_PCB_For;

   ---------------
   -- UDP_Input --
   ---------------

   procedure UDP_Input
     (Buf   : Buffers.Buffer_Id;
      Netif : NIF.Netif_Id)
      --# global in out Buffers.State, Bound_PCBs, PCBs;

   is
      Ihdr, Uhdr : System.Address;

      Err : AIP.Err_T;
      PCB : AIP.EID := NOPCB;
   begin
      --  Latch address of IP header and retrieve a UDP view of the incoming
      --  datagram.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP_To_UDP (Buf, Uhdr, Err);

      --  Find the best UDP PCB to take the datagram, verify the checksum
      --  and adjust the payload offset before passing up to the applicative
      --  callback.

      if AIP.No (Err) then
         PCB := UDP_PCB_For (Ihdr, Uhdr, Netif);

         if PCB /= NOPCB
           or else
             IPaddrs.Same (NIF.NIF_Addr (Netif), IPH.IPH_Dst_Address (Ihdr))
         then
            null;  --  ??? cksum check here
         end if;

         if PCB = NOPCB then

            --  Recover IP header and send ICMP destination unreachable

            Buffers.Buffer_Header
              (Buf, 4 * AIP.S16_T (IPH.IPH_IHL (Ihdr)), Err);

            if AIP.No (Err) then
               ICMP.ICMP_Reject
                 (IP_Buf => Buf,
                  I_Type => ICMPH.ICMP_Type_Dest_Unreachable,
                  Code   => ICMPH.ICMP_Unreach_Code_Port_Unreachable);
            end if;

            Err := AIP.ERR_VAL;
         end if;
      end if;

      --  If we have a taker, trigger an UDP_RECV event if a callback was
      --  registered for it. Releasing the buffer is the application's
      --  responsibility in this case.

      if AIP.No (Err)
        and then PCB /= NOPCB
        and then PCBs (PCB).RECV_Cb /= Callbacks.NOCB
      then
         --  Skip UDP header and perform upcall to application

         Buffers.Buffer_Header (Buf, -UDP_HLEN, Err);

         UDP_Event
           (UDP_Event_T'(Kind => UDP_RECV,
                         Buf  => Buf,
                         IP   => IPH.IPH_Src_Address (Ihdr),
                         Port => UDPH.UDPH_Src_Port (Uhdr)),
            PCB,
            PCBs (PCB).RECV_Cb);
      else
         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end UDP_Input;

   ------------------------
   -- UDP_Bind Internals --
   ------------------------

   function PCB_Binding_Matches
     (PCB  : UDP_PCB;
      IPA  : IPaddrs.IPaddr;
      Port : Port_T) return Boolean
   is
   begin
      return PCB.Local_Port = Port
        and then IPaddrs.Match (PCB.IPCB.Local_IP, IPA);
   end PCB_Binding_Matches;

   function PCB_Bound_To (Port : Port_T) return AIP.EID
      --# global in PCBs, Bound_PCBs;
   is
      Pid : AIP.EID;
   begin
      Pid := Bound_PCBs;
      loop
         exit when Pid = NOPCB or else PCBs (Pid).Local_Port = Port;
         Pid := PCBs (Pid).Link;
      end loop;
      return Pid;
   end PCB_Bound_To;

   function Available_Port return Port_T
      --# global in PCBs, Bound_PCBs;
   is
      Aport : Port_T := NOPORT;  --  Port found to be available
      Cport : Port_T;            --  Candidate port to examine
   begin
      Cport := Config.UDP_LOCAL_PORT_FIRST;
      loop
         exit when Aport /= NOPORT or else Cport > Config.UDP_LOCAL_PORT_LAST;
         if PCB_Bound_To (Cport) = NOPCB then
            Aport := Cport;
         else
            Cport := Cport + 1;
         end if;
      end loop;
      return Aport;
   end Available_Port;

   ----------------
   --  UDP_Bind  --
   ----------------

   procedure UDP_Bind
     (PCB : PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : Port_T;
      Err  : out AIP.Err_T)
      --# global in out PCBs, Bound_PCBs;
   is
      Rebind : Boolean;
      Pid : AIP.EID;
      Port_To_Bind : Port_T;
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      Err := AIP.NOERR;

      --  See if we're rebinding an already bound PCB, and/or if
      --  we're binding to the same addr/port as another bound PCB.

      Rebind := False;

      Pid := Bound_PCBs;
      while Pid /= NOPCB and then AIP.No (Err) loop
         if Pid = PCB then
            Rebind := True;
         elsif not Config.UDP_SHARED_ENDPOINTS
           and then PCB_Binding_Matches (PCBs (Pid), Local_IP, Local_Port)
         then
            Err := AIP.ERR_USE;
         end if;
         Pid := PCBs (Pid).Link;
      end loop;

      if AIP.No (Err) then

         --  Pick an available port if none was specified

         if Local_Port = NOPORT then
            Port_To_Bind := Available_Port;
            if Port_To_Bind = NOPORT then
               Err := AIP.ERR_MEM;
            end if;
         else
            Port_To_Bind := Local_Port;
         end if;

         --  Assign the local IP/port, and insert into the list of bound PCBs
         --  unless it was already there.

         PCBs (PCB).Local_Port := Port_To_Bind;
         PCBs (PCB).IPCB.Local_IP := Local_IP;

         if not Rebind then
            PCBs (PCB).Link := Bound_PCBs;
            Bound_PCBs := PCB;
         end if;
      end if;

   end UDP_Bind;

   --------------------
   -- PCB_Force_Bind --
   --------------------

   procedure PCB_Force_Bind (PCB : PCB_Id; Err : out AIP.Err_T)
      --# global in out PCBs, Bound_PCBs;
   is
      Local_IP : IPaddrs.IPaddr;
   begin
      if PCBs (PCB).Local_Port = NOPORT then
         Local_IP := PCBs (PCB).IPCB.Local_IP;
         UDP_Bind (PCB, Local_IP, NOPORT, Err);
      else
         Err := AIP.NOERR;
      end if;
   end PCB_Force_Bind;

   ----------------
   -- PCB_Unlink --
   ----------------

   procedure PCB_Unlink (PCB : PCB_Id)
      --# global in out PCBs, Bound_PCBs;
   is
      Cur, Prev : AIP.EID;
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      if PCB = Bound_PCBs then
         Bound_PCBs := PCBs (PCB).Link;
      else
         Prev := NOPCB;
         Cur := Bound_PCBs;

         while Cur /= NOPCB and then PCB /= Cur loop
            Prev := Cur;
            Cur := PCBs (Cur).Link;
         end loop;

         if Cur /= NOPCB then
            pragma Assert (Prev /= NOPCB);
            PCBs (Prev).Link := PCBs (Cur).Link;
            PCBs (Cur).Link := NOPCB;
         end if;
      end if;
   end PCB_Unlink;

   -------------------
   --  UDP_Connect  --
   -------------------

   procedure UDP_Connect
     (PCB         : PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : Port_T;
      Err         : out AIP.Err_T)
      --# global in out PCBs, Bound_PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      --  Make sure we have a local binding in place, so that the (dummy)
      --  connection has two well identified endpoints.

      PCB_Force_Bind (PCB, Err);

      --  If all went fine, assign the remote endpoint components and flag
      --  the PCB as connected. Either PCB had a local_port set on entry,
      --  meaning bound already, or we bound it ourselves.  In both cases,
      --  it should already be present in the list of active PCBs.

      if AIP.No (Err) then
         PCBs (PCB).IPCB.Remote_IP := Remote_IP;
         PCBs (PCB).Remote_Port    := Remote_Port;
         PCBs (PCB).Connected      := True;
      end if;
   end UDP_Connect;

   -------------------------
   --  UDP_Send internals --
   -------------------------

   ------------------------
   -- Prepend_UDP_Header --
   ------------------------

   procedure Prepend_UDP_Header
     (Buf  : Buffers.Buffer_Id;
      Ubuf : out Buffers.Buffer_Id;
      Err  : out AIP.Err_T)
   is
      HLEN_To_IP : AIP.U16_T;
      Buf_Room : AIP.U16_T;
   begin
      --  If we have enough room for a UDP header and everything else
      --  downstack, simply adjust the current buffer payload. Otherwise,
      --  allocate a separate buffer for all the headers we'll need.

      Buf_Room := Buffers.Buffer_Poffset (Buf);
      HLEN_To_IP := Inet.HLEN_To (Inet.IP_LAYER);

      if Buf_Room >= HLEN_To_IP + UDP_HLEN then
         Buffers.Buffer_Header (Buf, UDP_HLEN, Err);
         pragma Assert (AIP.No (Err));
         Ubuf := Buf;
      else
         Buffers.Buffer_Alloc
           (Buffers.SPLIT_BUF, HLEN_To_IP, UDP_HLEN, Ubuf);
         if Ubuf = Buffers.NOBUF then
            Err := AIP.ERR_MEM;
         else
            Buffers.Buffer_Chain (Ubuf, Buf);
            Err := AIP.NOERR;
         end if;
      end if;
   end Prepend_UDP_Header;

   --------------------
   -- UDP_Send_To_If --
   --------------------

   procedure UDP_Send_To_If
     (PCB      : PCB_Id;
      Buf      : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      NH_IP    : IPaddrs.IPaddr;
      Dst_Port : Port_T;
      Netif    : NIF.Netif_Id;
      Err      : out AIP.Err_T)
      --# global in out Buffers.State, PCBs, Bound_PCBs;
   is
      Ubuf : Buffers.Buffer_Id;
      Ulen : AIP.U16_T;
      Uhdr : System.Address;
      --  UDP buffer to send, associated length and UDP header address

      Src_IP : IPaddrs.IPaddr;
      --  Source IP we'll advertise in the output datagram

      PUhdr : System.Address;
      --  Address of pseudo-header for checksum computation

   begin
      --  Setup a local binding if we don't have one already

      PCB_Force_Bind (PCB, Err);

      --  Make room for a UDP header in front of BUF

      Ubuf := Buffers.NOBUF;
      if AIP.No (Err) then
         Prepend_UDP_Header (Buf, Ubuf, Err);
      end if;

      --  Get source IP to use from the interface. This is normally the same
      --  as the PCB local address, unless the latter is IP_ADDR_ANY, or the
      --  interface IP has changed since the routing request was issued, and
      --  bets are off in the latter case, so drop the packet. If all is well
      --  compute/Assign the UDP header fields, pass the whole thing to IP and
      --  release the dedicated buffer we allocated for the header, if any.

      if AIP.No (Err) then

         Src_IP := NIF.NIF_Addr (Netif);

         if not IPaddrs.Any (PCBs (PCB).IPCB.Local_IP)
           and then not IPaddrs.Same (PCBs (PCB).IPCB.Local_IP, Src_IP)
         then
            Err := AIP.ERR_VAL;
         else
            Uhdr := Buffers.Buffer_Payload (Ubuf);
            Ulen := Buffers.Buffer_Tlen (Ubuf);

            UDPH.Set_UDPH_Src_Port (Uhdr, PCBs (PCB).Local_Port);
            UDPH.Set_UDPH_Dst_Port (Uhdr, Dst_Port);
            UDPH.Set_UDPH_Length   (Uhdr, Ulen);

            --  Checksum computation and assignment.

            --  Expose room for a temporary pseudo-header and fill it in. The
            --  length we store here is that of the original dgram. We expect
            --  room to be available already, anticipated for the IP and link
            --  layers downstack and not yet filled with anything of use.

            --# accept F, 10, Err, "Assignment is ineffective";
            Buffers.Buffer_Header
              (Ubuf, UDPH.UDP_Pseudo_Header_Size / 8, Err);
            pragma Assert (No (Err));
            --# end accept;

            PUhdr := Buffers.Buffer_Payload (Ubuf);
            UDPH.Set_UDPP_Src_Address (PUhdr, Src_IP);
            UDPH.Set_UDPP_Dst_Address (PUhdr, Dst_IP);
            UDPH.Set_UDPP_Zero        (PUhdr, 0);
            UDPH.Set_UDPP_Protocol    (PUhdr, IPH.IP_Proto_UDP);
            UDPH.Set_UDPP_Length      (PUhdr, Ulen);

            --  Compute checksum, pseudo-header included, then remove
            --  the pseudo-header

            UDPH.Set_UDPH_Checksum
              (Uhdr, not Checksum.Sum (Ubuf, Buffers.Buffer_Tlen (Ubuf)));

            --# accept F, 10, Err, "Assignment is ineffective";
            Buffers.Buffer_Header
              (Ubuf, -UDPH.UDP_Pseudo_Header_Size / 8, Err);
            pragma Assert (No (Err));
            --# end accept;

            --  Now ready to pass to IP

            IP.IP_Output_If
              (Ubuf,
               Src_IP,
               Dst_IP,
               NH_IP,
               PCBs (PCB).IPCB.TTL,
               PCBs (PCB).IPCB.TOS,
               IPH.IP_Proto_UDP,
               Netif,
               Err);

            if Ubuf /= Buf then
               Buffers.Buffer_Blind_Free (Ubuf);
            end if;
         end if;
      end if;
   end UDP_Send_To_If;

   --------------
   -- UDP_Send --
   --------------

   procedure UDP_Send
     (PCB : PCB_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T)
      --# global in out Buffers.State, PCBs, Bound_PCBs;
   is
      Dst_IP : IPaddrs.IPaddr;
      Dst_Port : Port_T;

      Netif : AIP.EID;
      --  Outbound interface

      NH_IP : IPaddrs.IPaddr;
      --  Next hop

      Buf_Entry_Pload : System.Address;
      --  Buf's payload on entry, to be restored for callers

      Lerr : AIP.Err_T;
      --  Local error status

   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      Buf_Entry_Pload := Buffers.Buffer_Payload (Buf);

      Dst_IP   := PCBs (PCB).IPCB.Remote_IP;
      Dst_Port := PCBs (PCB).Remote_Port;

      --  ERR_USE if we have no clear destination endpoint. Otherwise, route
      --  to find the proper network interface for Dst_IP and send. ERR_RTE if
      --  no route could be found.

      if not PCBs (PCB).Connected
        or else IPaddrs.Any (Dst_IP)
        or else Dst_Port = NOPORT
      then
         Err := AIP.ERR_USE;

      else
         IP.IP_Route (Dst_IP, NH_IP, Netif);
         if Netif = NIF.IF_NOID then
            Err := AIP.ERR_RTE;
         else
            UDP_Send_To_If (PCB, Buf, Dst_IP, NH_IP, Dst_Port, Netif, Err);
         end if;
      end if;

      Buffers.Buffer_Set_Payload (Buf, Buf_Entry_Pload, Lerr);
      if AIP.No (Err) then
         Err := Lerr;
      end if;
   end UDP_Send;

   ----------------------
   --  UDP_Disconnect  --
   ----------------------

   procedure UDP_Disconnect (PCB : PCB_Id)
      --# global in out PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      --  Reset the remote address association and flag PCB as unconnected

      PCBs (PCB).IPCB.Remote_IP := IPaddrs.IP_ADDR_ANY;
      PCBs (PCB).Remote_Port    := 0;
      PCBs (PCB).Connected      := False;
   end UDP_Disconnect;

   -------------------
   --  UDP_Release  --
   -------------------

   procedure UDP_Release (PCB : PCB_Id)
      --# global in out PCBs, Bound_PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      PCB_Unlink (PCB);
      PCBs (PCB).Link := PCB_UNUSED;
   end UDP_Release;

   --------------------
   --  UDP_Callback  --
   --------------------

   procedure UDP_Callback
     (Evk  : UDP_Event_Kind;
      PCB  : PCB_Id;
      Cbid : Callbacks.CBK_Id)
      --# global in out PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      case Evk is
         when UDP_RECV => PCBs (PCB).RECV_Cb := Cbid;
      end case;
   end UDP_Callback;

   ---------------
   -- UDP_Udata --
   ---------------

   procedure UDP_Set_Udata (PCB : PCB_Id; Udata : System.Address)
      --# global in out PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      PCBs (PCB).Udata := Udata;
   end UDP_Set_Udata;

   function UDP_Udata (PCB : PCB_Id) return System.Address
      --# global in PCBs;
   is
   begin
      pragma Assert (PCB in Valid_PCB_Ids);

      return PCBs (PCB).Udata;
   end UDP_Udata;

end AIP.UDP;
