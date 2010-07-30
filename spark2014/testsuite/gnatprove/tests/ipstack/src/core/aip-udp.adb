------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.Inet;

with AIP.ICMP;
with AIP.ICMPH;
with AIP.IP;
with AIP.IPH;
with AIP.UDPH;

package body AIP.UDP
   --# own State is IPCBs, UPCBs, Bound_PCBs;
is

   ---------------------
   -- Data structures --
   ---------------------

   type UDP_PCB is record
      RECV_Cb     : Callbacks.CBK_Id;
      --  Callback id for UDP_RECV events
   end record;

   UDP_PCB_Initializer : constant UDP_PCB :=
                           UDP_PCB'(RECV_Cb => Callbacks.NOCB);

   subtype Valid_UDP_PCB_Id is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_UDP_PCB - 1;

   subtype UDP_IPCB_Array is PCBs.IP_PCB_Array (Valid_UDP_PCB_Id);
   type UDP_UPCB_Array is array (Valid_UDP_PCB_ID) of UDP_PCB;

   IPCBs : UDP_IPCB_Array;
   UPCBs : UDP_UPCB_Array;

   Bound_PCBs : AIP.EID;

   ----------------
   --  UDP_Init  --
   ----------------

   procedure UDP_Init
      --# global out IPCBs, UPCBs, Bound_PCBs;
   is
   begin
      --  Initialize all the PCBs, marking them unused, and initialize the list
      --  of bound PCBs as empty.

      IPCBs := UDP_IPCB_Array'(others => PCBs.IP_PCB_Initializer);
      UPCBs := UDP_UPCB_Array'(others => UDP_PCB_Initializer);

      Bound_PCBs := PCBs.NOPCB;
   end UDP_Init;

   ---------------
   -- PCB_Clear --
   ---------------

   procedure PCB_Clear (PCB : PCBs.PCB_Id)
      --# global in out IPCBs, UPCBs;
   is
   begin
      IPCBs (PCB) := PCBs.IP_PCB_Initializer;
      UPCBs (PCB) := UDP_PCB_Initializer;

      IPCBs (PCB).Link := PCBs.NOPCB;
   end PCB_Clear;

   -------------
   -- UDP_New --
   -------------

   procedure UDP_New (Id : out PCBs.PCB_Id)
      --# global in out IPCBs, UPCBs;
   is
   begin
      PCBs.Allocate_PCB (IPCBs, Id);

      if Id /= PCBs.NOPCB then
         PCB_Clear (Id);
         IPCBs (Id).TTL := Config.UDP_TTL;
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
      Uhdr  : System.Address) return AIP.EID
      --# global in IPCBs, Bound_PCBs;
   is
      PCB : AIP.EID;
   begin
      PCBs.Find_PCB
        (Local_IP    => IPH.IPH_Dst_Address (Ihdr),
         Local_Port  => UDPH.UDPH_Dst_Port (Uhdr),
         Remote_IP   => IPH.IPH_Src_Address (Ihdr),
         Remote_Port => UDPH.UDPH_Src_Port (Uhdr),
         PCB_List    => Bound_PCBs,
         PCB_Pool    => IPCBs,
         PCB         => PCB);
      return PCB;
   end UDP_PCB_For;

   ---------------
   -- UDP_Input --
   ---------------

   procedure UDP_Input
     (Buf   : Buffers.Buffer_Id;
      Netif : NIF.Netif_Id)
      --# global in out Buffers.State, Bound_PCBs, IPCBs, UPCBs;

   is
      Ihdr, Uhdr : System.Address;

      Err : AIP.Err_T;
      PCB : AIP.EID := PCBs.NOPCB;
   begin
      --  Latch address of IP header and retrieve a UDP view of the incoming
      --  datagram.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP_To_UDP (Buf, Uhdr, Err);

      --  Find the best UDP PCB to take the datagram, verify the checksum
      --  and adjust the payload offset before passing up to the applicative
      --  callback.

      if AIP.No (Err) then
         PCB := UDP_PCB_For (Ihdr, Uhdr);

         if PCB /= PCBs.NOPCB
           or else
             IPaddrs.Same (NIF.NIF_Addr (Netif), IPH.IPH_Dst_Address (Ihdr))
         then
            null;  --  ??? cksum check here
         end if;

         if PCB = PCBs.NOPCB then

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
        and then PCB /= PCBs.NOPCB
        and then UPCBs (PCB).RECV_Cb /= Callbacks.NOCB
      then
         --  Skip UDP header and perform upcall to application

         Buffers.Buffer_Header (Buf, -UDP_HLEN, Err);

         UDP_Event
           (UDP_Event_T'(Kind => UDP_RECV,
                         Buf  => Buf,
                         IP   => IPH.IPH_Src_Address (Ihdr),
                         Port => UDPH.UDPH_Src_Port (Uhdr)),
            PCB,
            UPCBs (PCB).RECV_Cb);

         --  No free if buffer passed to application???
      else
         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end UDP_Input;

   ------------------
   -- PCB_Bound_To --
   ------------------

   function PCB_Bound_To (Port : PCBs.Port_T) return AIP.EID
      --# global in IPCBs, Bound_PCBs;
   is
      Pid : AIP.EID;
   begin
      Pid := Bound_PCBs;
      loop
         exit when Pid = PCBs.NOPCB or else IPCBs (Pid).Local_Port = Port;
         Pid := IPCBs (Pid).Link;
      end loop;
      return Pid;
   end PCB_Bound_To;

   --------------------
   -- Available_Port --
   --------------------

   function Available_Port return PCBs.Port_T
      --# global in IPCBs, Bound_PCBs;
   is
      Aport : PCBs.Port_T := PCBs.NOPORT;  --  Port found to be available
      Cport : PCBs.Port_T;                 --  Candidate port to examine
   begin
      Cport := Config.UDP_LOCAL_PORT_FIRST;
      loop
         exit when Aport /= PCBs.NOPORT
                     or else Cport > Config.UDP_LOCAL_PORT_LAST;
         if PCB_Bound_To (Cport) = PCBs.NOPCB then
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
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : PCBs.Port_T;
      Err        : out AIP.Err_T)
      --# global in out IPCBs, Bound_PCBs;
   is
      Rebind       : Boolean;
      Pid          : AIP.EID;
      Port_To_Bind : PCBs.Port_T;
   begin
      Err := AIP.NOERR;

      --  See if we're rebinding an already bound PCB, and/or if
      --  we're binding to the same addr/port as another bound PCB.

      Rebind := False;

      Pid := Bound_PCBs;
      while Pid /= PCBs.NOPCB and then AIP.No (Err) loop
         if Pid = PCB then
            Rebind := True;
         elsif not Config.UDP_SHARED_ENDPOINTS
           and then PCBs.Bound_To (IPCBs (Pid), Local_IP, Local_Port)
         then
            Err := AIP.ERR_USE;
         end if;
         Pid := IPCBs (Pid).Link;
      end loop;

      if AIP.No (Err) then

         --  Pick an available port if none was specified

         if Local_Port = PCBs.NOPORT then
            Port_To_Bind := Available_Port;
            if Port_To_Bind = PCBs.NOPORT then
               Err := AIP.ERR_MEM;
            end if;
         else
            Port_To_Bind := Local_Port;
         end if;

         --  Assign the local IP/port, and insert into the list of bound PCBs
         --  unless it was already there.

         IPCBs (PCB).Local_Port := Port_To_Bind;
         IPCBs (PCB).Local_IP := Local_IP;

         if not Rebind then
            IPCBs (PCB).Link := Bound_PCBs;
            Bound_PCBs := PCB;
         end if;
      end if;

   end UDP_Bind;

   --------------------
   -- PCB_Force_Bind --
   --------------------

   procedure PCB_Force_Bind (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
      --# global in out IPCBs, Bound_PCBs;
   is
      Local_IP : IPaddrs.IPaddr;
   begin
      if IPCBs (PCB).Local_Port = PCBs.NOPORT then
         Local_IP := IPCBs (PCB).Local_IP;
         UDP_Bind (PCB, Local_IP, PCBs.NOPORT, Err);
      else
         Err := AIP.NOERR;
      end if;
   end PCB_Force_Bind;

   ----------------
   -- PCB_Unlink --
   ----------------

   procedure PCB_Unlink (PCB : PCBs.PCB_Id)
      --# global in out IPCBs, Bound_PCBs;
   is
      Cur, Prev : AIP.EID;
   begin
      if PCB = Bound_PCBs then
         Bound_PCBs := IPCBs (PCB).Link;
      else
         Prev := PCBs.NOPCB;
         Cur := Bound_PCBs;

         while Cur /= PCBs.NOPCB and then PCB /= Cur loop
            Prev := Cur;
            Cur := IPCBs (Cur).Link;
         end loop;

         if Cur /= PCBs.NOPCB then
            pragma Assert (Prev /= PCBs.NOPCB);
            IPCBs (Prev).Link := IPCBs (Cur).Link;
            IPCBs (Cur).Link := PCBs.NOPCB;
         end if;
      end if;
   end PCB_Unlink;

   -------------------
   --  UDP_Connect  --
   -------------------

   procedure UDP_Connect
     (PCB         : PCBs.PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : PCBs.Port_T;
      Err         : out AIP.Err_T)
      --# global in out IPCBs, Bound_PCBs;
   is
   begin
      --  Make sure we have a local binding in place, so that the (dummy)
      --  connection has two well identified endpoints.

      PCB_Force_Bind (PCB, Err);

      --  If all went fine, assign the remote endpoint components and flag
      --  the PCB as connected. Either PCB had a local_port set on entry,
      --  meaning bound already, or we bound it ourselves.  In both cases,
      --  it should already be present in the list of active PCBs.

      if AIP.No (Err) then
         IPCBs (PCB).Remote_IP   := Remote_IP;
         IPCBs (PCB).Remote_Port := Remote_Port;
         IPCBs (PCB).Connected   := True;
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
           (Offset => HLEN_To_IP,
            Size   => UDP_HLEN,
            Kind   => Buffers.SPLIT_BUF,
            Buf    => Ubuf);

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
     (PCB      : PCBs.PCB_Id;
      Buf      : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      NH_IP    : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;
      Netif    : NIF.Netif_Id;
      Err      : out AIP.Err_T)
      --# global in out Buffers.State, IPCBs, Bound_PCBs;
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

         if not IPaddrs.Any (IPCBs (PCB).Local_IP)
           and then not IPaddrs.Same (IPCBs (PCB).Local_IP, Src_IP)
         then
            Err := AIP.ERR_VAL;
         else
            Uhdr := Buffers.Buffer_Payload (Ubuf);
            Ulen := Buffers.Buffer_Tlen (Ubuf);

            UDPH.Set_UDPH_Src_Port (Uhdr, IPCBs (PCB).Local_Port);
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

            --  Initialize checksum field to 0 to compute the actual checksum

            UDPH.Set_UDPH_Checksum (Uhdr, 0);

            --  Compute checksum, including pseudo-header

            UDPH.Set_UDPH_Checksum
              (Uhdr, not Checksum.Sum (Ubuf, Buffers.Buffer_Tlen (Ubuf)));

            --  Remove pseudo-header

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
               IPCBs (PCB).TTL,
               IPCBs (PCB).TOS,
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
     (PCB : PCBs.PCB_Id;
      Buf : Buffers.Buffer_Id;
      Err : out AIP.Err_T)
      --# global in out Buffers.State, IPCBs, Bound_PCBs;
   is
      Dst_IP : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;

      Netif : AIP.EID;
      --  Outbound interface

      NH_IP : IPaddrs.IPaddr;
      --  Next hop

      Buf_Entry_Pload : System.Address;
      --  Buf's payload on entry, to be restored for callers

      Lerr : AIP.Err_T;
      --  Local error status

   begin
      Buf_Entry_Pload := Buffers.Buffer_Payload (Buf);

      Dst_IP   := IPCBs (PCB).Remote_IP;
      Dst_Port := IPCBs (PCB).Remote_Port;

      --  ERR_USE if we have no clear destination endpoint. Otherwise, route
      --  to find the proper network interface for Dst_IP and send. ERR_RTE if
      --  no route could be found.

      if not IPCBs (PCB).Connected
        or else IPaddrs.Any (Dst_IP)
        or else Dst_Port = PCBs.NOPORT
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

   procedure UDP_Disconnect (PCB : PCBs.PCB_Id)
      --# global in out IPCBs;
   is
   begin
      --  Reset the remote address association and flag PCB as unconnected

      IPCBs (PCB).Remote_IP   := IPaddrs.IP_ADDR_ANY;
      IPCBs (PCB).Remote_Port := 0;
      IPCBs (PCB).Connected   := False;
   end UDP_Disconnect;

   -------------------
   --  UDP_Release  --
   -------------------

   procedure UDP_Release (PCB : PCBs.PCB_Id)
      --# global in out IPCBs, UPCBs, Bound_PCBs;
   is
   begin
      PCB_Unlink (PCB);
      IPCBs (PCB).Link := PCBs.PCB_UNUSED;
   end UDP_Release;

   --------------------
   --  UDP_Callback  --
   --------------------

   procedure UDP_Callback
     (Evk  : UDP_Event_Kind;
      PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id)
      --# global in out UPCBs;
   is
   begin
      case Evk is
         when UDP_RECV => UPCBs (PCB).RECV_Cb := Cbid;
      end case;
   end UDP_Callback;

   ---------------
   -- UDP_Udata --
   ---------------

   procedure UDP_Set_Udata (PCB : PCBs.PCB_Id; Udata : System.Address)
      --# global in out IPCBs;
   is
   begin
      IPCBs (PCB).Udata := Udata;
   end UDP_Set_Udata;

   function UDP_Udata (PCB : PCBs.PCB_Id) return System.Address
      --# global in IPCBs;
   is
   begin
      return IPCBs (PCB).Udata;
   end UDP_Udata;

end AIP.UDP;
