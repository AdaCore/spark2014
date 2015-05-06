------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.Inet;

with AIP.ICMP;
with AIP.ICMPH;
with AIP.IPH;
with AIP.UDPH;

package body AIP.UDP with
  Refined_State => (State => (IPCBs, UPCBs, Bound_PCBs))
is

   -----------------------
   -- Local subprograms --
   -----------------------

   procedure PCB_Force_Bind (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
   --  Force a local binding on PCB if it isn't bound already.
   --
   --  ERR as UDP_Bind.
   with
     Global => (In_Out => (Bound_PCBs, IPCBs));

   ------------------------
   -- UDP_Send internals --
   ------------------------

   procedure Prepend_UDP_Header
     (Buf  : Buffers.Buffer_Id;
      Ubuf : out Buffers.Buffer_Id;
      Err  : out AIP.Err_T)
   --  Setup space for a UDP header before the data in Buf. See if there is
   --  enough room preallocated for this purpose, and adjust the payload
   --  pointer in this case. Prepend a separate buffer otherwise.
   --
   --  ERR_MEM if the operation failed. BUF is unchanged in this case.
   with
     Global => (In_Out => Buffers.State);

   procedure UDP_Send_To_If
     (PCB      : PCBs.PCB_Id;
      Buf      : Buffers.Buffer_Id;
      Dst_IP   : IPaddrs.IPaddr;
      NH_IP    : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;
      Netif    : NIF.Netif_Id;
      Err      : out AIP.Err_T)
   --  Send BUF to DST_IP/DST_PORT via next hop NH_IP through NETIF, acting
   --  for PCB. This involves prepending a UDP header in front of BUF.
   --
   --  ERR_VAL if PCB has a specific local IP set which differs from NETIF's.
   with
     Global => (In_Out => (Bound_PCBs, Buffers.State, IP.State, IPCBs));

   ---------------------
   -- Data structures --
   ---------------------

   UDP_HLEN : constant := UDPH.UDP_Header_Size / 8;
   --  Fixed length of a UDP header, in bytes

   type UDP_Callbacks is array (UDP_Event_Kind) of Callbacks.CBK_Id;

   type UDP_PCB is record
      Callbacks : UDP_Callbacks;
   end record;

   UDP_PCB_Initializer : constant UDP_PCB :=
     UDP_PCB'(Callbacks => UDP_Callbacks'(others => Callbacks.NOCB));

   subtype UDP_PCB_Index is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_UDP_PCB - 1;

   subtype UDP_IPCB_Array is PCBs.IP_PCB_Array (UDP_PCB_Index);
   type UDP_UPCB_Array is array (UDP_PCB_Index) of UDP_PCB;

   IPCBs : UDP_IPCB_Array;
   UPCBs : UDP_UPCB_Array;

   Bound_PCBs : AIP.EID;
   subtype UDP_PCB_Heads_Range is Natural range 1 .. 1;
   subtype UDP_PCB_Heads is PCBs.PCB_List (UDP_PCB_Heads_Range);

   --------------
   -- UDP_Init --
   --------------

   procedure UDP_Init with
     Refined_Global => (Output => (Bound_PCBs, IPCBs, UPCBs))
   is
   begin
      --  Initialize all the PCBs, marking them unused, and initialize the list
      --  of bound PCBs as empty.

      IPCBs := UDP_IPCB_Array'(others => PCBs.IP_PCB_Initializer);
      UPCBs := UDP_UPCB_Array'(others => UDP_PCB_Initializer);

      Bound_PCBs := PCBs.NOPCB;
   end UDP_Init;

   -------------
   -- UDP_New --
   -------------

   procedure UDP_New (PCB : out PCBs.PCB_Id) with
     Refined_Global => (In_Out => (IPCBs, UPCBs))
   is
   begin
      PCBs.Allocate (IPCBs, PCB);

      if PCB /= PCBs.NOPCB then
         IPCBs (PCB).TTL := Config.UDP_TTL;
         UPCBs (PCB) := UDP_PCB_Initializer;
      end if;
   end UDP_New;

   ---------------
   -- UDP_Input --
   ---------------

   procedure UDP_Input
     (Buf   : Buffers.Buffer_Id;
      Netif : NIF.Netif_Id)
   with
     Refined_Global => (Input  => (Bound_PCBs, IPCBs, UPCBs),
                        In_Out => Buffers.State)
   is
      Ihdr, Uhdr, PUhdr : System.Address;

      PUH_Buf  : Buffers.Buffer_Id;
      Err      : AIP.Err_T;
      PCB      : PCBs.PCB_Id := PCBs.NOPCB;
      Wildcard : Natural;
   begin
      --  Latch address of IP header and retrieve a UDP view of the incoming
      --  datagram.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP.Get_Next_Header
        (Buf,
         UDPH.UDP_Header_Size / 8,
         Uhdr,
         Err);

      --  Verify UDP checksum

      Buffers.Buffer_Alloc
        (0, UDPH.UDP_Pseudo_Header_Size / 8, Buffers.SPLIT_BUF, PUH_Buf);

      if PUH_Buf =  Buffers.NOBUF then
         Err := AIP.ERR_MEM;
      else
         PUhdr := Buffers.Buffer_Payload (PUH_Buf);

         UDPH.Set_UDPP_Src_Address (PUhdr, IPH.IPH_Src_Address (Ihdr));
         UDPH.Set_UDPP_Dst_Address (PUhdr, IPH.IPH_Dst_Address (Ihdr));
         UDPH.Set_UDPP_Zero        (PUhdr, 0);
         UDPH.Set_UDPP_Protocol    (PUhdr, IPH.IP_Proto_UDP);
         UDPH.Set_UDPP_Length      (PUhdr, UDPH.UDPH_Length (Uhdr));

         Buffers.Buffer_Chain (PUH_Buf, Buf);

         if not NIF.Offload (Netif, NIF.UDP_CS)
              and then Checksum.Sum (PUH_Buf, Buffers.Buffer_Tlen (PUH_Buf))
                         /= 16#ffff#
         then
            Err := AIP.ERR_VAL;
         end if;

         Buffers.Buffer_Blind_Free (PUH_Buf);
      end if;

      --  Search the best UDP PCB to take the datagram. ERR_VAL and ICMP port
      --  unreachable if none could be found.

      if AIP.No (Err) then
         pragma Warnings (Off, "unused assignment to ""Wildcard""");
         PCBs.Find_PCB_In_List
           (Local_IP    => IPH.IPH_Dst_Address (Ihdr),
            Local_Port  => UDPH.UDPH_Dst_Port  (Uhdr),
            Remote_IP   => IPH.IPH_Src_Address (Ihdr),
            Remote_Port => UDPH.UDPH_Src_Port  (Uhdr),
            PCB_Head    => Bound_PCBs,
            PCB_Pool    => IPCBs,
            PCB         => PCB,
            Wildcard    => Wildcard);
         pragma Warnings (On, "unused assignment to ""Wildcard""");

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

      --  If we have a taker, trigger UDP_EVENT_RECV.
      --  Releasing the buffer is the app's responsibility in this case (???).

      if AIP.No (Err) and then PCB /= PCBs.NOPCB  then

         --  Skip UDP header and perform upcall to application

         Buffers.Buffer_Header (Buf, -UDP_HLEN, Err);

         if AIP.No (Err) then
            UDP_Event
              (UDP_Event_T'(Kind => UDP_EVENT_RECV,
                            Buf  => Buf,
                            IP   => IPH.IPH_Src_Address (Ihdr),
                            Port => UDPH.UDPH_Src_Port (Uhdr)),
               PCB,
               UPCBs (PCB).Callbacks (UDP_EVENT_RECV));
         end if;
      end if;
   end UDP_Input;

   --------------
   -- UDP_Bind --
   --------------

   procedure UDP_Bind
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : PCBs.Port_T;
      Err        : out AIP.Err_T)
   with
     Refined_Global => (In_Out => (Bound_PCBs, IPCBs))
   is
   begin
      PCBs.Bind_PCB
        (PCB        => PCB,
         Local_IP   => Local_IP,
         Local_Port => Local_Port,
         PCB_Heads  => UDP_PCB_Heads'(1 => Bound_PCBs),
         PCB_Pool   => IPCBs,
         Err        => Err);

      if AIP.No (Err) then
         IPCBs (PCB).Link := Bound_PCBs;
         Bound_PCBs := PCB;
      end if;
   end UDP_Bind;

   --------------------
   -- PCB_Force_Bind --
   --------------------

   procedure PCB_Force_Bind (PCB : PCBs.PCB_Id; Err : out AIP.Err_T) is
   begin
      if IPCBs (PCB).Local_Port = PCBs.NOPORT then
         UDP_Bind (PCB, IPaddrs.IP_ADDR_ANY, PCBs.NOPORT, Err);
      else
         Err := AIP.NOERR;
      end if;
   end PCB_Force_Bind;

   -----------------
   -- UDP_Connect --
   -----------------

   procedure UDP_Connect
     (PCB         : PCBs.PCB_Id;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : PCBs.Port_T;
      Err         : out AIP.Err_T)
   with
     Refined_Global => (In_Out => (Bound_PCBs, IPCBs))
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

   ------------------------
   -- UDP_Send internals --
   ------------------------

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

            --  Checksum computation and assignment

            UDPH.Set_UDPH_Checksum (Uhdr, 0);

            if not NIF.Offload (Netif, NIF.UDP_CS) then

               --  Expose room for a temporary pseudo-header and fill it in.
               --  The length we store here is that of the original datagram.
               --  We expect room to be available already, anticipated for the
               --  IP and link layers downstack and not yet filled with
               --  anything of use.

               pragma Warnings (Off, "unused assignment to ""Err""");
               Buffers.Buffer_Header
                 (Ubuf, UDPH.UDP_Pseudo_Header_Size / 8, Err);
               pragma Assert (No (Err));
               pragma Warnings (On, "unused assignment to ""Err""");

               PUhdr := Buffers.Buffer_Payload (Ubuf);
               UDPH.Set_UDPP_Src_Address (PUhdr, Src_IP);
               UDPH.Set_UDPP_Dst_Address (PUhdr, Dst_IP);
               UDPH.Set_UDPP_Zero        (PUhdr, 0);
               UDPH.Set_UDPP_Protocol    (PUhdr, IPH.IP_Proto_UDP);
               UDPH.Set_UDPP_Length      (PUhdr, Ulen);

               --  Compute the actual checksum, including pseudo-header. This
               --  relies on the above initialization of the checksum field to
               --  zero.

               UDPH.Set_UDPH_Checksum
                 (Uhdr, not Checksum.Sum (Ubuf, Buffers.Buffer_Tlen (Ubuf)));

               --  Remove pseudo-header

               pragma Warnings (Off, "unused assignment to ""Err""");
               Buffers.Buffer_Header
                 (Ubuf, -UDPH.UDP_Pseudo_Header_Size / 8, Err);
               pragma Assert (No (Err));
               pragma Warnings (On, "unused assignment to ""Err""");

            end if;

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

            --  Note: once the packet has been passed to the link layer,
            --  we should not touch it anymore (in particular we should not
            --  clobber the payload pointer, which now points to the link
            --  level header).

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
   with
     Refined_Global => (Input  => IP.FIB,
                        In_Out => (Bound_PCBs, Buffers.State, IP.State, IPCBs))
   is
      Dst_IP : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;

      Netif : AIP.EID;
      --  Outbound interface

      NH_IP : IPaddrs.IPaddr;
      --  Next hop

   begin
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
   end UDP_Send;

   --------------------
   -- UDP_Disconnect --
   --------------------

   procedure UDP_Disconnect (PCB : PCBs.PCB_Id) with
     Refined_Global => (In_Out => IPCBs)
   is
   begin
      --  Reset the remote address association and flag PCB as unconnected

      IPCBs (PCB).Remote_IP   := IPaddrs.IP_ADDR_ANY;
      IPCBs (PCB).Remote_Port := 0;
      IPCBs (PCB).Connected   := False;
   end UDP_Disconnect;

   -----------------
   -- UDP_Release --
   -----------------

   procedure UDP_Release (PCB : PCBs.PCB_Id) with
     Refined_Global => (In_Out => (Bound_PCBs, IPCBs))
   is
   begin
      PCBs.Unlink (PCB, Bound_PCBs, IPCBs);
      IPCBs (PCB).Link := PCBs.PCB_UNUSED;
   end UDP_Release;

   ------------------
   -- UDP_Callback --
   ------------------

   procedure UDP_Callback
     (Evk  : UDP_Event_Kind;
      PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id)
   with
     Global => (In_Out => UPCBs)
   is
   begin
      UPCBs (PCB).Callbacks (Evk) := Cbid;
   end UDP_Callback;

   -----------------
   -- On_UDP_Recv --
   -----------------

   procedure On_UDP_Recv
     (PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id)
   with
     Refined_Global => (In_Out => UPCBs)
   is
   begin
      UDP_Callback (UDP_EVENT_RECV, PCB, Cbid);
   end On_UDP_Recv;

   ---------------
   -- UDP_Udata --
   ---------------

   procedure UDP_Set_Udata (PCB : PCBs.PCB_Id; Udata : System.Address) with
     Refined_Global => (In_Out => IPCBs)
   is
   begin
      IPCBs (PCB).Udata := Udata;
   end UDP_Set_Udata;

   function UDP_Udata (PCB : PCBs.PCB_Id) return System.Address with
     Refined_Global => IPCBs
   is
   begin
      return IPCBs (PCB).Udata;
   end UDP_Udata;

end AIP.UDP;
