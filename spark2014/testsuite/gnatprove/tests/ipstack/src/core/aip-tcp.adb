------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.Conversions;
with AIP.Inet;
with AIP.IP;
with AIP.IPH;
with AIP.TCPH;
with AIP.Time_Types;

package body AIP.TCP
--# own State is Boot_Time, TCP_Ticks, IPCBs, TPCBs, Bound_PCBs,
--#     Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
is

   ---------------------
   -- Data structures --
   ---------------------

   type TCP_State is
     (Closed,
      Listen,
      Syn_Sent,
      Syn_Received,
      Established,
      Fin_Wait_1,
      Fin_Wait_2,
      Close_Wait,
      Closing,
      Last_Ack,
      Time_Wait);

   type TCP_Callbacks is array (TCP_Event_Kind) of Callbacks.CBK_Id;

   type TCP_PCB is record
      State : TCP_State;
      --  TCP state of this connection.
      --  Can be changed only by procedure Set_State below, which verifies
      --  the legality of the requested transition.

      Active : Boolean;
      --  Set True if connection was initiated with an active open (i.e. went
      --  through the SYN-SENT state).

      --  Connection parameters

      Local_MSS  : AIP.U16_T; --  Maximum segment size for receiving
      Remote_MSS : AIP.U16_T; --  Maximum segment size for sending

      --  Send sequence variables

      SND_UNA  : AIP.M32_T; --  Send unacknowledged
      SND_NXT  : AIP.M32_T; --  Send next
      SND_WND  : AIP.M32_T; --  Send window
      SND_UP   : AIP.M32_T; --  Send urgent pointer
      SND_WL1  : AIP.M32_T; --  Segment sequence number for last window update
      SND_WL2  : AIP.M32_T; --  Segment ack number for last window update
      ISS      : AIP.M32_T; --  Initial send sequence number

      NSS      : AIP.M32_T; --  Next send sequence number
      SND_BUF  : AIP.U16_T; --  Available send buffer room

      Dup_Acks : AIP.U8_T;  --  Consecutive duplicated acks

      --  Receive sequence variables

      RCV_NXT  : AIP.M32_T; --  Receive next
      RCV_WND  : AIP.M32_T; --  Receive window
      RCV_UP   : AIP.M32_T; --  Receive urgent pointer
      IRS      : AIP.M32_T; --  Initial receive sequence number

      --  Note: RCV_WND and SND_WND are kept as 32-bit values even though the
      --  Window field in the TCP header is just 16 bits wide for two reasons:
      --    - it makes it more convenient to do arithmetics involving sequence
      --      numbers and window sizes;
      --    - the window size in bytes may exceed 65_535 if a window scaling
      --      option is negotiated (in which case the Window field must be
      --      shifted left by the window scaling factor to obtain the actual
      --      xxx_WND value).

      --  Slow start

      CWND     : AIP.M32_T; --  Congestion window
      SSTHRESH : AIP.M32_T; --  Slow start threshold

      --  Round-trip average and standard deviation estimators for computation
      --  of retransmit timeout (in TCP 500 ms ticks).

      Poll_Ticks : AIP.M32_T;
      Poll_Ivl   : AIP.M32_T;
      --  TCP ticks value when polling callback was last called, and polling
      --  interval (0 for no polling).

      Persist_Ticks   : AIP.S16_T;
      Persist_Backoff : AIP.S16_T;
      --  TCP ticks value for persist timer (-1 if not running, ticks count
      --  since last reset if running, and current backoff count (0 if not
      --  running).

      Retransmit_Ticks : AIP.S16_T;
      Retransmit_Count : AIP.U8_T;
      --  TCP ticks value for retransmit timer (-1 if timer not running, ticks
      --  count since last if running), and retransmit count

      Watchdog_Ticks : AIP.M32_T;
      --  TCP ticks for watchdog timer (used for idle/keepalive, stuck PCB, and
      --  2MSL TIME_WAIT).

      RTT_Seq    : AIP.M32_T;
      --  Sequence number of segment used for RTT estimation

      RTT_Ticks  : AIP.M32_T;
      --  TCP ticks value when segment used for RTT estimation was sent

      RTT_Average : AIP.S16_T;
      RTT_Stddev  : AIP.S16_T;
      RTO         : AIP.S16_T;

      --  Transmission queues

      Send_Queue  : Buffers.Packet_Queue;
      --  Packets to be sent out

      Unack_Queue : Buffers.Packet_Queue;
      --  Sent packets waiting for ack/retransmit

      --  Cached next hop information

      Next_Hop_IP    : IPaddrs.IPaddr;
      Next_Hop_Netif : AIP.EID;

      --  Receive queue

      Refused_Packet : Buffers.Buffer_Id;
      --  At most one segment of deferred data is kept pending for delivery
      --  to application.

      --  User (application) callbacks

      Callbacks : TCP_Callbacks;
   end record;

   TCP_PCB_Initializer : constant TCP_PCB :=
                           TCP_PCB'(State            => Closed,

                                    Active           => False,

                                    Local_MSS        => 0,
                                    Remote_MSS       => 0,

                                    SND_UNA          => 0,
                                    SND_NXT          => 0,
                                    SND_WND          => 0,
                                    SND_UP           => 0,
                                    SND_WL1          => 0,
                                    SND_WL2          => 0,
                                    ISS              => 0,

                                    NSS              => 0,
                                    SND_BUF          => Config.TCP_SND_BUF,

                                    Dup_Acks         => 0,

                                    RCV_NXT          => 0,
                                    RCV_WND          => Config.TCP_WINDOW,
                                    RCV_UP           => 0,
                                    IRS              => 0,

                                    CWND             => 0,
                                    SSTHRESH         => 0,

                                    Poll_Ticks       => 0,
                                    Poll_Ivl         => 0,

                                    Persist_Ticks    => 0,
                                    Persist_Backoff  => 0,

                                    Retransmit_Ticks => -1,
                                    Retransmit_Count => 0,

                                    Watchdog_Ticks   => 0,

                                    RTT_Seq          => 0,
                                    RTT_Ticks        => 0,
                                    RTT_Average      => 0,
                                    RTT_Stddev       => 0,
                                    RTO              => 0,

                                    Send_Queue       =>
                                      Buffers.Empty_Packet_Queue,
                                    Unack_Queue      =>
                                      Buffers.Empty_Packet_Queue,

                                    Next_Hop_IP      => IPaddrs.IP_ADDR_ANY,
                                    Next_Hop_Netif   => NIF.IF_NOID,

                                    Refused_Packet   => Buffers.NOBUF,

                                    Callbacks        =>
                                      TCP_Callbacks'(others =>
                                                       Callbacks.NOCB));

   subtype Valid_TCP_PCB_Id is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_TCP_PCB - 1;

   subtype TCP_IPCB_Array is PCBs.IP_PCB_Array (Valid_TCP_PCB_Id);
   type TCP_TPCB_Array is array (Valid_TCP_PCB_Id) of TCP_PCB;

   Boot_Time : Time_Types.Time;
   --  Startup time of TCP subsystem

   TCP_Ticks : AIP.M32_T;
   --  Current TCP time counter (TCP_Hz ticks per second)

   TCP_Hz    : constant := 2;
   --  TCP timer frequency (do not change)

   --  Persist timer parameters, in TCP ticks (500 ms)

   Initial_Persist_Backoff : constant := 3/2 * TCP_Hz;  -- 1.5 s
   Max_Persist_Backoff     : constant := 60 * TCP_Hz;   -- 60 s

   --  Timeouts, in TCP ticks

   Fin_Wait_Timeout     : constant := 20 * TCP_Hz; -- 20 s
   Syn_Received_Timeout : constant := 20 * TCP_Hz; -- 20 s

   IPCBs : TCP_IPCB_Array;
   TPCBs : TCP_TPCB_Array;

   Bound_PCBs     : PCBs.PCB_Id;
   Listen_PCBs    : PCBs.PCB_Id;
   Active_PCBs    : PCBs.PCB_Id;
   Time_Wait_PCBs : PCBs.PCB_Id;
   subtype TCP_PCB_Heads_Range is Natural range 1 .. 4;
   subtype TCP_PCB_Heads is PCBs.PCB_List (TCP_PCB_Heads_Range);

   --  Type used to carry around information about a received segment

   type Segment is record
      Buf  : Buffers.Buffer_Id;
      --  Underlying packet buffer

      Ihdr : System.Address;
      --  IP header

      Thdr : System.Address;
      --  TCP header

      Len  : AIP.U16_T;
      --  Segment length (including SYN, payload and FIN)

      Seq  : AIP.M32_T;
      Ack  : AIP.M32_T;
      --  Sequence number and ack number

      --  TCP options

      MSS : AIP.U16_T;
      --  MSS option (0 if not present)

      Window_Scale : AIP.U8_T;
      --  Window scaling factor option (0 if not present)
   end record;

   --  function Initial_Sequence_Number
   --    (Local_IP    : IPaddrs.IPaddr;
   --     Local_Port  : PCBs.Port_T;
   --     Remote_IP   : IPaddrs.IPaddr;
   --     Remote_Port : PCBs.Port_T) return AIP.M32_T
   --  Determine an appropriate initial sequence number for a connection whose
   --  socket identifiers are given.

   --  procedure TCP_Seg_Len
   --    (Buf : Buffers.Buffer_Id;
   --     Seg_Len : out AIP.M32_T);
   --  Return the TCP segment length for the TCP segment in Buf. Note: this
   --  needs to modify transiently Buffers.State, which is restored prior to
   --  return, but this counts as a side effect anyway for SPARK's purposes,
   --  so this can't be a function.

   --  procedure TCP_Receive
   --    (PCB : PCBs.PCB_Id;
   --     Seg : Segment;
   --     Err : out AIP.Err_T);
   --  Process an incmoming segment, once the relevant PCB has been identified

   --  procedure Update_RTT_Estimator
   --    (TPCB : in out TCP_PCB;
   --     Meas : AIP.S16_T);
   --  Update the RTT estimator using the given RTT measurement, as per
   --  Jacobson paper.

   --  procedure Process_Ack (PCB : PCBs.PCB_Id; Seg : Segment);
   --  Process received ack in Seg

   --  procedure Deliver_Segment
   --    (PCB : PCBs.PCB_Id;
   --     Buf : Buffers.Buffer_Id);
   --  Attempt to deliver pending refused data and/or new segment in Buf to
   --  application.

   --  procedure Setup_PCB
   --    (PCB         : PCBs.PCB_Id;
   --     Local_IP    : IPaddrs.IPaddr;
   --     Local_Port  : PCBs.Port_T;
   --     Remote_IP   : IPaddrs.IPaddr;
   --     Remote_Port : PCBs.Port_T;
   --     Err         : out AIP.Err_T);
   --  Common setup procedure shared by active and passive opens

   --  procedure Set_State
   --    (PCB   : PCBs.PCB_Id;
   --     State : TCP_State);
   --  Sets PCB's state to the given state, handling chaining on the
   --  appropriate PCB lists. Verifies that PCB is not already in that State,
   --  and that the transition is legal.

   --  procedure TCP_Segment_For
   --    (Ptr  : System.Address;
   --     Len  : AIP.U16_T;
   --     Copy : Boolean;
   --     Tbuf : out Buffers.Buffer_Id);
   --  Allocate a packet (segment) suitable for the TCP transmission of Len
   --  bytes of Data starting at Ptr. Copy controls whether data needs to be
   --  copied within buffer space or if we just keep a reference to it.
   --  Header space is allocated for all the protocol layers downstream,
   --  without options. Packet_Info is set to designate the TCP header, and
   --  Payload designates the data. None of the TCP header fields is set by
   --  this operation.

   --  procedure TCP_Enqueue
   --    (PCB     : PCBs.PCB_Id;
   --     Control : Boolean;
   --     Data    : System.Address;
   --     Len     : AIP.M32_T;
   --     Copy    : Boolean;
   --     Push    : Boolean;
   --     Syn     : Boolean;
   --     Err     : out AIP.Err_T)
   --  Request push onto the Send_Queue for later output by TCP_Output.
   --  If Control is False, Data/Len, Copy and Push operate as for user data
   --  passed to TCP_Write, with segments cut to be MSS bytes max each.
   --  If Control is True, Data/Len designates a TCP options area, sent over
   --  an empty segment with the SYN and ACK header bits set according to the
   --  Syn and Ack arguments.
   --
   --  ERR_MEM on segment memory allocation failure

   --  procedure TCP_Force_Bind
   --    (PCB : PCBs.PCB_Id;
   --     Err : out AIP.Err_T);
   --  TCP_Bind PCB on IP_ADDR_ANY and an ephemeral port if it is not
   --  bound already.

   --  procedure TCP_Send_Segment
   --    (Tbuf : Buffers.Buffer_Id; PCB : PCBs.PCB_Id);
   --  Helper for TCP_Output. Send segment held in Tbuf over IP for PCB.

   --  procedure Retransmit_Timeout (PCB : PCBs.PCB_Id);
   --  Handle expiration of the retransmit timer on PCB

   --  procedure Send_Window_Probe (PCB : PCBs.PCB_Id);
   --  Send window probe for PCB (expiration of persist timer)

   -----------------
   -- TCP_Seg_Len --
   -----------------

   procedure TCP_Seg_Len (Buf : Buffers.Buffer_Id; Seg_Len : out AIP.M32_T)
   --# global in out Buffers.State;
   is
      Saved_Payload : System.Address;
      Thdr          : System.Address;
      Err           : AIP.Err_T;
   begin
      Saved_Payload := Buffers.Buffer_Payload (Buf);
      Thdr := Buffers.Packet_Info (Buf);
      Buffers.Buffer_Set_Payload (Buf, Thdr, Err);
      pragma Assert (AIP.No (Err));

      Seg_Len := AIP.M32_T (Buffers.Buffer_Tlen (Buf))
                   - 4 * AIP.M32_T (TCPH.TCPH_Data_Offset (Thdr))
                   + AIP.M32_T (TCPH.TCPH_Syn (Thdr))
                   + AIP.M32_T (TCPH.TCPH_Fin (Thdr));
      Buffers.Buffer_Set_Payload (Buf, Saved_Payload, Err);
      pragma Assert (AIP.No (Err));
   end TCP_Seg_Len;

   ------------
   -- Seq_Lt --
   ------------

   function Seq_Lt (L, R : AIP.M32_T) return Boolean is
   begin
      return L - R > AIP.M32_T'(2 ** 31);
   end Seq_Lt;

   ------------
   -- Seq_Le --
   ------------

   function Seq_Le (L, R : AIP.M32_T) return Boolean is
   begin
      return R - L < AIP.M32_T'(2 ** 31);
   end Seq_Le;

   ---------------
   -- Seq_Range --
   ---------------

   function Seq_Range (L, S, R : AIP.M32_T) return Boolean is
   begin
      return Seq_Le (L, S) and then Seq_Lt (S, R);
   end Seq_Range;

   ----------------------
   -- TCP_Send_Segment --
   ----------------------

   procedure TCP_Send_Segment
     (Tbuf       : Buffers.Buffer_Id;
      PCB        : PCBs.PCB_Id;
      Retransmit : Boolean)
   --# global in IPCBs, TPCBs; in out IP.State, Buffers.State;
   is
      PThdr, Thdr : System.Address;
      Tlen : AIP.U16_T;

      Src_IP, Dst_IP : IPaddrs.IPaddr;
      Err : AIP.ERR_T;
   begin
      Src_IP := IPCBs (PCB).Local_IP;
      Dst_IP := IPCBs (PCB).Remote_IP;

      --  Beware that we might have two kinds of packets here (from the send
      --  queue): those with data copied in, standalone with headers in a
      --  single buffer, and those with data referenced, as a hdrs-->data_ref
      --  buffer chain.

      --  Fetch the TCP header address from Packet_Info, then set the payload
      --  pointer to designate that for checksum computation and IP processing
      --  downstream.

      Thdr := Buffers.Packet_Info (Tbuf);
      Buffers.Buffer_Set_Payload (Tbuf, Thdr, Err);
      pragma Assert (AIP.No (Err));

      --  Fill in the ACK number field and advertise our receiving window
      --  size.

      TCPH.Set_TCPH_Ack_Num (Thdr, TPCBs (PCB).RCV_NXT);
      TCPH.Set_TCPH_Window  (Thdr, AIP.U16_T (TPCBs (PCB).RCV_WND));

      --  Compute checksum and pass down to IP, assuming the current payload
      --  pointer designates the TCP header.

      --  Capture the current segment length, then expose room for a temporary
      --  pseudo-header and fill it in. We expect that much room to be
      --  available as part of the space allocation for the protocol headers
      --  (TCP and down) issued when this segment was constructed.

      Tlen := Buffers.Buffer_Tlen (Tbuf);
      Buffers.Buffer_Header (Tbuf, TCPH.TCP_Pseudo_Header_Size / 8, Err);
      pragma Assert (AIP.No (Err));

      PThdr := Buffers.Buffer_Payload (Tbuf);
      TCPH.Set_TCPP_Src_Address (PThdr, Src_IP);
      TCPH.Set_TCPP_Dst_Address (PThdr, Dst_IP);
      TCPH.Set_TCPP_Zero        (PThdr, 0);
      TCPH.Set_TCPP_Protocol    (PThdr, IPH.IP_Proto_TCP);
      TCPH.Set_TCPP_Length      (PThdr, Tlen);

      --  Compute the actual checksum, including pseudo-header. This relies on
      --  a preliminary initialization of the checksum field.

      TCPH.Set_TCPH_Checksum (Thdr, 0);
      TCPH.Set_TCPH_Checksum
        (Thdr, not Checksum.Sum (Tbuf, Buffers.Buffer_Tlen (Tbuf)));

      --  Remove pseudo-header

      Buffers.Buffer_Header (Tbuf, -TCPH.TCP_Pseudo_Header_Size / 8, Err);
      pragma Assert (AIP.No (Err));

      if not Retransmit then

         --  New segment: reset retransmit timer

         TPCBs (PCB).Retransmit_Ticks := 0;
         TPCBs (PCB).Retransmit_Count := 0;

      else
         --  Here when retransmitting an already sent segment

         TPCBs (PCB).Retransmit_Count := TPCBs (PCB).Retransmit_Count + 1;
      end if;

      --  Finally hand out segment to IP

      IP.IP_Output_If
        (Buf    => Tbuf,
         Src_IP => Src_IP,
         Dst_IP => Dst_IP,
         NH_IP  => TPCBs (PCB).Next_Hop_IP,
         TTL    => IPCBs (PCB).TTL,
         TOS    => IPCBs (PCB).TOS,
         Proto  => IPH.IP_Proto_TCP,
         Netif  => TPCBs (PCB).Next_Hop_Netif,
         Err    => Err);
      pragma Assert (AIP.No (Err));
   end TCP_Send_Segment;

   ----------------
   -- TCP_Output --
   ----------------

   procedure TCP_Output (PCB : PCBs.PCB_Id; Ack_Now : Boolean)
   --# global in out IPCBs, TPCBs, IP.State, Buffers.State;
   is
      Seg     : Buffers.Buffer_Id;
      Seg_Len : AIP.M32_T;
      --  Segment to be processed (first buffer of segment packet) and
      --  associated length

      This_WND : AIP.M32_T;
      --  Window size for this output sequence: minimum of send window
      --  and congestion window.

      Thdr : System.Address;

      N_ACKs_Q : AIP.U32_T;
      --  Number of ACKs sent together with segments from the Send_Queue.

   begin

      --  Default the PCB local IP to that of the interface if it's not set
      --  already, used for checksum computations later on.

      if IPCBs (PCB).Local_IP = IPaddrs.IP_ADDR_ANY then
         IPCBs (PCB).Local_IP := NIF.NIF_Addr (TPCBs (PCB).Next_Hop_Netif);
      end if;

      --  Send every segment in the send queue that fits within the current
      --  window. Count the number of ACKs sent along the way.

      N_ACKs_Q := 0;
      This_WND := AIP.M32_T'Min (TPCBs (PCB).SND_WND, TPCBs (PCB).CWND);

      loop
         Seg := Buffers.Head_Packet (TPCBs (PCB).Send_Queue);
         exit when Seg = Buffers.NOBUF;

         --  Here we have a candidate segment.

         --  See if it fits the send window, as delimited by SND_UNA and
         --  This_WND.  Out of Send_Queue, we expect the segment not to have
         --  been sent already, hence the start of segment to be past the
         --  start of window. Then we check if the segment ends before of
         --  beyond the end of window.

         Thdr := Buffers.Packet_Info (Seg);

         pragma Assert (TCPH.TCPH_Seq_Num (Thdr) >= TPCBs (PCB).SND_UNA);

         TCP_Seg_Len (Seg, Seg_Len);
         exit when Seq_Le (TCPH.TCPH_Seq_Num (Thdr) + Seg_Len,
                           TPCBs (PCB).SND_UNA + This_WND);

         --  ??? exit when Nagle blob

         --  Now prepare and send current segment.

         --  We always piggyback an ACK number in Send_Segment but only (and
         --  always) really ACK when not in SYN_SENT state.

         if TPCBs (PCB).State /= Syn_Sent then
            TCPH.Set_TCPH_Ack (Thdr, 1);
            N_ACKs_Q := N_ACKs_Q + 1;
         end if;

         TCP_Send_Segment
           (Tbuf       => Seg,
            PCB        => PCB,
            Retransmit => False);

         --  Remove packet from the Send_Queue and bump SND_NXT

         Buffers.Remove_Packet
           (Buffers.Transport, TPCBs (PCB).Send_Queue, Seg);

         TPCBs (PCB).SND_NXT := TPCBs (PCB).SND_NXT + Seg_Len;

      end loop;

      --  If we need to ACK this time around and haven't already piggybacked
      --  while processing the send queue, setup and send an empty ACK segment
      --  now.

      if ACK_Now and then N_ACKs_Q = 0 then
         Buffers.Buffer_Alloc
           (Size   => TCPH.TCP_Header_Size / 8,
            Offset => Inet.HLEN_To (Inet.IP_LAYER),
            Kind   => Buffers.SPLIT_BUF,
            Buf    => Seg);

         Thdr := Buffers.Buffer_Payload (Seg);

         TCPH.Set_TCPH_Data_Offset (Thdr, 5);

         TCPH.Set_TCPH_Src_Port (Thdr, IPCBs (PCB).Local_Port);
         TCPH.Set_TCPH_Dst_Port (Thdr, IPCBs (PCB).Remote_Port);
         TCPH.Set_TCPH_Seq_Num  (Thdr, TPCBs (PCB).SND_NXT);
         TCPH.Set_TCPH_Reserved (Thdr, 0);

         TCPH.Set_TCPH_Urg (Thdr, 0);
         TCPH.Set_TCPH_Psh (Thdr, 0);
         TCPH.Set_TCPH_Syn (Thdr, 0);
         TCPH.Set_TCPH_Fin (Thdr, 0);
         TCPH.Set_TCPH_Ack (Thdr, 1);

         TCP_Send_Segment
           (Tbuf       => Seg,
            PCB        => PCB,
            Retransmit => False);

         Buffers.Buffer_Blind_Free (Seg);
      end if;

   end TCP_Output;

   ---------------------
   -- Deliver_Segment --
   ---------------------

   procedure Deliver_Segment
     (PCB : PCBs.PCB_Id;
      Buf : Buffers.Buffer_Id)
   --# global in out TPCBs, IPCBs, IP.State, Buffers.State;
   is
      Saved_Payload : System.Address;
      D_Buf : Buffers.Buffer_Id;
      D_Len : AIP.M32_T;
      Err   : AIP.Err_T;
   begin
      --  Retry deferred data, if any, and then proceed to deliver new segment,
      --  if any. If deferred data was present and was refused again, the new
      --  segment (if present) is dropped.

      if TPCBs (PCB).Refused_Packet /= Buffers.NOBUF then
         D_Buf := TPCBs (PCB).Refused_Packet;
      else
         D_Buf := Buf;
      end if;

      loop
         Saved_Payload := Buffers.Buffer_Payload (D_Buf);

         --  Note: here we expect the application to know about chained buffers
         --  and retrieve all data from the delivered buffer chain.

         D_Len := AIP.M32_T (Buffers.Buffer_Tlen (D_Buf));
         TCP_Event
           (Ev   => TCP_Event_T'(Kind => TCP_EVENT_RECV,
                                 Len  => D_Len,
                                 Buf  => D_Buf,
                                 Addr => IPaddrs.IP_ADDR_ANY,
                                 Port => PCBs.NOPORT,
                                 Err  => AIP.NOERR),
            PCB  => PCB,
            Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_RECV),
            Err  => Err);

         if AIP.No (Err) then
            Buffers.Buffer_Blind_Free (D_Buf);
            TPCBs (PCB).Refused_Packet := Buffers.NOBUF;

            --  Open receive window

            TPCBs (PCB).RCV_WND :=
              AIP.M32_T'Min (TPCBs (PCB).RCV_WND + D_Len, Config.TCP_Window);

            if TCPH.TCPH_Fin (Buffers.Packet_Info (D_Buf)) = 1 then
               pragma Assert (D_Buf = Buf);

               --  Got FIN: signal end of stream to the application by
               --  delivering an empty buffer, unless already done above

               if D_Len /= 0 then
                  TCP_Event
                    (Ev   => TCP_Event_T'(Kind => TCP_EVENT_RECV,
                                          Len  => 0,
                                          Buf  => Buffers.NOBUF,
                                          Addr => IPaddrs.IP_ADDR_ANY,
                                          Port => PCBs.NOPORT,
                                          Err  => AIP.NOERR),
                     PCB  => PCB,
                     Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_RECV),
                     Err  => Err);
               end if;
            end if;

            if D_Buf /= Buf then

               --  More data to deliver

               D_Buf := Buf;

            else
               --  All data delivered with no error: try sending data and ack
               --  as needed

               TCP_Output (PCB => PCB, Ack_Now => False);
            end if;

         else
            --  Got error: restore payload pointer, park refused segment in PCB
            --  for later retry, and drop further segment if present.

            Buffers.Buffer_Set_Payload (D_Buf, Saved_Payload, Err);
            pragma Assert (AIP.No (Err));

            TPCBs (PCB).Refused_Packet := D_Buf;
            if Buf /= D_Buf then
               Buffers.Buffer_Blind_Free (Buf);
            end if;
         end if;
         exit when D_Buf = Buffers.NOBUF or else AIP.Any (Err);
      end loop;
   end Deliver_Segment;

   ----------------------------
   -- Initial_Sequence_Numer --
   ----------------------------

   function Initial_Sequence_Number
     (Local_IP    : IPaddrs.IPaddr;
      Local_Port  : PCBs.Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : PCBs.Port_T) return AIP.M32_T
   --# global in Boot_Time;
   is
   begin
      --  Should do much better than that to select a truly random ISN???
      return AIP.M32_T (Time_Types.Now)
        + (AIP.M32_T (Boot_Time)
             xor (Local_IP * 7
                + Remote_IP * 13
                + AIP.M32_T (Local_Port) * AIP.M32_T (Remote_Port)));
   end Initial_Sequence_Number;

   --------------------------
   -- Update_RTT_Estimator --
   --------------------------

   procedure Update_RTT_Estimator
     (TPCB  : in out TCP_PCB;
      Meas  : AIP.S16_T)
   is
      M : AIP.S16_T;
   begin
      M := Meas;

      --  Update average estimator

      M := M - TPCB.RTT_Average / 8;
      TPCB.RTT_Average := TPCB.RTT_Average + M;

      --  Update standard deviation estimator

      M := (abs M) - TPCB.RTT_Stddev / 4;
      TPCB.RTT_Stddev := TPCB.RTT_Stddev + M;

      --  Set new retransmit timeout

      TPCB.RTO := TPCB.RTT_Average / 8 + TPCB.RTT_Stddev;
   end Update_RTT_Estimator;

   ---------------
   -- Set_State --
   ---------------

   procedure Set_State
     (PCB   : PCBs.PCB_Id;
      State : TCP_State)
   --# global in out TPCBs, IPCBs,
   --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
   begin
      pragma Assert (TPCBs (PCB).State /= State);

      case TPCBs (PCB).State is
         when Closed =>
            pragma Assert (State = Listen or else State = Syn_Sent);

            pragma Assert (IPCBs (PCB).Local_Port /= PCBs.NOPORT);

            PCBs.Unlink
              (PCB      => PCB,
               PCB_Head => Bound_PCBs,
               PCB_Pool => IPCBs);

            if State = Listen then
               PCBs.Prepend
                 (PCB      => PCB,
                  PCB_Head => Listen_PCBs,
                  PCB_Pool => IPCBs);
            else
               PCBs.Prepend
                 (PCB      => PCB,
                  PCB_Head => Active_PCBs,
                  PCB_Pool => IPCBs);
            end if;

         when Listen =>
            pragma Assert (State = Syn_Received or else State = Closed);

            --  No transition from Listen to Syn_Sent

            if State = Closed then
               PCBs.Unlink
                 (PCB      => PCB,
                  PCB_Head => Listen_PCBs,
                  PCB_Pool => IPCBs);
            end if;

         when Syn_Sent =>

            --  We allow going directly from Syn_Sent to Closed for the case
            --  of the user closing a half-open connection.

            pragma Assert (State = Syn_Received
                           or else State = Established
                           or else State = Closed);

            if State = Closed then
               PCBs.Unlink
                 (PCB      => PCB,
                  PCB_Head => Active_PCBs,
                  PCB_Pool => IPCBs);
            end if;

         when Syn_Received =>

            --  Similarly an incoming RST may abort an half-open passive
            --  connection.

            pragma Assert (State = Established
                           or else State = Fin_Wait_1
                           or else State = Closed);

            if State = Closed then
               PCBs.Unlink
                 (PCB      => PCB,
                  PCB_Head => Active_PCBs,
                  PCB_Pool => IPCBs);
            end if;

         when Established =>
            pragma Assert (State = Fin_Wait_1 or else State = Close_Wait);
            null;

         when Fin_Wait_1 =>
            pragma Assert (State = Fin_Wait_2 or else State = Closing);
            null;

         when Fin_Wait_2 =>
            pragma Assert (State = Time_Wait);
            null;

         when Close_Wait =>
            pragma Assert (State = Last_Ack);
            null;

         when Closing =>
            pragma Assert (State = Time_Wait);
            null;

         when Last_Ack | Time_Wait =>
            pragma Assert (State = Closed);
            PCBs.Unlink
              (PCB      => PCB,
               PCB_Head => Active_PCBs,
               PCB_Pool => IPCBs);
      end case;

      TPCBs (PCB).State := State;
   end Set_State;

   --------------
   -- TCP_Init --
   --------------

   procedure TCP_Init
   --# global out Boot_Time, TCP_Ticks, IPCBs, TPCBs, Bound_PCBs, Listen_PCBs,
   --#            Active_PCBs, Time_Wait_PCBs;
   is
   begin
      --  Record boot time to serve as local secret for generation of ISN

      Boot_Time := Time_Types.Now;
      TCP_Ticks := 0;

      --  Initialize all the PCBs, marking them unused, and initialize the list
      --  of bound PCBs as empty.

      IPCBs := TCP_IPCB_Array'(others => PCBs.IP_PCB_Initializer);
      TPCBs := TCP_TPCB_Array'(others => TCP_PCB_Initializer);

      Bound_PCBs     := PCBs.NOPCB;
      Listen_PCBs    := PCBs.NOPCB;
      Active_PCBs    := PCBs.NOPCB;
      Time_Wait_PCBs := PCBs.NOPCB;
   end TCP_Init;

   ------------------
   -- TCP_Send_Rst --
   ------------------

   procedure TCP_Send_Rst
     (Src_IP   : IPaddrs.IPaddr;
      Src_Port : PCBs.Port_T;
      Dst_IP   : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;
      Ack      : Boolean;
      Seq_Num  : AIP.M32_T;
      Ack_Num  : AIP.M32_T;
      Err      : out AIP.Err_T)
   is
   begin
      null;
      --  TBD???
   end TCP_Send_Rst;

   ---------------
   -- TCP_Udata --
   ---------------

   procedure TCP_Set_Udata (PCB : PCBs.PCB_Id; Udata : System.Address)
   --# global in out IPCBs;
   is
   begin
      IPCBs (PCB).Udata := Udata;
   end TCP_Set_Udata;

   function TCP_Udata (PCB : PCBs.PCB_Id) return System.Address
   --# global in IPCBs;
   is
   begin
      return IPCBs (PCB).Udata;
   end TCP_Udata;

   --------------
   -- TCP_Bind --
   --------------

   procedure TCP_Bind
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : AIP.U16_T;
      Err        : out AIP.Err_T)
   --# global in out IPCBs, Bound_PCBs; in TPCBs, Listen_PCBs, Active_PCBs,
   --#               Time_Wait_PCBs;
   is
   begin
      if TPCBs (PCB).State /= Closed then
         Err := AIP.ERR_USE;
      else
         PCBs.Bind_PCB
           (PCB        => PCB,
            Local_IP   => Local_IP,
            Local_Port => Local_Port,
            PCB_Heads  =>
              TCP_PCB_Heads'(1 => Listen_PCBs,
                             2 => Bound_PCBs,
                             3 => Active_PCBs,
                             4 => Time_Wait_PCBs),
            PCB_Pool   => IPCBs,
            Err        => Err);

         if AIP.No (Err) then
            PCBs.Prepend
              (PCB      => PCB,
               PCB_Head => Bound_PCBs,
               PCB_Pool => IPCBs);
         end if;
      end if;
   end TCP_Bind;

   --------------------
   -- TCP_Force_Bind --
   --------------------

   procedure TCP_Force_Bind
     (PCB : PCBs.PCB_Id;
      Err : out AIP.Err_T)
   is
   begin
      if IPCBs (PCB).Local_Port = PCBs.NOPORT then
         TCP_Bind (PCB, IPaddrs.IP_ADDR_ANY, PCBs.NOPORT, Err);
      else
         Err := AIP.NOERR;
      end if;
   end TCP_Force_Bind;

   ------------------
   -- TCP_Callback --
   ------------------

   procedure TCP_Callback
     (Evk  : TCP_Event_Kind;
      PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id)
   --# global in out TPCBs;
   is
   begin
      TPCBs (PCB).Callbacks (Evk) := Cbid;
   end TCP_Callback;

   -------------------
   -- TCP_Listen_BL --
   -------------------

   procedure TCP_Listen_BL
     (PCB     : PCBs.PCB_Id;
      Backlog : AIP.U8_T;
      Err     : out AIP.Err_T)
   --# global in out IPCBs, TPCBs, Bound_PCBs, Listen_PCBs;
   --#        in Active_PCBs, Time_Wait_PCBs;
   is
      pragma Unreferenced (Backlog);
   begin
      pragma Assert (PCB /= PCBs.NOPCB);

      --  First bind PCB if necessary

      TCP_Force_Bind (PCB, Err);

      if AIP.No (Err) then
         pragma Assert (IPCBs (PCB).Local_Port /= PCBs.NOPORT);

         case TPCBs (PCB).State is
            when Closed =>
               Set_State (PCB, Listen);

            when Listen =>
               null;

            when others =>
               Err := AIP.ERR_ISCONN;
         end case;
      end if;
   end TCP_Listen_BL;

   ----------------
   -- TCP_Listen --
   ----------------

   procedure TCP_Listen (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
   --# global in out IPCBs, TPCBs, Bound_PCBs, Listen_PCBs;
   --#        in Active_PCBs, Time_Wait_PCBs;
   is
   begin
      TCP_Listen_BL (PCB, Config.TCP_DEFAULT_LISTEN_BACKLOG, Err);
   end TCP_Listen;

   -------------
   -- TCP_New --
   -------------

   procedure TCP_New (PCB : out PCBs.PCB_Id)
   --# global in out IPCBs, TPCBs;
   is
   begin
      PCBs.Allocate (IPCBs, PCB);

      if PCB /= PCBs.NOPCB then
         IPCBs (PCB).TTL := Config.TCP_TTL;
         TPCBs (PCB) := TCP_PCB_Initializer;
      end if;
   end TCP_New;

   --------------
   -- TCP_Free --
   --------------

   procedure TCP_Free (PCB : PCBs.PCB_Id)
   --# global in out IPCBs, TPCBs,
   --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
   begin
      if TPCBs (PCB).State = Closed
        and then IPCBs (PCB).Local_Port /= PCBs.NOPORT
      then
         PCBs.Unlink (PCB      => PCB,
                      PCB_Head => Bound_PCBs,
                      PCB_Pool => IPCBs);
      else
         Set_State (PCB, Closed);
      end if;

      IPCBs (PCB) := PCBs.IP_PCB_Initializer;
   end TCP_Free;

   ------------------
   -- On_TCP_Accept --
   ------------------

   procedure On_TCP_Accept
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_ACCEPT, PCB, Cb);
   end On_TCP_Accept;

   ------------------
   -- TCP_Accepted --
   ------------------

   procedure TCP_Accepted (PCB : PCBs.PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Accepted;

   --------------------------
   -- TCP_Data_Segment_For --
   --------------------------

   procedure TCP_Data_Segment_For
     (Ptr  : System.Address;
      Len  : AIP.U16_T;
      Tbuf : out Buffers.Buffer_Id)
   --# global in out Buffers.State;
   is
      Err : AIP.Err_T;
   begin
      --  Allocate one data buffer to hold user data + protocol headers,
      --  memorize the TCP header location and copy data at payload addr

      Buffers.Buffer_Alloc
        (Size   => Len,
         Offset => Inet.HLEN_To (Inet.TRANSPORT_LAYER),
         Kind   => Buffers.SPLIT_BUF,
         Buf    => Tbuf);

      if Tbuf /= Buffers.NOBUF then

         Buffers.Buffer_Header (Tbuf, TCPH.TCP_Header_Size / 8, Err);
         Buffers.Set_Packet_Info (Tbuf, Buffers.Buffer_Payload (Tbuf));
         Buffers.Buffer_Header (Tbuf, -TCPH.TCP_Header_Size / 8, Err);

         Conversions.Memcpy
           (Dst => Buffers.Buffer_Payload (Tbuf),
            Src => Ptr,
            Len => Natural (Len));
      end if;
   end TCP_Data_Segment_For;

   -------------------------
   -- TCP_Ref_Segment_For --
   -------------------------

   procedure TCP_Ref_Segment_For
     (Ptr  : System.Address;
      Len  : AIP.U16_T;
      Tbuf : out Buffers.Buffer_Id)
   --# global in out Buffers.State;
   is
      Hbuf : Buffers.Buffer_Id;
      --  Separate buffer for protocol headers

   begin
      --  Allocate one ref buffer to reference the user data, a distinct
      --  one for protocol headers. Chain them together and memorize the
      --  TCP header address.

      Buffers.Ref_Buffer_Alloc
        (Size     => Len,
         Offset   => 0,
         Data_Ref => Ptr,
         Buf      => Tbuf);

      if Tbuf /= Buffers.NOBUF then

         Buffers.Buffer_Alloc
           (Size   => TCPH.TCP_Header_Size / 8,
            Offset => Inet.HLEN_To (Inet.IP_LAYER),
            Kind   => Buffers.SPLIT_BUF,
            Buf    => Hbuf);

         if Hbuf = Buffers.NOBUF then
            Buffers.Buffer_Blind_Free (Tbuf);
            Tbuf := Buffers.NOBUF;
         else
            Buffers.Buffer_Chain (Tail => Tbuf, Head => Hbuf);
            Tbuf := Hbuf;
            Buffers.Set_Packet_Info (Tbuf, Buffers.Buffer_Payload (Hbuf));
         end if;
      end if;
   end TCP_Ref_Segment_For;

   ---------------------
   -- TCP_Segment_For --
   ---------------------

   procedure TCP_Segment_For
     (Ptr   : System.Address;
      Len   : AIP.U16_T;
      Copy  : Boolean;
      Tbuf  : out Buffers.Buffer_Id)
   --# global in out Buffers.State;
   is
   begin
      pragma Assert (Len > 0);

      if Copy then
         TCP_Data_Segment_For (Ptr, Len, Tbuf);
      else
         TCP_Ref_Segment_For (Ptr, Len, Tbuf);
      end if;
   end TCP_Segment_For;

   -----------------
   -- TCP_Enqueue --
   -----------------

   procedure TCP_Enqueue
     (PCB     : PCBs.PCB_Id;
      Control : Boolean;
      Data    : System.Address;
      Len     : AIP.M32_T;
      Copy    : Boolean;
      Push    : Boolean;
      Syn     : Boolean;
      Fin     : Boolean;
      Err     : out AIP.Err_T)
   --# global in out TPCBs, Buffers.State; in IPCBs;
   is

      Left : AIP.M32_T;
      Ptr  : System.Address;
      --  Amount of Data still unassigned a TCP segment, and start address
      --  of this data. This designates user data or TCP options according
      --  to Control.

      Dlen : AIP.U16_T;
      --  Amount of user or options Data carried by the current segment

      Toff : AIP.U4_T;
      --  TCP user data offset for current segment, in words.
      --  5 + length of options.

      SegQ : Buffers.Packet_Queue;
      --  Local packet queue, to hold segments temporarily until we know we
      --  can allocate all those we need.

      NSS  : AIP.M32_T;
      --  Next Send Sequence number, which we'll assign to the next segment to
      --  be queued.

      Tbuf : Buffers.Buffer_Id;
      Thdr : System.Address;
      --  One segment we build and its TCP header

   begin

      Err := AIP.NOERR;

      if Len > AIP.M32_T (TPCBs (PCB).SND_BUF) then
         Err := AIP.ERR_MEM;
      else

         --  Cut DATA into segments according to MSS, queuing into the
         --  local queue until we know we can allocate all we need.

         Left := Len;
         Ptr  := Data;

         NSS := TPCBs (PCB).NSS;

         SegQ := Buffers.Empty_Packet_Queue;

         if not Control then
            Toff := 5;
         else
            Toff := 5 + AIP.U4_T (Len / 4);
         end if;

         while Left > 0 loop

            if Left > AIP.M32_T (TPCBs (PCB).Remote_MSS) then
               Dlen := TPCBs (PCB).Remote_MSS;
            else
               Dlen := AIP.U16_T (Left);
            end if;

            --  Compute now what will be left to process afterwards, which
            --  tells us if this is the last segment for this time around.

            Left := Left - AIP.M32_T (Dlen);

            --  If we have a single non-control segment that fits in spare
            --  non-control room in the last segment of Send_Queue, request
            --  a headerless buffer that we'll chain there.

            --  ??? Implement me

            TCP_Segment_For (Ptr, Dlen, Copy, Tbuf);
            exit when Tbuf = Buffers.NOBUF;

            --  We have a new segment to queue at this point. Assign the TCP
            --  header fields, except ACK and WND determined at output time.

            Thdr := Buffers.Packet_Info (Tbuf);

            TCPH.Set_TCPH_Data_Offset (Thdr, Toff);

            TCPH.Set_TCPH_Src_Port (Thdr, IPCBs (PCB).Local_Port);
            TCPH.Set_TCPH_Dst_Port (Thdr, IPCBs (PCB).Remote_Port);
            TCPH.Set_TCPH_Seq_Num  (Thdr, NSS);
            TCPH.Set_TCPH_Reserved (Thdr, 0);

            TCPH.Set_TCPH_Urg (Thdr, 0);

            TCPH.Set_TCPH_Syn (Thdr, Boolean'Pos (Syn));
            TCPH.Set_TCPH_Fin (Thdr, Boolean'Pos (Fin));
            TCPH.Set_TCPH_Psh (Thdr, Boolean'Pos (Left = 0 and then Push));

            --  Push on the temporary queue and prepare to proceed with the
            --  next segment.

            Buffers.Append_Packet
              (Layer => Buffers.Transport,
               Buf   => Tbuf,
               Queue => SegQ);

            Ptr := Conversions.Ofs (Ptr, Integer (Dlen));
            NSS := NSS + AIP.M32_T (Dlen);
         end loop;

         --  If we have had any kind of trouble so far, release what we got
         --  and bail out. Otherwise proceed further.

         if AIP.Any (Err) then

            while not Buffers.Empty (SegQ) loop
               Buffers.Remove_Packet
                 (Layer => Buffers.Transport,
                  Queue => SegQ,
                  Buf   => Tbuf);
               Buffers.Buffer_Blind_Free (Tbuf);
            end loop;

         else

            --  Push the temporary queue on the Send_Queue for later
            --  processing by TCP_Output.

            if not Buffers.Empty (SegQ) then
               Buffers.Append_Packet
                 (Layer => Buffers.Transport,
                  Buf   => Buffers.Head_Packet (SegQ),
                  Queue => TPCBs (PCB).Send_Queue);
            end if;

            --  Memorize what the next segment sequence should be

            TPCBs (PCB).NSS := NSS;

         end if;

      end if;

   end TCP_Enqueue;

   ----------------------
   -- TCP_Send_Control --
   ----------------------

   procedure TCP_Send_Control
     (PCB : PCBs.PCB_Id;
      Syn : Boolean;
      Fin : Boolean;
      Err : out AIP.Err_T)
   --# global in out TPCBs, Buffers.State; in IPCBs;
   is
   begin
      TCP_Enqueue (PCB     => PCB,
                   Control => True,
                   Data    => System.Null_Address,
                   Len     => 0,
                   Copy    => True,
                   Push    => False,
                   Syn     => Syn,
                   Fin     => Fin,
                   Err     => Err);
   end TCP_Send_Control;

   ---------------
   -- Setup_PCB --
   ---------------

   procedure Setup_PCB
     (PCB         : PCBs.PCB_Id;
      Local_IP    : IPaddrs.IPaddr;
      Local_Port  : PCBs.Port_T;
      Remote_IP   : IPaddrs.IPaddr;
      Remote_Port : PCBs.Port_T;
      Err         : out AIP.Err_T)
   --# global in out Boot_Time, IPCBs, TPCBs; in IP.FIB;
   is
      Next_Hop_IP    : IPaddrs.IPaddr;
      Next_Hop_Netif : NIF.Netif_Id;
   begin
      IPCBs (PCB).Local_IP    := Local_IP;
      IPCBs (PCB).Local_Port  := Local_Port;
      IPCBs (PCB).Remote_IP   := Remote_IP;
      IPCBs (PCB).Remote_Port := Remote_Port;

      --  Find and cache return path information

      IP.IP_Route (IPCBs (PCB).Remote_IP, Next_Hop_IP, Next_Hop_Netif);
      TPCBs (PCB).Next_Hop_IP    := Next_Hop_IP;
      TPCBs (PCB).Next_Hop_Netif := Next_Hop_Netif;

      if TPCBs (PCB).Next_Hop_Netif = NIF.IF_NOID then
         --  No route to host: bail out

         Err := AIP.ERR_RTE;

      else
         --  Choose our ISN and set connection state variables

         TPCBs (PCB).ISS :=
           Initial_Sequence_Number
             (Local_IP    => IPCBs (PCB).Local_IP,
              Local_Port  => IPCBs (PCB).Local_Port,
              Remote_IP   => IPCBs (PCB).Remote_IP,
              Remote_Port => IPCBs (PCB).Remote_Port);

         TPCBs (PCB).NSS := TPCBs (PCB).ISS;

         TPCBs (PCB).SND_NXT := TPCBs (PCB).ISS;
         TPCBs (PCB).SND_UNA := TPCBs (PCB).ISS - 1;
         TPCBs (PCB).SND_WND := Config.TCP_WINDOW;

         TPCBs (PCB).RCV_WND := Config.TCP_WINDOW;

         --  Set MSS using MTU of next hop interface, accounting for IP and TCP
         --  headers, and provisioning for 20 bytes of options.

         TPCBs (PCB).Local_MSS :=
           NIF.NIF_MTU (TPCBs (PCB).Next_Hop_Netif)
           - IPH.IP_Header_Size / 8
           - TCPH.TCP_Header_Size / 8
           - 20;
      end if;
   end Setup_PCB;

   -----------------
   -- TCP_Connect --
   -----------------

   procedure TCP_Connect
     (PCB  : PCBs.PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
      Cb   : Callbacks.CBK_Id;
      Err  : out AIP.Err_T)
   is
   begin

      --  Check that we're in proper state for this operation and make sure
      --  the local end of the connection is well identified.

      if TPCBs (PCB).State /= Closed then
         Err := ERR_USE;
      else
         TCP_Force_Bind (PCB, Err);
      end if;

      --  Compute an initial Next Send Sequence number and setup the
      --  relevant connection state variables.

      if AIP.No (Err) then
         Setup_PCB
           (PCB         => PCB,
            Local_IP    => IPCBs (PCB).Local_IP,
            Local_Port  => IPCBs (PCB).Local_Port,
            Remote_IP   => Addr,
            Remote_Port => Port,
            Err         => Err);
      end if;

      --  Send the active-open SYN segment, switch to Syn_Sent state
      --  and setup the TCP_EVENT_CONNECT callback identifier

      if AIP.No (Err) then
         TCP_Send_Control
           (PCB => PCB,
            Syn => True,
            Fin => False,
            Err => Err);
      end if;

      if AIP.No (Err) then
         Set_State (PCB, Syn_Sent);
         TCP_Callback (TCP_EVENT_CONNECT, PCB, Cb);
      end if;
   end TCP_Connect;

   ---------------
   -- TCP_Write --
   ---------------

   procedure TCP_Write
     (PCB   : PCBs.PCB_Id;
      Data  : System.Address;
      Len   : AIP.M32_T;
      Copy  : Boolean;
      Push  : Boolean;
      Err   : out AIP.Err_T)
   --# global in out TPCBs, Buffers.State; in IPCBs;
   is
   begin
      case TPCBs (PCB).State is
         when Established | Close_Wait | Syn_Sent | Syn_Received =>
            if Len = 0 then
               Err := AIP.NOERR;
            else
               TCP_Enqueue (PCB     => PCB,
                            Control => False,
                            Data    => Data,
                            Len     => Len,
                            Copy    => Copy,
                            Push    => Push,
                            Syn     => False,
                            Fin     => False,
                            Err     => Err);
            end if;
         when others =>
            Err := AIP.ERR_USE;
      end case;
   end TCP_Write;

   -----------------
   -- Process_Ack --
   -----------------

   procedure Process_Ack (PCB : PCBs.PCB_Id; Seg : Segment)
   --# global in out Buffers.State, TPCBs, IPCBs, Bound_PCBs, Listen_PCBs,
   --#               Active_PCBs, Time_Wait_PCBs; in TCP_Ticks;
   is
      Packet : Buffers.Buffer_Id;
      Thdr   : System.Address;
      Len    : AIP.M32_T;
      Err    : AIP.Err_T;

      CWND_Increment : AIP.M32_T;
   begin
      if Seq_Lt (Seg.Ack, TPCBs (PCB).SND_UNA) then
         --  Duplicated ack

         TPCBs (PCB).Dup_Acks := TPCBs (PCB).Dup_Acks + 1;

         --  Ignore duplicated ack, unless it's the third in a row, in which
         --  case we initiate a fast retransmit without waiting for the
         --  retransmit timer to expire.

         --  Fast retransmit /fast recovery are not implemented yet???
         null;

      else
         --  Invalid ack for a seqno not sent yet should have been discarded

         pragma Assert (Seq_Le (Seg.Ack, TPCBs (PCB).SND_NXT));

         TPCBs (PCB).Dup_Acks := 0;

         TPCBs (PCB).SND_UNA := Seg.Ack;

         --  Perform slow start and congestion avoidance

         if TPCBs (PCB).CWND < TPCBs (PCB).SSTHRESH then
            CWND_Increment := AIP.M32_T (TPCBs (PCB).Remote_MSS);
         else
            CWND_Increment :=
              AIP.M32_T (TPCBs (PCB).Remote_MSS * TPCBs (PCB).Remote_MSS)
                / TPCBs (PCB).CWND;
         end if;

         TPCBs (PCB).CWND := TPCBs (PCB).CWND + CWND_Increment;

         --  Update RTT estimator

         if TPCBs (PCB).RTT_Seq = Seg.Ack then
            Update_RTT_Estimator
              (TPCB => TPCBs (PCB),
               Meas => AIP.S16_T (TCP_Ticks - TPCBs (PCB).RTT_Ticks));
            TPCBs (PCB).RTT_Seq := 0;
         end if;

         --  Purge entirely acked segments

         loop
            Packet := Buffers.Head_Packet (TPCBs (PCB).Unack_Queue);
            exit when Packet = Buffers.NOBUF;

            Thdr := Buffers.Packet_Info (Packet);
            TCP_Seg_Len (Packet, Len);
            exit when not Seq_Le (TCPH.TCPH_Seq_Num (Thdr) + Len, Seg.Ack);

            --  Segment entirely acked: notify user and remove from queue.
            --  Note: For a segment carrying a FIN, we do not signal it sent
            --  if the ack covers all of the data but not the FIN flag.

            TCP_Event
              (Ev   => TCP_Event_T'(Kind => TCP_EVENT_SENT,
                                    Len  =>
                                      Len
                                    - AIP.M32_T (TCPH.TCPH_Syn (Thdr))
                                    - AIP.M32_T (TCPH.TCPH_Fin (Thdr)),
                                    Buf  => Buffers.NOBUF,
                                    Addr => IPaddrs.IP_ADDR_ANY,
                                    Port => PCBs.NOPORT,
                                    Err  => AIP.ERR_RST),
               PCB  => PCB,
               Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_SENT),
               Err  => Err);

            if TCPH.TCPH_Fin (Thdr) = 1 then
               case TPCBs (PCB).State is
                  when Fin_Wait_1 =>
                     Set_State (PCB, Fin_Wait_2);

                  when Closing =>
                     Set_State (PCB, Time_Wait);

                  when Last_Ack =>
                     TCP_Free (PCB);

                  when Time_Wait =>

                     --  Ack retransmitted FIN

                     TCP_Send_Control
                       (PCB => PCB,
                        Syn => False,
                        Fin => False,
                        Err => Err);

                     --  Restart 2MSL timeout???

                  when others =>
                     --  Can't happen (we sent a FIN)

                     null;
               end case;
            end if;

            --  Note: the following call leaves Packet unchanged (but removes
            --  it from the head of Unack_Queue).

            Buffers.Remove_Packet
              (Buffers.Transport, TPCBs (PCB).Unack_Queue, Packet);
         end loop;

         --  Update window if:
         --    Seg.Seq > WL1
         --    Seg.Seq = WL1 and Seg.Ack > WL2
         --    Seg.Seq = WL1 and Seg.Awk = WL2 and window grows

         if Seq_Lt (TPCBs (PCB).SND_WL1, Seg.Seq)
              or else
            (TPCBs (PCB).SND_WL1 = Seg.Seq
             and then (Seq_Lt (TPCBs (PCB).SND_WL2, Seg.Ack)
                         or else (TPCBs (PCB).SND_WL2 = Seg.Ack
                                    and then
                                  AIP.M32_T (TCPH.TCPH_Window (Seg.Thdr))
                                    > TPCBs (PCB).SND_WND)))
         then
            TPCBs (PCB).SND_WND := AIP.M32_T (TCPH.TCPH_Window (Seg.Thdr));
            TPCBs (PCB).SND_WL1 := Seg.Seq;
            TPCBs (PCB).SND_WL2 := Seg.Ack;

            if TPCBs (PCB).SND_WND = 0 then

               --  Start persist timer

               TPCBs (PCB).Persist_Ticks   := 0;
               TPCBs (PCB).Persist_Backoff := Initial_Persist_Backoff;
            else
               --  Stop persist timer

               TPCBs (PCB).Persist_Ticks   := -1;
               TPCBs (PCB).Persist_Backoff := 0;
            end if;
         end if;
      end if;
   end Process_Ack;

   ----------------
   -- TCP_Sndbuf --
   ----------------

   function TCP_Sndbuf (PCB : PCBs.PCB_Id) return AIP.U16_T
   --# global in TPCBs;
   is
   begin
      return TPCBs (PCB).SND_BUF;
   end TCP_Sndbuf;

   -----------------
   -- On_TCP_Sent --
   -----------------

   procedure On_TCP_Sent
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_SENT, PCB, Cb);
   end On_TCP_Sent;

   -----------------
   -- On_TCP_Recv --
   -----------------

   procedure On_TCP_Recv
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_RECV, PCB, Cb);
   end On_TCP_Recv;

   ----------------
   -- TCP_Recved --
   ----------------

   procedure TCP_Recved
     (PCB : PCBs.PCB_Id;
      Len : AIP.U16_T)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Recved;

   -----------------
   -- On_TCP_Poll --
   -----------------

   procedure On_TCP_Poll
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id;
      Ivl : AIP.U16_T)
   --# global in out TPCBs; in TCP_Ticks;
   is
   begin
      --  First disable polling temporarily

      TPCBs (PCB).Poll_Ivl := 0;

      --  Set new callback

      TCP_Callback (TCP_EVENT_POLL, PCB, Cb);

      --  Start timer with initial value so that it triggers immediately

      TPCBs (PCB).Poll_Ticks := TCP_Ticks - AIP.M32_T (Ivl) - 1;
      TPCBs (PCB).Poll_Ivl   := AIP.M32_T (Ivl);
   end On_TCP_Poll;

   ---------------
   -- TCP_Close --
   ---------------

   procedure TCP_Close (PCB : PCBs.PCB_Id; Err : out AIP.Err_T)
   --# global in out IPCBs, TPCBs,
   --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??

      --  Finally deallocate PCB

      TCP_Free (PCB);
      Err := AIP.NOERR;
   end TCP_Close;

   ---------------
   -- TCP_Abort --
   ---------------

   procedure TCP_Drop (PCB : PCBs.PCB_Id)
   --# global in out IPCBs, TPCBs,
   --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
      Err : AIP.Err_T;
      pragma Unreferenced (Err);
   begin
      --  Send RST

      TCP_Send_Rst
        (Src_IP   => IPCBs (PCB).Local_IP,
         Src_Port => IPCBs (PCB).Local_Port,
         Dst_IP   => IPCBs (PCB).Remote_IP,
         Dst_Port => IPCBs (PCB).Remote_Port,
         Ack      => True,
         Seq_Num  => TPCBs (PCB).SND_NXT,
         Ack_Num  => TPCBs (PCB).RCV_NXT,
         Err      => Err);

      --  Deallocate PCB

      TCP_Free (PCB);
   end TCP_Drop;

   ------------------
   -- On_TCP_Abort --
   ------------------

   procedure On_TCP_Abort
     (PCB : PCBs.PCB_Id;
      Cb  : Callbacks.CBK_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_ABORT, PCB, Cb);
   end On_TCP_Abort;

   -----------------
   -- TCP_Receive --
   -----------------

   procedure TCP_Receive
     (PCB : PCBs.PCB_Id;
      Seg : Segment;
      Err : out AIP.Err_T)
   --# global in out TPCBs, IPCBs, IP.State, Buffers.State;
   --#        in IP.FIB, Boot_Time, TCP_Ticks,
   --#           Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
      New_PCB : PCBs.PCB_Id;

      Win_L, Win_R : AIP.M32_T;
      --  Left and right edges of receive window

      New_Data_Len : AIP.M32_T;
      --  Length of non-duplicate data in segment

      Discard : Boolean := False;
      --  Set True to prevent any further processing

      --  procedure Setup_Flow_Control;
      --  Shared processing between passive and active open: once the remote
      --  MSS is known, set up the congestion window and other flow control
      --  parameters.

      --  procedure Teardown (Callback : Boolean);
      --  Tear down the current connection, notify user if Callback is True

      ------------------------
      -- Setup_Flow_Control --
      ------------------------

      procedure Setup_Flow_Control (PCB : PCBs.PCB_Id)
      --# global in out TPCBs; in Seg;
      is
      begin
         --  Set remote MSS

         if Seg.MSS = 0 then
            TPCBs (PCB).Remote_MSS := 512;
         else
            TPCBs (PCB).Remote_MSS := Seg.MSS;
         end if;

         --  Slow start: initialize CWND to 1 segment

         TPCBs (PCB).CWND := AIP.M32_T (TPCBs (PCB).Remote_MSS);

         --  Congestion avoidance: initialize SSthresh to 65_535

         TPCBs (PCB).SSTHRESH := 65_535;
      end Setup_Flow_Control;

      --------------
      -- Teardown --
      --------------

      procedure Teardown (Callback : Boolean)
      --# global in out Buffers.State, Discard, IPCBs, TPCBs,
      --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
      --#        in PCB;
      is
         Err : AIP.Err_T;
      begin
         if Callback then
            TCP_Event
              (Ev   => TCP_Event_T'(Kind => TCP_EVENT_ABORT,
                                    Len  => 0,
                                    Buf  => Buffers.NOBUF,
                                    Addr => IPaddrs.IP_ADDR_ANY,
                                    Port => PCBs.NOPORT,
                                    Err  => AIP.ERR_RST),
               PCB  => PCB,
               Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_ABORT),
               Err  => Err);

            --  Notify failure of pending send operations???
         end if;
         Set_State (PCB, Closed);
         TCP_Free (PCB);
         Discard := True;
      end Teardown;

   --  Start of processing for TCP_Receive

   begin
      pragma Assert (PCB /= PCBs.NOPCB);

      case TPCBs (PCB).State is
         when Listen =>
            if TCPH.TCPH_Rst (Seg.Thdr) = 1 then

               --  Discard RST on listening PCB

               null;

            elsif TCPH.TCPH_Ack (Seg.Thdr) = 1 then
               TCP_Send_Rst
                 (Src_IP   => IPH.IPH_Dst_Address (Seg.Ihdr),
                  Src_Port => TCPH.TCPH_Dst_Port  (Seg.Thdr),
                  Dst_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
                  Dst_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
                  Ack      => False,
                  Seq_Num  => Seg.Ack,
                  Ack_Num  => 0,
                  Err      => Err);

            elsif TCPH.TCPH_Syn (Seg.Thdr) = 1 then
               --  Check segment security???
               --  Check segment precedence???

               --  Check backlog???

               TCP_New (New_PCB);
               if New_PCB = PCBs.NOPCB then

                  --  Can't queue new connection, discard segment

                  null;

               else
                  --  Copy TCP parameters from Listen PCB

                  TPCBs (New_PCB) := TPCBs (PCB);

                  --  Set up PCB for new connection

                  Set_State (New_PCB, Syn_Received);

                  Setup_PCB
                    (PCB         => New_PCB,
                     Local_IP    => IPH.IPH_Dst_Address (Seg.Ihdr),
                     Local_Port  => TCPH.TCPH_Dst_Port  (Seg.Thdr),
                     Remote_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
                     Remote_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
                     Err         => Err);

                  if AIP.No (Err) then
                     Setup_Flow_Control (New_PCB);

                     TPCBs (New_PCB).SND_UNA := TPCBs (New_PCB).ISS;
                     TPCBs (New_PCB).SND_NXT := TPCBs (New_PCB).ISS;
                     TPCBs (New_PCB).IRS     := Seg.Seq;
                     TPCBs (New_PCB).RCV_NXT := TPCBs (New_PCB).IRS + 1;

                     --  Insert new PCB in active list

                     PCBs.Prepend
                       (PCB      => New_PCB,
                        PCB_Head => Active_PCBs,
                        PCB_Pool => IPCBs);

                     --  Send SYN|ACK

                     TCP_Send_Control
                       (PCB => New_PCB,
                        Syn => True,
                        Fin => False,
                        Err => Err);
                  else
                     --  Failed to set up PCB: bail out

                     TCP_Free (New_PCB);
                  end if;
               end if;

            else
               --  Invalid, drop segment and return

               null;

            end if;

         when Syn_Sent =>
            if TCPH.TCPH_Ack (Seg.Thdr) = 1 then
               --  Reject if SEG.ACK <= ISS or SEG.ACK > SND.NXT

               if not Seq_Range
                 (TPCBs (PCB).ISS,
                  Seg.Ack - 1,
                  TPCBs (PCB).SND_NXT)
               then
                  if TCPH.TCPH_Rst (Seg.Thdr) = 0 then
                     TCP_Send_Rst
                       (Src_IP   => IPH.IPH_Dst_Address (Seg.Ihdr),
                        Src_Port => TCPH.TCPH_Dst_Port  (Seg.Thdr),
                        Dst_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
                        Dst_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
                        Ack      => False,
                        Seq_Num  => Seg.Ack,
                        Ack_Num  => 0,
                        Err      => Err);
                  end if;
                  Discard := True;
               end if;
            end if;

            if not Discard then
               if TCPH.TCPH_Rst (Seg.Thdr) = 1 then
                  if TCPH.TCPH_Ack (Seg.Thdr) = 1 then
                     --  Connection refused

                     TCP_Event
                       (Ev   => TCP_Event_T'(Kind => TCP_EVENT_ABORT,
                                             Len  => 0,
                                             Buf  => Buffers.NOBUF,
                                             Addr => IPaddrs.IP_ADDR_ANY,
                                             Port => PCBs.NOPORT,
                                             Err  => AIP.ERR_RST),
                        PCB  => PCB,
                        Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_ABORT),
                        Err  => Err);

                     --  Drop PCB

                     TCP_Free (PCB);
                  end if;

                  Discard := True;
               end if;
            end if;

            if not Discard then
               --  Check security???
               --  Check precedence???

               if TCPH.TCPH_Syn (Seg.Thdr) = 1 then
                  Setup_Flow_Control (PCB);

                  TPCBs (PCB).IRS     := Seg.Seq + 1;
                  TPCBs (PCB).RCV_NXT := TPCBs (PCB).IRS + 1;

                  if TCPH.TCPH_Ack (Seg.Thdr) = 1 then
                     Process_Ack (PCB, Seg);
                  end if;

                  if TPCBs (PCB).SND_UNA > TPCBs (PCB).ISS then
                     Set_State (PCB, Established);
                     TCP_Send_Control (PCB => PCB,
                                       Syn => False,
                                       Fin => False,
                                       Err => Err);

                  else
                     Set_State (PCB, Syn_Received);
                     TCP_Send_Control (PCB => PCB,
                                       Syn => True,
                                       Fin => False,
                                       Err => Err);
                  end if;
               end if;
            end if;

         when others =>
            --  1. Check sequence number

            Win_L := TPCBs (PCB).RCV_NXT;
            Win_R := TPCBs (PCB).RCV_NXT + TPCBs (PCB).RCV_WND;

            if not
              (TPCBs (PCB).RCV_WND = 0 and then Seg.Seq = TPCBs (PCB).RCV_NXT)
                or else
              Seq_Range (Win_L, Seg.Seq, Win_R)
                or else
              Seq_Range (Win_L, Seg.Seq + AIP.M32_T (Seg.Len) - 1, Win_R)
            then
               --  Segment is not acceptable: send ACK (unless RST is present)
               --  and discard.

               if TCPH.TCPH_Rst (Seg.Thdr) = 0 then
                  TCP_Send_Control (PCB => PCB,
                                    Syn => False,
                                    Fin => False,
                                    Err => Err);
               end if;
               Discard := True;

            else
               --  Here if segment is acceptable

               --  2. Check RST bit

               if TCPH.TCPH_Rst (Seg.Thdr) = 1 then
                  Teardown
                    (Callback => (TPCBs (PCB).State = Syn_Received
                                    and then TPCBs (PCB).Active)
                                 or else
                                   TPCBs (PCB).State in
                                     Established .. Close_Wait);
               end if;
            end if;

            --  3. Check security and precedence???

            --  4. Check SYN bit

            if not Discard and then TCPH.TCPH_Syn (Seg.Thdr) = 1 then
               --  SYN is in the window: error, tear down connection

               Teardown (Callback => True);
            end if;

            --  5. Check ACK field

            if not Discard and then TCPH.TCPH_Ack (Seg.Thdr) = 0 then
               Discard := True;
            end if;

            if not Discard then
               if TPCBs (PCB).State = Syn_Received then
                  if Seq_Range
                    (TPCBs (PCB).SND_UNA,
                     Seg.Ack,
                     TPCBs (PCB).SND_NXT + 1)
                  then
                     Set_State (PCB, Established);
                  else
                     TCP_Send_Rst
                       (Src_IP   => IPH.IPH_Dst_Address (Seg.Ihdr),
                        Src_Port => TCPH.TCPH_Dst_Port  (Seg.Thdr),
                        Dst_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
                        Dst_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
                        Ack      => False,
                        Seq_Num  => Seg.Ack,
                        Ack_Num  => 0,
                        Err      => Err);
                     Teardown (Callback => False);
                  end if;
               end if;
            end if;

            if not Discard then
               case TPCBs (PCB).State is
                  when Syn_Received =>
                     --  Can't happen, processed previously

                     null; -- raise Program_Error; ???

                  when Established | Fin_Wait_1 | Fin_Wait_2 =>
                     Process_Ack (PCB, Seg);

                     if TPCBs (PCB).State = Fin_Wait_2
                       and then Buffers.Empty (TPCBs (PCB).Unack_Queue)
                     then
                        --  Ack user CLOSE but do not free PCB???
                        null; --  TBD???
                     end if;

                     --  6. Check URG bit

                     if TCPH.TCPH_Urg (Seg.Thdr) = 1
                          and then
                        Seq_Lt (TPCBs (PCB).RCV_UP,
                                Seg.Seq
                                + AIP.M32_T (TCPH.TCPH_Urgent_Ptr (Seg.Thdr)))
                     then
                        TPCBs (PCB).RCV_UP :=
                          Seg.Seq
                          + AIP.M32_T (TCPH.TCPH_Urgent_Ptr (Seg.Thdr));

                        --  Notify user ???

                        null;
                     end if;

                     --  7. Process segment text

                     Buffers.Buffer_Header
                       (Seg.Buf,
                        -(4 * AIP.S16_T (IPH.IPH_IHL (Seg.Ihdr)
                          + TCPH.TCPH_Data_Offset (Seg.Thdr))),
                        Err);
                     pragma Assert (AIP.No (Err));

                     pragma Assert (not Seq_Lt (TPCBs (PCB).RCV_NXT, Seg.Seq));
                     --  Else segment is out of order

                     if Seq_Lt (Seg.Seq, TPCBs (PCB).RCV_NXT) then
                        --  Drop head of segment that was already received

                        New_Data_Len :=
                          AIP.M32_T (Seg.Len)
                          - (TPCBs (PCB).RCV_NXT - Seg.Seq);

                        Buffers.Buffer_Header
                          (Seg.Buf,
                           -AIP.S16_T (TPCBs (PCB).RCV_NXT - Seg.Seq),
                           Err);
                        pragma Assert (AIP.No (Err));
                     else
                        New_Data_Len := AIP.M32_T (Seg.Len);
                     end if;

                     TPCBs (PCB).RCV_NXT := Seg.Seq + New_Data_Len;

                     if AIP.M32_T (Seg.Len) < TPCBs (PCB).RCV_WND then
                        TPCBs (PCB).RCV_WND :=
                          TPCBs (PCB).RCV_WND - New_Data_Len;

                     else
                        TPCBs (PCB).RCV_WND := 0;
                     end if;

                     Deliver_Segment (PCB, Seg.Buf);

                  when others =>

                     --  Ignore urgent pointer and segment text

                     null;
               end case;

               --  8. check FIN bit

               if TCPH.TCPH_Fin (Seg.Thdr) = 1 then
                  case TPCBs (PCB).State is
                     when Closed | Listen | Syn_Sent =>
                        null;

                     when Established | Syn_Received =>
                        --  Notify connection closed: deliver 0 bytes of data

                        TCP_Event
                          (Ev   => TCP_Event_T'(Kind => TCP_EVENT_RECV,
                                                Len  => 0,
                                                Buf  => Buffers.NOBUF,
                                                Addr => IPaddrs.IP_ADDR_ANY,
                                                Port => PCBs.NOPORT,
                                                Err  => AIP.NOERR),
                           PCB  => PCB,
                           Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_RECV),
                           Err  => Err);
                        Set_State (PCB, Close_Wait);

                     when Fin_Wait_1 =>
                        --  If our FIN has been Ack'd then we are already
                        --  in Closing or Fin_Wait_2.

                        Set_State (PCB, Closing);

                     when Fin_Wait_2 =>
                        Set_State (PCB, Time_Wait);

                        --  Start Time_Wait timer???

                     when Close_Wait | Closing | Last_Ack =>
                        null;

                     when Time_Wait =>
                        --  Restart 2MSL timeout???
                        null;
                  end case;
               end if;
            end if;
      end case;
   end TCP_Receive;

   ---------------
   -- TCP_Input --
   ---------------

   procedure TCP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --# global in out TPCBs, IPCBs, IP.State, Buffers.State;
   --#        in IP.FIB, Boot_Time, TCP_Ticks,
   --#           Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
      pragma Unreferenced (Netif);

      Seg : Segment;

      PThdr : System.Address;

      PTH_Buf : Buffers.Buffer_Id;
      Err : AIP.Err_T;

      PCB : PCBs.PCB_Id := PCBs.NOPCB;
      --  PCB of the current segment

      Tlen : AIP.U16_T;
      --  TCP payload length (TCP header including options + segment payload)

      Data_Offset : AIP.U16_T;
      --  Data offset from start of TCP headers, in bytes

      Option_Offset : AIP.U16_T;
      --  Offset of option information being processed

      Malformed_Options : Boolean := False;
      --  Set True if malformed options are detected

      Option_Kind, Option_Length, Option_Val : AIP.U8_T;
      --  Fields of TCP options

      --  Variables used for construction of reply

      Ack : Boolean;
      Seq_Num, Ack_Num : AIP.M32_T;

      --  procedure Get_Option_Byte (V : out AIP.U8_T);
      --  Retrieve one byte of TCP options at Option_Offset, and increment
      --  Option_Offset.

      ---------------------
      -- Get_Option_Byte --
      ---------------------

      procedure Get_Option_Byte (V : out AIP.U8_T) is
         --# hide Get_Option_Byte;
         pragma Assert (Option_Offset < Data_Offset);
         Result : AIP.U8_T;
         for Result'Address use
           Conversions.Ofs (Seg.Thdr, Natural (Option_Offset));
      begin
         Option_Offset := Option_Offset + 1;
         V := Result;
      end Get_Option_Byte;

      --  procedure Check_Option_Length (Len : AIP.U8_T);
      --  Check that the option length is equal to Length, and that enough
      --  option information is available (used for fixed length options).
      --  Current Option_Offset is right after the option kind. If the found
      --  length byte does not have the expected value, or insufficient
      --  option information is present, Malformed_Options is set.

      -------------------------
      -- Check_Option_Length --
      -------------------------

      procedure Check_Option_Length (Len : AIP.U8_T)
      --# global in Data_Offset, Option_Offset; in out Malformed_Options;
      is
         Actual_Len : AIP.U8_T;
      begin
         if Data_Offset - Option_Offset < AIP.U16_T (Len) - 1 then
            Malformed_Options := True;
         else
            Get_Option_Byte (Actual_Len);
            if Actual_Len /= Len then
               Malformed_Options := True;
            end if;
         end if;
      end Check_Option_Length;

   --  Start of processing for TCP_Input

   begin
      Seg := Segment'(Buf          => Buf,
                      Thdr         => System.Null_Address,
                      Ihdr         => Buffers.Buffer_Payload (Buf),
                      Len          => 0,
                      Seq          => 0,
                      Ack          => 0,
                      MSS          => 0,
                      Window_Scale => 0);

      IP.Get_Next_Header
        (Buf,
         TCPH.TCP_Header_Size / 8,
         Seg.Thdr,
         Err);

      Tlen := IPH.IPH_Length (Seg.Ihdr)
                - 4 * AIP.U16_T (IPH.IPH_IHL (Seg.Ihdr));

      --  Verify TCP checksum

      Buffers.Buffer_Alloc
        (0, TCPH.TCP_Pseudo_Header_Size / 8, Buffers.SPLIT_BUF, PTH_Buf);

      if PTH_Buf =  Buffers.NOBUF then
         Err := AIP.ERR_MEM;
      else
         PThdr := Buffers.Buffer_Payload (PTH_Buf);

         TCPH.Set_TCPP_Src_Address (PThdr, IPH.IPH_Src_Address (Seg.Ihdr));
         TCPH.Set_TCPP_Dst_Address (PThdr, IPH.IPH_Dst_Address (Seg.Ihdr));
         TCPH.Set_TCPP_Zero        (PThdr, 0);
         TCPH.Set_TCPP_Protocol    (PThdr, IPH.IP_Proto_TCP);
         TCPH.Set_TCPP_Length      (PThdr, Tlen);

         Buffers.Buffer_Chain (PTH_Buf, Buf);

         if Checksum.Sum (PTH_Buf, Buffers.Buffer_Tlen (PTH_Buf))
              /= 16#ffff#
         then
            Err := AIP.ERR_VAL;
         end if;

         Buffers.Buffer_Blind_Free (PTH_Buf);
      end if;

      if AIP.No (Err) then
         --  Now we know we have a valid TCP header, compute Seg.Len and
         --  retrieve PCB. Seg.Len is the logical TCP segment length, including
         --  the data payload, as well as the SYN and FIN flags.

         Data_Offset := 4 * AIP.U16_T (TCPH.TCPH_Data_Offset (Seg.Thdr));
         Seg.Len := Tlen - Data_Offset
                      + AIP.U16_T (TCPH.TCPH_Syn (Seg.Thdr))
                      + AIP.U16_T (TCPH.TCPH_Fin (Seg.Thdr));
         Seg.Seq := TCPH.TCPH_Seq_Num (Seg.Thdr);
         Seg.Ack := TCPH.TCPH_Ack_Num (Seg.Thdr);

         --  Save Thdr in buffer so that we can easily access it if we park
         --  the segment for later delivery.

         Buffers.Set_Packet_Info (Buf, Seg.Thdr);

         --  Parse TCP options

         Option_Offset := TCPH.TCP_Header_Size / 8;
         while Option_Offset < Data_Offset and then not Malformed_Options loop
            Get_Option_Byte (Option_Kind);
            case Option_Kind is
               when TCPH.TCP_Option_End | TCPH.TCP_Option_NOP =>
                  --  End of option list, No operation

                  null;

               when TCPH.TCP_Option_MSS =>
                  --  Maximum segment size

                  Check_Option_Length (4);
                  if not Malformed_Options then
                     Get_Option_Byte (Option_Val);
                     Seg.MSS := AIP.U16_T (Option_Val) * 256;
                     Get_Option_Byte (Option_Val);
                     Seg.MSS := Seg.MSS + AIP.U16_T (Option_Val);
                  end if;

               when TCPH.TCP_Option_Win_Scale =>
                  --  Window scale factor

                  Check_Option_Length (3);
                  if not Malformed_Options then
                     Get_Option_Byte (Seg.Window_Scale);
                  end if;

               when others =>
                  if Data_Offset - Option_Offset < 1 then
                     Malformed_Options := True;

                  else
                     Get_Option_Byte (Option_Length);
                     if Option_Length < 2
                       or else Data_Offset - Option_Offset
                                 < AIP.U16_T (Option_Length) - 2
                     then
                        Malformed_Options := True;

                     else
                        --  Discard unknown option

                        Option_Offset :=
                          Option_Offset + AIP.U16_T (Option_Length) - 2;
                     end if;
                  end if;
            end case;
         end loop;

         --  Find PCB

         PCBs.Find_PCB
           (Local_IP    => IPH.IPH_Dst_Address (Seg.Ihdr),
            Local_Port  => TCPH.TCPH_Dst_Port  (Seg.Thdr),
            Remote_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
            Remote_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
            PCB_Heads   =>
              TCP_PCB_Heads'(1 => Listen_PCBs,
                             2 => Bound_PCBs,
                             3 => Active_PCBs,
                             4 => Time_Wait_PCBs),
            PCB_Pool    => IPCBs,
            PCB         => PCB);

         pragma Assert (PCB = PCBs.NOPCB or else TPCBs (PCB).State /= Closed);

         if PCB = PCBs.NOPCB then
            --  Closed case

            if TCPH.TCPH_Rst (Seg.Thdr) = 1 then
               --  Discard incoming RST without associated PCB

               null;

            else
               if TCPH.TCPH_Ack (Seg.Thdr) = 0 then
                  Seq_Num := 0;
                  Ack_Num := Seg.Seq + AIP.M32_T (Seg.Len);
                  Ack := True;
               else
                  Seq_Num := Seg.Ack;
                  Ack_Num := 0;
                  Ack := False;
               end if;

               TCP_Send_Rst
                 (Src_IP   => IPH.IPH_Dst_Address (Seg.Ihdr),
                  Src_Port => TCPH.TCPH_Dst_Port  (Seg.Thdr),
                  Dst_IP   => IPH.IPH_Src_Address (Seg.Ihdr),
                  Dst_Port => TCPH.TCPH_Src_Port  (Seg.Thdr),
                  Ack      => Ack,
                  Seq_Num  => Seq_Num,
                  Ack_Num  => Ack_Num,
                  Err      => Err);
            end if;

         else
            --  Over to actual TCP FSM

            TCP_Receive (PCB, Seg, Err);
         end if;
      end if;

      Buffers.Buffer_Blind_Free (Buf);
   end TCP_Input;

   --------------------
   -- TCP_Fast_Timer --
   --------------------

   procedure TCP_Fast_Timer
   --# global in out Buffers.State, TPCBs, IP.State; in Active_PCBs, IPCBs;
   is
      PCB : PCBs.PCB_Id;
   begin
      --  Retry delivery of pending segments

      PCB := Active_PCBs;
      while PCB /= PCBs.NOPCB loop
         if TPCBs (PCB).Refused_Packet /= Buffers.NOBUF then
            Deliver_Segment (PCB, Buffers.NOBUF);
         end if;
         PCB := IPCBs (PCB).Link;
      end loop;

      --  Generated stub: replace with real body!
      null;
   end TCP_Fast_Timer;

   ------------------------
   -- Retransmit_Timeout --
   ------------------------

   procedure Retransmit_Timeout (PCB : PCBs.PCB_Id) is
   begin
      null; --  TBD???
   end Retransmit_Timeout;

   -----------------------
   -- Send_Window_Probe --
   -----------------------

   procedure Send_Window_Probe (PCB : PCBs.PCB_Id) is
   begin
      null; --  TBD???
   end Send_Window_Probe;

   --------------------
   -- TCP_Slow_Timer --
   --------------------

   procedure TCP_Slow_Timer
   --# global in out TCP_Ticks, Active_PCBs, IPCBs, TPCBs;
   is
      Remove_PCB : Boolean;
      PCB      : PCBs.PCB_Id;
      Next_PCB : PCBs.PCB_Id;
   begin
      TCP_Ticks := TCP_Ticks + 1;

      PCB := Active_PCBs;
      while PCB /= PCBs.NOPCB loop
         Next_PCB := IPCBs (PCB).Link;
         Remove_PCB := False;

         if (TPCBs (PCB).State = SYN_SENT
             and then TPCBs (PCB).Retransmit_Count = Config.TCP_MAX_SYN_RTX)
           or else
             TPCBs (PCB).Retransmit_Count = Config.TCP_MAX_RTX
           or else (TPCBs (PCB).State = FIN_WAIT_2
                    and then TCP_Ticks - TPCBs (PCB).Watchdog_Ticks
                                > Fin_Wait_Timeout)
           or else (TPCBs (PCB).State = Syn_Received
                    and then TCP_Ticks - TPCBs (PCB).Watchdog_Ticks
                                > Syn_Received_Timeout)
           or else (TPCBs (PCB).State = Last_Ack
                    and then TCP_Ticks - TPCBs (PCB).Watchdog_Ticks
                                > 2 * Config.TCP_MSL * TCP_Hz)
         then
            Remove_PCB := True;

         else
            --  Persist timer: if SND_WND is 0, send window probe

            if TPCBs (PCB).Persist_Backoff > 0 then
               TPCBs (PCB).Persist_Ticks := TPCBs (PCB).Persist_Ticks + 1;

               if TPCBs (PCB).Persist_Ticks
                    >= TPCBs (PCB).Persist_Backoff
               then
                  TPCBs (PCB).Persist_Ticks := 0;

                  --  Double persist backoff up to Max_Persist_Backoff

                  if TPCBs (PCB).Persist_Backoff * 2
                       <= Max_Persist_Backoff
                  then
                     TPCBs (PCB).Persist_Backoff :=
                       TPCBs (PCB).Persist_Backoff * 2;
                  else
                     TPCBs (PCB).Persist_Backoff := Max_Persist_Backoff;
                  end if;

                  --  Send probe

                  Send_Window_Probe (PCB);
               end if;

            else
               --  Retransmit timer

               if TPCBs (PCB).Retransmit_Ticks >= 0 then
                  TPCBs (PCB).Retransmit_Ticks :=
                    TPCBs (PCB).Retransmit_Ticks + 1;
               end if;

               if not Buffers.Empty (TPCBs (PCB).Unack_Queue)
                 and then TPCBs (PCB).Retransmit_Ticks > TPCBs (PCB).RTO
               then
                  if TPCBs (PCB).State /= SYN_SENT then
                     --  Exponential backoff, except in SYN_SENT state

                     TPCBs (PCB).RTO := TPCBs (PCB).RTO * 2;
                  end if;
                  TPCBs (PCB).Retransmit_Ticks := 0;

                  --  Update SSTHRESH and congestion window

                  TPCBs (PCB).SSTHRESH :=
                    AIP.M32_T'Max
                      (AIP.M32_T'Min
                         (TPCBs (PCB).SND_WND, TPCBs (PCB).Cwnd) / 2,
                       2 * AIP.M32_T (TPCBs (PCB).Remote_MSS));
                  TPCBs (PCB).Cwnd := AIP.M32_T (TPCBs (PCB).Remote_MSS);

                  Retransmit_Timeout (PCB);
               end if;
            end if;

            --  Keep-alive timer

            --  TBD???
         end if;

         if Remove_PCB then
            TCP_Free (PCB);
         end if;
         PCB := Next_PCB;
      end loop;
   end TCP_Slow_Timer;

end AIP.TCP;
