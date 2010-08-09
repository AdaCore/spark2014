------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.Conversions;
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

   pragma Unreferenced (Closing, Last_Ack);

   type TCP_Callbacks is array (TCP_Event_Kind) of Callbacks.CBK_Id;

   type TCP_PCB is record
      State : TCP_State;

      Active : Boolean;
      --  Set True if connection was initiated with an active open (i.e. went
      --  through the SYN-SENT state).

      --  Connection parameters

      Local_MSS  : AIP.U16_T; --  Maximum segment size for receiving
      Remote_MSS : AIP.U16_T; --  Maximum segment size for sending

      --  Send sequence variables

      SND_UNA : AIP.M32_T; --  Send unacknowledged
      SND_NXT : AIP.M32_T; --  Send next
      SND_WND : AIP.M32_T; --  Send window
      SND_UP  : AIP.M32_T; --  Send urgent pointer
      SND_WL1 : AIP.M32_T; --  Segment sequence number for last window update
      SND_WL2 : AIP.M32_T; --  Segment ack number for last window update
      ISS     : AIP.M32_T; --  Initial send sequence number

      --  Receive sequence variables

      RCV_NXT : AIP.M32_T; --  Receive next
      RCV_WND : AIP.M32_T; --  Receive window
      RCV_UP  : AIP.M32_T; --  Receive urgent pointer
      IRS     : AIP.M32_T; --  Initial receive sequence number

      --  Round-trip average and standard deviation estimators for computation
      --  of retransmit timeout (in TCP 500 ms ticks).

      Poll_Ticks : AIP.M32_T;
      Poll_Ivl   : AIP.M32_T;
      --  TCP ticks value when polling callback was last called, and polling
      --  interval (0 for no polling).

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

      --  User (application) callbacks

      Callbacks : TCP_Callbacks;
   end record;

   TCP_PCB_Initializer : constant TCP_PCB :=
                           TCP_PCB'(State       => Closed,

                                    Active      => False,

                                    Local_MSS   => 0,
                                    Remote_MSS  => 0,

                                    SND_UNA     => 0,
                                    SND_NXT     => 0,
                                    SND_WND     => 0,
                                    SND_UP      => 0,
                                    SND_WL1     => 0,
                                    SND_WL2     => 0,
                                    ISS         => 0,

                                    RCV_NXT     => 0,
                                    RCV_WND     => 0,
                                    RCV_UP      => 0,
                                    IRS         => 0,

                                    Poll_Ticks  => 0,
                                    Poll_Ivl    => 0,

                                    RTT_Seq     => 0,
                                    RTT_Ticks   => 0,
                                    RTT_Average => 0,
                                    RTT_Stddev  => 0,
                                    RTO         => 0,

                                    Send_Queue  => Buffers.Empty_Packet_Queue,
                                    Unack_Queue => Buffers.Empty_Packet_Queue,

                                    Callbacks   =>
                                      TCP_Callbacks'(others =>
                                                       Callbacks.NOCB));

   subtype Valid_TCP_PCB_Id is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_TCP_PCB - 1;

   subtype TCP_IPCB_Array is PCBs.IP_PCB_Array (Valid_TCP_PCB_Id);
   type TCP_TPCB_Array is array (Valid_TCP_PCB_Id) of TCP_PCB;

   Boot_Time : Time_Types.Time;
   TCP_Ticks : AIP.M32_T;

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

   -----------------
   -- Process_Ack --
   -----------------

   procedure Process_Ack (PCB : PCBs.PCB_Id; Seg : Segment)
   --# global in out Buffers.State, TPCBs; in TCP_Ticks;
   is
      Packet : Buffers.Buffer_Id;
      Thdr   : System.Address;
      Len    : AIP.M32_T;
   begin
      if Seq_Lt (Seg.Ack, TPCBs (PCB).SND_UNA) then
         --  Ignore duplicated ack

         null;

      else
         --  Invalid ack for a seqno not sent yet should have been discarded

         pragma Assert (Seq_Le (Seg.Ack, TPCBs (PCB).SND_NXT));

         TPCBs (PCB).SND_UNA := Seg.Ack;

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
               Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_SENT));

            if TPCBs (PCB).State = Fin_Wait_1
              and then TCPH.TCPH_Fin (Thdr) = 1
            then
               --  FIN acked in FIN_WAIT_1 state: proceed to FIN_WAIT_2

               TPCBs (PCB).State := Fin_Wait_2;
            end if;

            --  Note: the following call leaves Packet unchanged (but removes
            --  it from the head of Unack_Queue).

            Buffers.Remove_Packet
              (Buffers.Transport,
               TPCBs (PCB).Unack_Queue,
               Packet);
         end loop;

         if Seq_Lt (TPCBs (PCB).SND_WL1, Seg.Seq)
              or else
            (TPCBs (PCB).SND_WL1 = Seg.Seq
               and then Seq_Le (TPCBs (PCB).SND_WL2, Seg.Ack))
         then
            --  Update window

            TPCBs (PCB).SND_WND := AIP.M32_T (TCPH.TCPH_Window (Seg.Thdr));
            TPCBs (PCB).SND_WND := Seg.Seq;
            TPCBs (PCB).SND_WND := Seg.Ack;
         end if;
      end if;
   end Process_Ack;

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

   ----------------------
   -- TCP_Send_Control --
   ----------------------

   procedure TCP_Send_Control
     (PCB : PCBs.PCB_Id;
      Syn : Boolean;
      Ack : Boolean;
      Err : out AIP.Err_T)
   is
   begin
      null;
      --  TBD???
   end TCP_Send_Control;

   -------------
   -- TCP_Arg --
   -------------

   procedure TCP_Arg (PCB : PCBs.PCB_Id; Arg : System.Address) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Arg;

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

      Err := AIP.NOERR;

      --  First bind PCB if necessary

      if IPCBs (PCB).Local_Port = PCBs.NOPORT then
         TCP_Bind (PCB, IPaddrs.IP_ADDR_ANY, PCBs.NOPORT, Err);
      end if;

      if AIP.No (Err) then
         pragma Assert (IPCBs (PCB).Local_Port /= PCBs.NOPORT);

         case TPCBs (PCB).State is
            when Closed =>
               TPCBs (PCB).State := Listen;
               PCBs.Unlink
                 (PCB      => PCB,
                  PCB_Head => Bound_PCBs,
                  PCB_Pool => IPCBs);
               PCBs.Prepend
                 (PCB      => PCB,
                  PCB_Head => Listen_PCBs,
                  PCB_Pool => IPCBs);
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
      case TPCBs (PCB).State is
         when Closed   =>
            if IPCBs (PCB).Local_Port /= PCBs.NOPORT then
               PCBs.Unlink (PCB      => PCB,
                            PCB_Head => Bound_PCBs,
                            PCB_Pool => IPCBs);
            end if;

         when Listen   =>
            PCBs.Unlink (PCB      => PCB,
                         PCB_Head => Listen_PCBs,
                         PCB_Pool => IPCBs);

         when Syn_Sent =>
            PCBs.Unlink (PCB      => PCB,
                         PCB_Head => Bound_PCBs,
                         PCB_Pool => IPCBs);

         when Established =>
            PCBs.Unlink (PCB      => PCB,
                         PCB_Head => Active_PCBs,
                         PCB_Pool => IPCBs);

         when Time_Wait =>
            PCBs.Unlink (PCB      => PCB,
                         PCB_Head => Time_Wait_PCBs,
                         PCB_Pool => IPCBs);

         when others =>
            --  Is this PCB supposed to be on a list???
            null;
      end case;

      IPCBs (PCB) := PCBs.IP_PCB_Initializer;
   end TCP_Free;

   ----------------
   -- TCP_Accept --
   ----------------

   procedure TCP_Accept (PCB : PCBs.PCB_Id; Cb : Accept_Cb_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_ACCEPT, PCB, Cb);
   end TCP_Accept;

   ------------------
   -- TCP_Accepted --
   ------------------

   procedure TCP_Accepted (PCB : PCBs.PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Accepted;

   -----------------
   -- TCP_Connect --
   -----------------

   procedure TCP_Connect
     (PCB  : PCBs.PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
      Cb   : Connect_Cb_Id;
      Err  : out AIP.Err_T)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Connect;

   ---------------
   -- TCP_Write --
   ---------------

   procedure TCP_Write
     (PCB   : PCBs.PCB_Id;
      Data  : System.Address;
      Len   : AIP.U16_T;
      Flags : AIP.U8_T;
      Err   : out AIP.Err_T)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Write;

   ----------------
   -- TCP_Sndbuf --
   ----------------

   function TCP_Sndbuf (PCB : PCBs.PCB_Id) return AIP.U16_T is
      pragma Unreferenced (PCB);
   begin
      --  Generated stub: replace with real body!
      return 0; --  TBD???
   end TCP_Sndbuf;

   --------------
   -- TCP_Sent --
   --------------

   procedure TCP_Sent (PCB : PCBs.PCB_Id; Cb : Sent_Cb_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_SENT, PCB, Cb);
   end TCP_Sent;

   --------------
   -- TCP_Recv --
   --------------

   procedure TCP_Recv (PCB : PCBs.PCB_Id; Cb : Recv_Cb_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_RECV, PCB, Cb);
   end TCP_Recv;

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

   --------------
   -- TCP_Poll --
   --------------

   procedure TCP_Poll
     (PCB : PCBs.PCB_Id;
      Cb  : Poll_Cb_Id;
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
   end TCP_Poll;

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

   -------------
   -- TCP_Err --
   -------------

   procedure TCP_Abort (PCB : PCBs.PCB_Id; Cb : Abort_Cb_Id)
   --# global in out TPCBs;
   is
   begin
      TCP_Callback (TCP_EVENT_ABORT, PCB, Cb);
   end TCP_Abort;

   -----------------
   -- TCP_Receive --
   -----------------

   procedure TCP_Receive
     (PCB : PCBs.PCB_Id;
      Seg : Segment;
      Err : out AIP.Err_T)
   --# global in out Buffers.State, TPCBs, IPCBs;
   --#        in Boot_Time, TCP_Ticks,
   --#           Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
   is
      New_PCB : PCBs.PCB_Id;

      Win_L, Win_R : AIP.M32_T;
      --  Left and right edges of receive window

      Discard : Boolean := False;
      --  Set True to prevent any further processing

      --  procedure Teardown (Callback : Boolean);
      --  Tear down the current connection, notify user if Callback is True

      --------------
      -- Teardown --
      --------------

      procedure Teardown (Callback : Boolean)
      --# global in out Buffers.State, Discard, IPCBs, TPCBs,
      --#               Bound_PCBs, Listen_PCBs, Active_PCBs, Time_Wait_PCBs;
      --#        in PCB;
      is
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
               Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_ABORT));

            --  Notify failure of pending send operations???
         end if;
         TPCBs (PCB).State := Closed;
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

                  TPCBs (New_PCB).State := Syn_Received;

                  IPCBs (New_PCB).Local_IP    := IPH.IPH_Dst_Address
                    (Seg.Ihdr);
                  IPCBs (New_PCB).Local_Port  := TCPH.TCPH_Dst_Port
                    (Seg.Thdr);
                  IPCBs (New_PCB).Remote_IP   := IPH.IPH_Dst_Address
                    (Seg.Ihdr);
                  IPCBs (New_PCB).Remote_Port := TCPH.TCPH_Dst_Port
                    (Seg.Thdr);

                  TPCBs (New_PCB).Remote_MSS := Seg.MSS;
                  TPCBs (New_PCB).ISS :=
                    Initial_Sequence_Number
                      (Local_IP    => IPCBs (New_PCB).Local_IP,
                       Local_Port  => IPCBs (New_PCB).Local_Port,
                       Remote_IP   => IPCBs (New_PCB).Remote_IP,
                       Remote_Port => IPCBs (New_PCB).Remote_Port);

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
                     Ack => True,
                     Err => Err);
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
                        Cbid => TPCBs (PCB).Callbacks (TCP_EVENT_ABORT));

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
                  TPCBs (PCB).IRS     := Seg.Seq + 1;
                  TPCBs (PCB).RCV_NXT := TPCBs (PCB).IRS + 1;

                  if TCPH.TCPH_Ack (Seg.Thdr) = 1 then
                     Process_Ack (PCB, Seg);
                  end if;

                  if TPCBs (PCB).SND_UNA > TPCBs (PCB).ISS then
                     TPCBs (PCB).State := Established;
                     TCP_Send_Control (PCB => PCB,
                                       Syn => False,
                                       Ack => True,
                                       Err => Err);

                  else
                     TPCBs (PCB).State := Syn_Received;
                     TCP_Send_Control (PCB => PCB,
                                       Syn => True,
                                       Ack => True,
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
                                    Ack => True,
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
                     TPCBs (PCB).State := Established;
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

                  when Established =>
                     Process_Ack (PCB, Seg);

                  when Fin_Wait_1 | Fin_Wait_2 =>
                     Process_Ack (PCB, Seg);

                     if TPCBs (PCB).State = Fin_Wait_2
                          and then Buffers.Empty (TPCBs (PCB).Unack_Queue)
                     then
                        --  Ack user CLOSE but do not free PCB???
                        null; --  TBD???
                     end if;

                  when others =>
                     null; --  TBD???

               end case;
            end if;

            --  6. Check URG bit

            null;
            --  TBD???
      end case;
   end TCP_Receive;

   ---------------
   -- TCP_Input --
   ---------------

   procedure TCP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --# global in out Buffers.State, TPCBs, IPCBs;
   --#        in Boot_Time, TCP_Ticks,
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

   -----------------
   -- TCP_Enqueue --
   -----------------

   procedure TCP_Enqueue
     (PCB : PCBs.PCB_Id;
      Buf : Buffers.Buffer_Id;
      Syn : Boolean;
      Ack : Boolean;
      Err : out AIP.Err_T)
   is
   begin
      null;
      --  TBD???
   end TCP_Enqueue;

   --------------------
   -- TCP_Fast_Timer --
   --------------------

   procedure TCP_Fast_Timer is
   begin
      --  Generated stub: replace with real body!
      null;
   end TCP_Fast_Timer;

   --------------------
   -- TCP_Slow_Timer --
   --------------------

   procedure TCP_Slow_Timer
   --# global in out TCP_Ticks;
   is
   begin
      TCP_Ticks := TCP_Ticks + 1;
   end TCP_Slow_Timer;

end AIP.TCP;
