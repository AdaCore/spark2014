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

   pragma Unreferenced
     (Syn_Sent, Established,
      Fin_Wait_1, Fin_Wait_2, Close_Wait, Closing, Last_Ack, Time_Wait);

   type TCP_Callbacks is array (TCP_Event_Kind) of Callbacks.CBK_Id;

   type TCP_PCB is record
      State : TCP_State;

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

      RTT_Ticks  : AIP.M32_T;
      --  TCP ticks value when segment used for RTT estimation was sent

      RTT_Average : AIP.S16_T;
      RTT_Stddev  : AIP.S16_T;
      RTO         : AIP.S16_T;

      --  Send queue

      Send_Queue : Buffers.Packet_List;

      --  User (application) callbacks

      Callbacks : TCP_Callbacks;
   end record;

   TCP_PCB_Initializer : constant TCP_PCB :=
                           TCP_PCB'(State       => Closed,

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

                                    RTT_Ticks   => 0,
                                    RTT_Average => 0,
                                    RTT_Stddev  => 0,
                                    RTO         => 0,

                                    Send_Queue  => Buffers.Empty_Packet_List,
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

   procedure TCP_New (Id : out PCBs.PCB_Id)
   --# global in out IPCBs, TPCBs;
   is
   begin
      PCBs.Allocate_PCB (IPCBs, Id);

      if Id /= PCBs.NOPCB then
         IPCBs (Id).TTL := Config.TCP_TTL;
         TPCBs (Id) := TCP_PCB_Initializer;
      end if;
   end TCP_New;

   ----------------
   -- TCP_Accept --
   ----------------

   procedure TCP_Accept
     (PCB : PCBs.PCB_Id;
      Cb  : Accept_Cb_Id)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
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

   procedure TCP_Sent
     (PCB : PCBs.PCB_Id;
      Cb  : Sent_Cb_Id)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Sent;

   --------------
   -- TCP_Recv --
   --------------

   procedure TCP_Recv
     (PCB : PCBs.PCB_Id;
      Cb  : Recv_Cb_Id)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
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
      Ivl : AIP.U8_T)
   is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Poll;

   ---------------
   -- TCP_Close --
   ---------------

   procedure TCP_Close (PCB : PCBs.PCB_Id; Err : out AIP.Err_T) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Close;

   ---------------
   -- TCP_Abort --
   ---------------

   procedure TCP_Abort (PCB : PCBs.PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Abort;

   -------------
   -- TCP_Err --
   -------------

   procedure TCP_Err (PCB : PCBs.PCB_Id; Cb : Err_Cb_Id) is
   begin
      --  Generated stub: replace with real body!
      null; --  TBD??
   end TCP_Err;

   ---------------
   -- TCP_Input --
   ---------------

   procedure TCP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id)
   --# global in out Buffers.State, TPCBs, IPCBs;
   --#        in Boot_Time, Bound_PCBs, Listen_PCBs, Active_PCBs,
   --#           Time_Wait_PCBs;

   is
      pragma Unreferenced (Netif);

      Ihdr, Thdr, PThdr : System.Address;

      PTH_Buf : Buffers.Buffer_Id;
      Err : AIP.Err_T;

      PCB : PCBs.PCB_Id := PCBs.NOPCB;
      --  PCB of the current segment

      New_PCB : PCBs.PCB_Id;
      --  New PCB (used when a new connection is created)

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

      --  Options

      MSS : AIP.U16_T := 0;
      --  Remote advertised MSS

      Window_Scale : AIP.U8_T := 0;
      --  Window scaling factor

      Seg_Len : AIP.U16_T;
      --  Segment length (SEG.LEN)

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
           Conversions.Ofs (Thdr, Natural (Option_Offset));
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

      procedure Check_Option_Length (Len : AIP.U8_T) is
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

      --  procedure Update_RTT_Estimator (TPCB : in out TCP_PCB);
      --  Update the RTT estimator using the given RTT measurement, as per
      --  Jacobson paper.

      --------------------------
      -- Update_RTT_Estimator --
      --------------------------

      procedure Update_RTT_Estimator (TPCB  : in out TCP_PCB) is
         M : AIP.S16_T;
         --  Measured round trip time
      begin
         if TPCB.RTT_Ticks /= 0 then
            M := AIP.S16_T (TCP_Ticks - TPCB.RTT_Ticks);

            --  Update average estimator

            M := M - TPCB.RTT_Average / 8;
            TPCB.RTT_Average := TPCB.RTT_Average + M;

            --  Update standard deviation estimator

            M := (abs M) - TPCB.RTT_Stddev / 4;
            TPCB.RTT_Stddev := TPCB.RTT_Stddev + M;

            --  Set new retransmit timeout

            TPCB.RTO := TPCB.RTT_Average / 8 + TPCB.RTT_Stddev;

            TPCB.RTT_Ticks := 0;
         end if;
      end Update_RTT_Estimator;

   --  Start of processing for TCP_Input

   begin
      --  Latch address of IP header and retrieve a TCP view of the incoming
      --  segment.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP.Get_Next_Header
        (Buf,
         TCPH.TCP_Header_Size / 8,
         Thdr,
         Err);

      Tlen := IPH.IPH_Length (Ihdr) - 4 * AIP.U16_T (IPH.IPH_IHL (Ihdr));

      --  Verify TCP checksum

      Buffers.Buffer_Alloc
        (0, TCPH.TCP_Pseudo_Header_Size / 8, Buffers.SPLIT_BUF, PTH_Buf);

      if PTH_Buf =  Buffers.NOBUF then
         Err := AIP.ERR_MEM;
      else
         PThdr := Buffers.Buffer_Payload (PTH_Buf);

         TCPH.Set_TCPP_Src_Address (PThdr, IPH.IPH_Src_Address (Ihdr));
         TCPH.Set_TCPP_Dst_Address (PThdr, IPH.IPH_Dst_Address (Ihdr));
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
         --  Now we know we have a valid TCP header, compute Seg_Len and
         --  retrieve PCB. Seg_Len is the logical TCP segment length, including
         --  the data payload, as well as the flags field if SYN or FIN is set.

         Data_Offset := 4 * AIP.U16_T (TCPH.TCPH_Data_Offset (Thdr));
         Seg_Len := Tlen - Data_Offset
                      + AIP.U16_T (TCPH.TCPH_Syn (Thdr))
                      + AIP.U16_T (TCPH.TCPH_Fin (Thdr));

         --  Parse TCP options

         Option_Offset := TCPH.TCP_Header_Size / 8;
         while Option_Offset < Data_Offset and then not Malformed_Options loop
            Get_Option_Byte (Option_Kind);
            case Option_Kind is
               when 0 | 1 =>
                  --  End of option list, No operation

                  null;

               when 2 =>
                  --  Maximum segment size

                  Check_Option_Length (4);
                  if not Malformed_Options then
                     Get_Option_Byte (Option_Val);
                     MSS := AIP.U16_T (Option_Val) * 256;
                     Get_Option_Byte (Option_Val);
                     MSS := MSS + AIP.U16_T (Option_Val);
                  end if;

               when 3 =>
                  --  Window scale factor

                  Check_Option_Length (3);
                  if not Malformed_Options then
                     Get_Option_Byte (Window_Scale);
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
           (Local_IP    => IPH.IPH_Dst_Address (Ihdr),
            Local_Port  => TCPH.TCPH_Dst_Port  (Thdr),
            Remote_IP   => IPH.IPH_Src_Address (Ihdr),
            Remote_Port => TCPH.TCPH_Src_Port  (Thdr),
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

            if TCPH.TCPH_Rst (Thdr) = 1 then
               --  Discard incoming RST without associated PCB

               null;

            else
               if TCPH.TCPH_Ack (Thdr) = 0 then
                  Seq_Num := 0;
                  Ack_Num := TCPH.TCPH_Seq_Num (Thdr) + AIP.M32_T (Seg_Len);
                  Ack := True;
               else
                  Seq_Num := TCPH.TCPH_Ack_Num (Thdr);
                  Ack_Num := 0;
                  Ack := False;
               end if;

               TCP_Send_Rst
                 (Src_IP   => IPH.IPH_Dst_Address (Ihdr),
                  Src_Port => TCPH.TCPH_Dst_Port  (Thdr),
                  Dst_IP   => IPH.IPH_Src_Address (Ihdr),
                  Dst_Port => TCPH.TCPH_Src_Port  (Thdr),
                  Ack      => Ack,
                  Seq_Num  => Seq_Num,
                  Ack_Num  => Ack_Num,
                  Err      => Err);
            end if;

         else
            case TPCBs (PCB).State is
               when Listen =>
                  if TCPH.TCPH_Rst (Thdr) = 1 then

                     --  Discard RST on listening PCB

                     null;

                  elsif TCPH.TCPH_Ack (Thdr) = 1 then
                     TCP_Send_Rst
                       (Src_IP   => IPH.IPH_Dst_Address (Ihdr),
                        Src_Port => TCPH.TCPH_Dst_Port  (Thdr),
                        Dst_IP   => IPH.IPH_Src_Address (Ihdr),
                        Dst_Port => TCPH.TCPH_Src_Port  (Thdr),
                        Ack      => False,
                        Seq_Num  => TCPH.TCPH_Ack_Num (Thdr),
                        Ack_Num  => 0,
                        Err      => Err);

                  elsif TCPH.TCPH_Syn (Thdr) = 1 then
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
                                                         (Ihdr);
                        IPCBs (New_PCB).Local_Port  := TCPH.TCPH_Dst_Port
                                                         (Thdr);
                        IPCBs (New_PCB).Remote_IP   := IPH.IPH_Dst_Address
                                                         (Ihdr);
                        IPCBs (New_PCB).Remote_Port := TCPH.TCPH_Dst_Port
                                                         (Thdr);

                        TPCBs (New_PCB).Remote_MSS := MSS;
                        TPCBs (New_PCB).ISS :=
                          Initial_Sequence_Number
                            (Local_IP    => IPCBs (New_PCB).Local_IP,
                             Local_Port  => IPCBs (New_PCB).Local_Port,
                             Remote_IP   => IPCBs (New_PCB).Remote_IP,
                             Remote_Port => IPCBs (New_PCB).Remote_Port);

                        TPCBs (New_PCB).SND_UNA := TPCBs (New_PCB).ISS;
                        TPCBs (New_PCB).SND_NXT := TPCBs (New_PCB).ISS;
                        TPCBs (New_PCB).IRS     := TCPH.TCPH_Seq_Num (Thdr);
                        TPCBs (New_PCB).RCV_NXT := TPCBs (New_PCB).IRS + 1;

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

               when others =>
                  null;
                  --  TBD???
            end case;
         end if;

         if AIP.No (ERR) then
            --  Process segment payload???
            null;
         end if;

         Buffers.Buffer_Blind_Free (Buf);
      end if;
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
