------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Checksum;
with AIP.Config;
with AIP.IP;
with AIP.IPH;
with AIP.TCPH;
with AIP.Time_Types;

package body AIP.TCP
   --# own State is Boot_Time, IPCBs, TPCBs;
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

      --  Send sequence variables

      SND_UNA : M32_T; --  Send unacknowledged
      SND_NXT : M32_T; --  Send next
      SND_WND : M32_T; --  Send window
      SND_UP  : M32_T; --  Send urgent pointer
      SND_WL1 : M32_T; --  Segment sequence number used for last window update
      SND_WL2 : M32_T; --  Segment ack number used for last window update
      ISS     : M32_T; --  Initial send sequence number

      --  Receive sequence variables

      RCV_NXT : M32_T; --  Receive next
      RCV_WND : M32_T; --  Receive window
      RCV_UP  : M32_T; --  Receive urgent pointer
      IRS     : M32_T; --  Initial receive sequence number

      --  Send queue

      Send_Queue : Buffers.Packet_List;

      --  User (application) callbacks

      Callbacks : TCP_Callbacks;
   end record;

   TCP_PCB_Initializer : constant TCP_PCB :=
                           TCP_PCB'(State      => Closed,
                                    Callbacks  =>
                                      TCP_Callbacks'(others => Callbacks.NOCB),
                                    Send_Queue => Buffers.Empty_Packet_List,
                                    others     => 0);

   subtype Valid_TCP_PCB_Id is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_TCP_PCB - 1;

   subtype TCP_IPCB_Array is PCBs.IP_PCB_Array (Valid_TCP_PCB_Id);
   type TCP_TPCB_Array is array (Valid_TCP_PCB_Id) of TCP_PCB;

   Boot_Time : Time_Types.Time;

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
   is
   begin
      --  Should do much better than that to select a truly random ISN???
      return M32_T (Time_Types.Now)
        + (M32_T (Boot_Time)
             xor (Local_IP * 7
                + Remote_IP * 13
                + M32_T (Local_Port) * M32_T (Remote_Port)));
   end Initial_Sequence_Number;

   --------------
   -- TCP_Init --
   --------------

   procedure TCP_Init
      --# global out PCBs, Bound_PCBs, Listen_PCBs;
   is
   begin
      --  Record boot time to serve as local secret for generation of ISN

      Boot_Time := Time_Types.Now;

      --  Initialize all the PCBs, marking them unused, and initialize the list
      --  of bound PCBs as empty.

      IPCBs := TCP_IPCB_Array'(others => PCBs.IP_PCB_Initializer);
      TPCBs := TCP_TPCB_Array'(others => TCP_PCB_Initializer);

      Bound_PCBs     := PCBs.NOPCB;
      Listen_PCBs    := PCBs.NOPCB;
      Active_PCBs    := PCBs.NOPCB;
      Time_Wait_PCBs := PCBs.NOPCB;
   end TCP_Init;

   -------------
   -- TCP_Arg --
   -------------

   procedure TCP_Arg (PCB : PCBs.PCB_Id; Arg : System.Address) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Arg;

   --------------
   -- TCP_Bind --
   --------------

   procedure TCP_Bind
     (PCB        : PCBs.PCB_Id;
      Local_IP   : IPaddrs.IPaddr;
      Local_Port : AIP.U16_T;
      Err        : out AIP.Err_T)
   is
   begin
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

      if No (Err) then
         IPCBs (PCB).Link := Bound_PCBs;
         Bound_PCBs := PCB;
      end if;
   end TCP_Bind;

   ------------------
   -- TCP_Callback --
   ------------------

   procedure TCP_Callback
     (Evk  : TCP_Event_Kind;
      PCB  : PCBs.PCB_Id;
      Cbid : Callbacks.CBK_Id)
   is
   begin
      TPCBs (PCB).Callbacks (Evk) := Cbid;
   end TCP_Callback;

   ----------------
   -- TCP_Listen --
   ----------------

   procedure TCP_Listen (PCB : PCBs.PCB_Id; Err : out AIP.Err_T) is
   begin
      TCP_Listen_BL (PCB, Config.TCP_DEFAULT_LISTEN_BACKLOG, Err);
   end TCP_Listen;

   -------------------
   -- TCP_Listen_BL --
   -------------------

   procedure TCP_Listen_BL
     (PCB     : PCBs.PCB_Id;
      Backlog : AIP.U8_T;
      Err     : out AIP.Err_T)
   is
      pragma Unreferenced (Backlog);
   begin
      pragma Assert (PCB /= PCBs.NOPCB);

      if IPCBs (PCB).Local_Port = PCBs.NOPORT then
         --  PCB must first be bound

         Err := ERR_USE;
      else
         case TPCBs (PCB).State is
            when Closed =>
               TPCBs (PCB).State := Listen;

            when Listen =>
               null;

            when others =>
               Err := ERR_ISCONN;
         end case;
      end if;
   end TCP_Listen_BL;

   -------------
   -- TCP_New --
   -------------

   procedure TCP_New (Id : out PCBs.PCB_Id)
   --# global in out PCBs;
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
      raise Program_Error;
   end TCP_Accept;

   ------------------
   -- TCP_Accepted --
   ------------------

   procedure TCP_Accepted (PCB : PCBs.PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Accepted;

   -----------------
   -- TCP_Connect --
   -----------------

   procedure TCP_Connect
     (PCB  : PCBs.PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : PCBs.Port_T;
      Cb   : Connect_Cb_Id;
      Err  : out Err_T)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Connect;

   ---------------
   -- TCP_Write --
   ---------------

   procedure TCP_Write
     (PCB   : PCBs.PCB_Id;
      Data  : System.Address;
      Len   : AIP.U16_T;
      Flags : AIP.U8_T;
      Err   : out Err_T)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Write;

   ----------------
   -- TCP_Sndbuf --
   ----------------

   function TCP_Sndbuf (PCB : PCBs.PCB_Id) return AIP.U16_T is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Sndbuf (PCB);
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
      raise Program_Error;
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
      raise Program_Error;
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
      raise Program_Error;
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
      raise Program_Error;
   end TCP_Poll;

   ---------------
   -- TCP_Close --
   ---------------

   procedure TCP_Close (PCB : PCBs.PCB_Id; Err : out AIP.Err_T) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Close;

   ---------------
   -- TCP_Abort --
   ---------------

   procedure TCP_Abort (PCB : PCBs.PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Abort;

   -------------
   -- TCP_Err --
   -------------

   procedure TCP_Err (PCB : PCBs.PCB_Id; Cb : Err_Cb_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Err;

   ---------------
   -- TCP_Input --
   ---------------

   procedure TCP_Input (Buf : Buffers.Buffer_Id; Netif : NIF.Netif_Id) is
      pragma Unreferenced (Netif);

      Ihdr, Thdr, PThdr : System.Address;

      PTH_Buf : Buffers.Buffer_Id;
      Err : AIP.Err_T;

      PCB : PCBs.PCB_Id := PCBs.NOPCB;
      --  PCB of the current segment

      New_PCB : PCBs.PCB_Id;
      --  New PCB (used when a new connection is created)

      Tlen : U16_T;
      --  TCP payload length (TCP header including options + segment payload)

      Seg_Len : U16_T;
      --  Segment length (SEG.LEN)

      --  Variables used for construction of reply

      Ack : Boolean;
      Seq_Num, Ack_Num : M32_T;
   begin
      --  Latch address of IP header and retrieve a TCP view of the incoming
      --  segment.

      Ihdr := Buffers.Buffer_Payload (Buf);
      IP.Get_Next_Header
        (Buf,
         TCPH.TCP_Header_Size / 8,
         Thdr,
         Err);

      Tlen := IPH.IPH_Length (Ihdr) - 4 * U16_T (IPH.IPH_IHL (Ihdr));

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
         --  retrieve PCB.

         Seg_Len := Tlen - 4 * U16_T (TCPH.TCPH_Data_Offset (Thdr));

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
                  Ack_Num := TCPH.TCPH_Seq_Num (Thdr) + M32_T (Seg_Len);
                  Ack := True;
               else
                  Seq_Num := TCPH.TCPH_Ack_Num (Thdr);
                  Ack_Num := 0;
                  Ack := False;
               end if;

               TCP_Send_Control
                 (Src_IP   => IPH.IPH_Dst_Address (Ihdr),
                  Src_Port => TCPH.TCPH_Dst_Port  (Thdr),
                  Dst_IP   => IPH.IPH_Src_Address (Ihdr),
                  Dst_Port => TCPH.TCPH_Src_Port  (Thdr),
                  Syn      => False,
                  Rst      => True,
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
                     TCP_Send_Control
                       (Src_IP   => IPH.IPH_Dst_Address (Ihdr),
                        Src_Port => TCPH.TCPH_Dst_Port  (Thdr),
                        Dst_IP   => IPH.IPH_Src_Address (Ihdr),
                        Dst_Port => TCPH.TCPH_Src_Port  (Thdr),
                        Syn      => False,
                        Rst      => True,
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
                        TPCBs (New_PCB) := TPCBs (PCB);

                        TPCBs (New_PCB).State := Syn_Received;

                        IPCBs (New_PCB).Local_IP    := IPH.IPH_Dst_Address
                                                         (Ihdr);
                        IPCBs (New_PCB).Local_Port  := TCPH.TCPH_Dst_Port
                                                         (Thdr);
                        IPCBs (New_PCB).Remote_IP   := IPH.IPH_Dst_Address
                                                         (Ihdr);
                        IPCBs (New_PCB).Remote_Port := TCPH.TCPH_Dst_Port
                                                         (Thdr);

                        TPCBs (New_PCB).ISS :=
                          Initial_Sequence_Number
                            (Local_IP    => IPCBs (New_PCB).Local_IP,
                             Local_Port  => IPCBs (New_PCB).Local_Port,
                             Remote_IP   => IPCBs (New_PCB).Remote_IP,
                             Remote_Port => IPCBs (New_PCB).Remote_Port);

                        TPCBs (New_PCB).SND_UNA := TPCBs (New_PCB).ISS;
                        TPCBs (New_PCB).SND_NXT := TPCBs (New_PCB).ISS + 1;
                        TPCBs (New_PCB).IRS     := TCPH.TCPH_Seq_Num (Thdr);
                        TPCBs (New_PCB).RCV_NXT := TPCBs (New_PCB).IRS + 1;

                        TCP_Send_Control
                          (Src_IP   => IPCBs (New_PCB).Local_IP,
                           Src_Port => IPCBs (New_PCB).Local_Port,
                           Dst_IP   => IPCBs (New_PCB).Remote_IP,
                           Dst_Port => IPCBs (New_PCB).Remote_Port,
                           Syn      => True,
                           Rst      => False,
                           Ack      => True,
                           Seq_Num  => TPCBs (New_PCB).ISS,
                           Ack_Num  => TPCBs (New_PCB).RCV_NXT,
                           Err      => Err);

                        --  Process segment payload???
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

         Buffers.Buffer_Blind_Free (Buf);
      end if;
   end TCP_Input;

   --------------------
   -- TCP_Fast_Timer --
   --------------------

   procedure TCP_Fast_Timer is
   begin
      --  Generated stub: replace with real body!
      null;
   end TCP_Fast_Timer;

   ----------------------
   -- TCP_Send_Control --
   ----------------------

   procedure TCP_Send_Control
     (Src_IP   : IPaddrs.IPaddr;
      Src_Port : PCBs.Port_T;
      Dst_IP   : IPaddrs.IPaddr;
      Dst_Port : PCBs.Port_T;
      Syn      : Boolean;
      Rst      : Boolean;
      Ack      : Boolean;
      Seq_Num  : AIP.M32_T;
      Ack_Num  : AIP.M32_T;
      Err      : out AIP.Err_T)
   is
   begin
      null;
      --  TBD???
   end TCP_Send_Control;

   --------------------
   -- TCP_Slow_Timer --
   --------------------

   procedure TCP_Slow_Timer is
   begin
      --  Generated stub: replace with real body!
      null;
   end TCP_Slow_Timer;

end AIP.TCP;
