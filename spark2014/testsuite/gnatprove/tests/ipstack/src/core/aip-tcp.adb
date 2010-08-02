------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;

package body AIP.TCP is

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
     (Listen, Syn_Sent, Syn_Received, Established,
      Fin_Wait_1, Fin_Wait_2, Close_Wait, Closing, Last_Ack, Time_Wait);

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

      RECV_Cb     : Callbacks.CBK_Id;
      --  Callback id for TCP_RECV events
   end record;

   TCP_PCB_Initializer : constant TCP_PCB :=
                           TCP_PCB'(State   => Closed,
                                    RECV_Cb => Callbacks.NOCB,
                                    others  => 0);

   subtype Valid_TCP_PCB_Id is PCBs.Valid_PCB_Id
     range PCBs.Valid_PCB_Id'First
        .. PCBs.Valid_PCB_Id'First + Config.MAX_TCP_PCB - 1;

   subtype TCP_IPCB_Array is PCBs.IP_PCB_Array (Valid_TCP_PCB_Id);
   type TCP_TPCB_Array is array (Valid_TCP_PCB_Id) of TCP_PCB;

   IPCBs : TCP_IPCB_Array;
   TPCBs : TCP_TPCB_Array;

   Bound_PCBs     : PCBs.PCB_Id;
   Listen_PCBs    : PCBs.PCB_Id;
   Active_PCBs    : PCBs.PCB_Id;
   Time_Wait_PCBs : PCBs.PCB_Id;
   subtype TCP_PCB_Heads_Range is Natural range 1 .. 4;
   subtype TCP_PCB_Heads is PCBs.PCB_List (TCP_PCB_Heads_Range);

   ---------------
   -- PCB_Clear --
   ---------------

   procedure PCB_Clear (PCB : PCBs.PCB_Id)
      --# global in out PCBs;
   is
   begin
      IPCBs (PCB) := PCBs.IP_PCB_Initializer;
      TPCBs (PCB) := TCP_PCB_Initializer;

      IPCBs (PCB).Link := PCBs.NOPCB;
   end PCB_Clear;

   --------------
   -- TCP_Init --
   --------------

   procedure TCP_Init
      --# global out PCBs, Bound_PCBs, Listen_PCBs;
   is
   begin
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

   ------------------
   -- TCP_Callback --
   ------------------

   procedure TCP_Callback
     (Evk : TCP_Event_Kind;
      PCB : PCBs.PCB_Id;
      Id : Callbacks.CBK_Id)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Callback;

   -------------
   -- TCP_New --
   -------------

   procedure TCP_New (Id : out PCBs.PCB_Id)
   --# global in out PCBs;
   is
   begin
      PCBs.Allocate_PCB (IPCBs, Id);

      if Id /= PCBs.NOPCB then
         PCB_Clear (Id);
         IPCBs (Id).TTL := Config.TCP_TTL;
      end if;
   end TCP_New;

   --------------
   -- TCP_Bind --
   --------------

   procedure TCP_Bind
     (PCB  : PCBs.PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : AIP.U16_T;
      Err  : out Err_T)
   is
      B_Port : PCBs.Port_T;
      Other_PCB : PCBs.PCB_Id;
   begin
      pragma Assert (PCB /= PCBs.NOPCB);
      Err := NOERR;

      if TPCBs (PCB).State /= Closed then
         Err := ERR_ISCONN;
      end if;

      if Port = 0 then
         B_Port :=
           PCBs.Available_Port
             (PCB_Heads  =>
                  TCP_PCB_Heads'(1 => Listen_PCBs,
                                 2 => Bound_PCBs,
                                 3 => Active_PCBs,
                                 4 => Time_Wait_PCBs),
              PCB_Pool   => IPCBs,
              Privileged => False);
         if B_Port = 0 then
            Err := ERR_MEM;
         end if;
      else
         B_Port := Port;

         PCBs.Find_PCB (Local_IP    => Addr,
                        Local_Port  => Port,
                        Remote_IP   => IPaddrs.IP_ADDR_ANY,
                        Remote_Port => 0,
                        PCB_Heads   =>
                          TCP_PCB_Heads'(1 => Listen_PCBs,
                                         2 => Bound_PCBs,
                                         3 => Active_PCBs,
                                         4 => Time_Wait_PCBs),
                        PCB_Pool    => IPCBs,
                        PCB         => Other_PCB);

         if Other_PCB /= PCBs.NOPCB then
            Err := ERR_USE;
         end if;
      end if;

      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Bind;

   ----------------
   -- TCP_Listen --
   ----------------

   procedure TCP_Listen (PCB : PCBs.PCB_Id) is
   begin
      TCP_Listen_BL (PCB, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end TCP_Listen;

   -------------------
   -- TCP_Listen_BL --
   -------------------

   procedure TCP_Listen_BL
     (PCB     : PCBs.PCB_Id;
      Backlog : AIP.U8_T)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Listen_BL;

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
   begin
      --  Process segment???

      Buffers.Buffer_Blind_Free (Buf);
   end TCP_Input;

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

   procedure TCP_Slow_Timer is
   begin
      --  Generated stub: replace with real body!
      null;
   end TCP_Slow_Timer;

end AIP.TCP;
