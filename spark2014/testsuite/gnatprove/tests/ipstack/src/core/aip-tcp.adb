------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;

package body AIP.TCP is

   -------------
   -- TCP_Arg --
   -------------

   procedure TCP_Arg (PCB : PCB_Id; Arg : System.Address) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Arg;

   ------------------
   -- TCP_Callback --
   ------------------

   procedure TCP_Callback
     (Evk : TCP_Event_Kind;
      PCB : PCB_Id;
      Id : Callbacks.CBK_Id)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Callback;

   -------------
   -- TCP_New --
   -------------

   function TCP_New return PCB_Id is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_New;
   end TCP_New;

   --------------
   -- TCP_Bind --
   --------------

   function TCP_Bind
     (PCB  : PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : AIP.U16_T)
      return AIP.Err_T
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Bind (PCB, Addr, Port);
   end TCP_Bind;

   ----------------
   -- TCP_Listen --
   ----------------

   function TCP_Listen
     (PCB : PCB_Id)
      return PCB_Id
   is
   begin
      return TCP_Listen_BL (PCB, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end TCP_Listen;

   -------------------
   -- TCP_Listen_BL --
   -------------------

   function TCP_Listen_BL
     (PCB  : PCB_Id;
      Blog : AIP.U8_T)
      return PCB_Id
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Listen_BL (PCB, Blog);
   end TCP_Listen_BL;

   ----------------
   -- TCP_Accept --
   ----------------

   procedure TCP_Accept
     (PCB : PCB_Id;
      Cb  : Accept_Cb_Id)
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Accept;

   ------------------
   -- TCP_Accepted --
   ------------------

   procedure TCP_Accepted (PCB : PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Accepted;

   -----------------
   -- TCP_Connect --
   -----------------

   function TCP_Connect
     (PCB  : PCB_Id;
      Addr : IPaddrs.IPaddr;
      Port : AIP.U16_T;
      Cb   : Connect_Cb_Id)
      return AIP.Err_T
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Connect (PCB, Addr, Port, Cb);
   end TCP_Connect;

   ---------------
   -- TCP_Write --
   ---------------

   function TCP_Write
     (PCB   : PCB_Id;
      Data  : System.Address;
      Len   : AIP.U16_T;
      Flags : AIP.U8_T)
      return AIP.Err_T
   is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Write (PCB, Data, Len, Flags);
   end TCP_Write;

   ----------------
   -- TCP_Sndbuf --
   ----------------

   function TCP_Sndbuf (PCB : PCB_Id) return AIP.U16_T is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Sndbuf (PCB);
   end TCP_Sndbuf;

   --------------
   -- TCP_Sent --
   --------------

   procedure TCP_Sent
     (PCB : PCB_Id;
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
     (PCB : PCB_Id;
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
     (PCB : PCB_Id;
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
     (PCB : PCB_Id;
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

   function TCP_Close (PCB : PCB_Id) return AIP.Err_T is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
      return TCP_Close (PCB);
   end TCP_Close;

   ---------------
   -- TCP_Abort --
   ---------------

   procedure TCP_Abort (PCB : PCB_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Abort;

   -------------
   -- TCP_Err --
   -------------

   procedure TCP_Err (PCB : PCB_Id; Cb : Err_Cb_Id) is
   begin
      --  Generated stub: replace with real body!
      raise Program_Error;
   end TCP_Err;

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
