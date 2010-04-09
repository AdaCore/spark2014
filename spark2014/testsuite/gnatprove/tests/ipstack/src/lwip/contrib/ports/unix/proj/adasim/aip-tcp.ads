------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Callbacks, AIP.IPaddrs;

--# inherit AIP.Callbacks, AIP.IPaddrs;

package AIP.TCP is

   subtype TCB_Id is AIP.IPTR_T;
   NOTCB : constant TCB_Id := AIP.NULIPTR;

   procedure Tcp_Arg (Pcb : TCB_Id; Arg : AIP.IPTR_T);

   function Tcp_New return TCB_Id;

   function Tcp_Bind
     (Pcb : TCB_Id;
      Addr : AIP.IPaddrs.IPaddr_Id;
      Port : AIP.U16_T)
     return AIP.Err_T;

   function Tcp_Listen
     (Pcb : TCB_Id)
     return TCB_Id;

   function Tcp_Listen_BL
     (Pcb : TCB_Id;
      Blog : AIP.U8_T)
     return TCB_Id;

   procedure Tcp_Accepted (Pcb : TCB_Id);

   subtype Accept_Cb_Id is AIP.Callbacks.Callback_Id;
   procedure Tcp_Accept
     (Pcb : TCB_Id;
      Cb  : Accept_Cb_Id);

   subtype Connect_Cb_Id is AIP.Callbacks.Callback_Id;
   function Tcp_Connect
     (Pcb : TCB_Id;
      Addr : AIP.IPaddrs.IPaddr_Id;
      Port : AIP.U16_T;
      Cb : Connect_Cb_Id)
     return AIP.Err_T;

   function Tcp_Write
     (Pcb : TCB_Id;
      Data : AIP.IPTR_T;
      Len : AIP.U16_T;
      Copy : AIP.U8_T)
     return AIP.Err_T;

   subtype Sent_Cb_Id is AIP.Callbacks.Callback_Id;
   procedure Tcp_Sent
     (Pcb : TCB_Id;
      Cb  : Sent_Cb_Id);

   subtype Recv_Cb_Id is AIP.Callbacks.Callback_Id;
   procedure Tcp_Recv
     (Pcb : TCB_Id;
      Cb  : Recv_Cb_Id);

   procedure Tcp_Recved
     (Pcb : TCB_Id;
      Len : AIP.U16_T);

   subtype Poll_Cb_Id is AIP.Callbacks.Callback_Id;
   procedure Tcp_Poll
     (Pcb : TCB_Id;
      Cb  : Poll_Cb_Id;
      Ivl : AIP.U8_T);

   function Tcp_Close (Pcb : TCB_Id) return AIP.Err_T;
   procedure Tcp_Abort (Pcb : TCB_Id);

   subtype Err_Cb_Id is AIP.Callbacks.Callback_Id;
   procedure Tcp_Err (Pcb : TCB_Id; Cb : Err_Cb_Id);

   function Tcp_Sndbuf (Pcb : TCB_Id) return AIP.U16_T;

private
   pragma Import (C, Tcp_Arg, "tcp_arg");
   pragma Import (C, Tcp_New, "tcp_new");
   pragma Import (C, Tcp_Bind, "tcp_bind");
   pragma Import (C, Tcp_Listen_BL, "tcp_listen_with_backlog");
   pragma Import (C, Tcp_Accept, "tcp_accept");
   pragma Import (C, Tcp_Accepted, "tcp_accepted");
   pragma Import (C, Tcp_Connect, "tcp_connect");
   pragma Import (C, Tcp_Write, "tcp_write");
   pragma Import (C, Tcp_Sent, "tcp_sent");
   pragma Import (C, Tcp_Recv, "tcp_recv");
   pragma Import (C, Tcp_Recved, "tcp_recved");

   pragma Import (C, Tcp_Poll, "tcp_poll");
   pragma Import (C, Tcp_Close, "tcp_close");
   pragma Import (C, Tcp_Abort, "tcp_abort");
   pragma Import (C, Tcp_Err, "tcp_err");

   pragma Import (C, Tcp_Sndbuf, "tcp_sndbuf_w");

end AIP.TCP;
