------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System, AIP_Ctypes, AIP_IPaddrs;

package AIP_TCP is

   type TCB_Id is private;
   NOTCB : constant TCB_Id;

   subtype Callback_Id is System.Address;

   procedure Tcp_Arg (Pcb : TCB_Id; Arg : System.Address);

   function Tcp_New return TCB_Id;

   function Tcp_Bind
     (Pcb : TCB_Id;
      Addr : AIP_IPaddrs.IPaddr_Id;
      Port : AIP_Ctypes.U16_T)
     return AIP_Ctypes.Err_T;

   function Tcp_Listen
     (Pcb : TCB_Id)
     return TCB_Id;

   function Tcp_Listen_BL
     (Pcb : TCB_Id;
      Blog : AIP_Ctypes.U8_T)
     return TCB_Id;

   procedure Tcp_Accepted (Pcb : TCB_Id);

   subtype Accept_Cb_Id is System.Address;
   procedure Tcp_Accept
     (Pcb : TCB_Id;
      Cb  : Accept_Cb_id);

   subtype Connect_Cb_Id is System.Address;
   function Tcp_Connect
     (Pcb : TCB_Id;
      Addr : AIP_IPaddrs.IPaddr_Id;
      Port : AIP_Ctypes.U16_T;
      Cb : Connect_Cb_Id)
     return AIP_Ctypes.Err_T;

   function Tcp_Write
     (Pcb : TCB_Id;
      Data : System.Address;
      Len : AIP_Ctypes.U16_T;
      Copy : AIP_Ctypes.U8_T)
     return AIP_Ctypes.Err_T;

   subtype Sent_Cb_Id is System.Address;
   procedure Tcp_Sent
     (Pcb : TCB_Id;
      Cb  : Sent_Cb_id);

   subtype Recv_Cb_Id is System.Address;
   procedure Tcp_Recv
     (Pcb : TCB_Id;
      Cb  : Recv_Cb_id);

   procedure Tcp_Recved
     (Pcb : TCB_Id;
      Len : AIP_Ctypes.U16_T);

   subtype Poll_Cb_Id is System.Address;
   procedure Tcp_Poll
     (Pcb : TCB_Id;
      Interval : AIP_Ctypes.U8_T;
      Cb : Poll_Cb_Id);

   function Tcp_Close (Pcb : TCB_Id) return AIP_Ctypes.Err_T;
   procedure Tcp_Abort (Pcb : TCB_Id);

   subtype Err_Cb_Id is System.Address;
   procedure Tcp_Err (Pcb : TCB_Id; Cb : Err_Cb_Id);

private
   type TCB is null record;
   type TCB_Id is access TCB;
   NOTCB : constant TCB_Id := null;

   pragma Import (C, Tcp_Arg, "tcp_arg");
   pragma Import (C, Tcp_New, "tcp_new");
   pragma Import (C, Tcp_Bind, "tcp_bind");
   pragma Import (C, Tcp_Listen_BL, "tcp_listen_with_backlog");
   pragma Import (C, Tcp_Accept, "tcp_accept");
   pragma Import (C, Tcp_Accepted, "tcp_accepted");
   pragma Import (C, Tcp_Connect, "tcp_connect");
   pragma Import (C, Tcp_Write, "tcp_write");
   pragma Import (C, Tcp_Sent, "tcp_went");
   pragma Import (C, Tcp_Recv, "tcp_recv");
   pragma Import (C, Tcp_Recved, "tcp_recved");

   pragma Import (C, Tcp_Poll, "tcp_poll");
   pragma Import (C, Tcp_Close, "tcp_close");
   pragma Import (C, Tcp_Abort, "tcp_abort");
   pragma Import (C, Tcp_Err, "tcp_err");

end AIP_TCP;
