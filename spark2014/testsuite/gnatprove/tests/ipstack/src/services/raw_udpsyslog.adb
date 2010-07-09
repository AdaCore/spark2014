------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Buffers;
with AIP.Callbacks;
with AIP.Conversions;
with AIP.IPaddrs;
with AIP.UDP;

use type AIP.EID;
--  use type AIP.IPTR_T;

package body RAW_Udpsyslog
   --# own CB_IDENTIFIERS is Syslog_Recv_Cb_Id;
is

   --  Callback identifiers

   Syslog_Recv_Cb_Id : AIP.Callbacks.CBK_Id;

   procedure Memcpy (Dst : AIP.IPTR_T; Src : String; Len : Integer);
   pragma Import (C, Memcpy, "memcpy");

   --------------------
   -- Syslog_Recv_Cb --
   --------------------

   procedure Syslog_Recv_Cb
     (Arg : AIP.IPTR_T;
      Ucb : AIP.UDP.PCB_Id;
      Pbu : AIP.Buffers.Buffer_Id;
      Ipa : AIP.IPaddrs.IPaddr;
      Pno : AIP.U16_T)
      --# global in out AIP.Pools.Buffer_POOL;
   is
      pragma Unreferenced (Arg, Ipa, Pno);
      --  Process datagram received on our syslog port.  We build a packet
      --  buffer with a valid user.debug syslog header + the start of an
      --  unstructured data block, catenate the incoming Buffer (expected to
      --  contain some applicative log message), and send that over udp to
      --  the syslog port of a well known peer where we have setup a syslogd
      --  to listen.

      --  Preliminary data (syslog header + start of data), to which
      --  we'll catenate the incoming Buffer:

      Logheader : constant String
        := "<15>1 2010-04-20T12:30:00.00Z 192.168.0.2 msglogger - 666";
      --  Syslog header per se ...
      --  PRI VERSION SP STAMP SP HOSTNAME SP APPNAME SP PROCID SP MSGID
      --
      --  Fake everything except PRI, user.debug, 1*8 + 7

      Logdata : constant String := "- AIP syslog bridge: ";
      --  Start of data in syslog message we will send, unstructured.
      --  SD [SP MSG]

      Logmsgstart : constant String := Logheader & " " & Logdata;

      --  Packet buffer to hold the message start and to which we'll chain the
      --  incoming Buffer:

      Logbuf : AIP.Buffers.Buffer_Id;

      --  IP of real syslog server to which we'll forward

      Syslogd_IP : AIP.IPaddrs.IPaddr;

      Err : AIP.Err_T;

   begin

      --  Allocate the packet buffer for the message start. We will copy data
      --  straight from the payload start and need to make sure that enough
      --  contiguous room is available from there. Request a RAM_Buffer for
      --  this purpose. This will all be sent over UDP, so declare TRANSPORT
      --  layer to get room for the necessary headers as well.

      AIP.Buffers.Buffer_Alloc
        (Offset => AIP.UDP.UDP_Payload_Offset,
         Size   => Logmsgstart'Length,
         Kind   => AIP.Buffers.MONO_BUF,
         Buf    => Logbuf);

      --  Fill the buffer and catenate the incoming one. We won't free the
      --  latter on its own so use 'cat' and not 'chain' here.

      Memcpy (AIP.Buffers.Buffer_Payload (Logbuf),
              Logmsgstart, Logmsgstart'Length);

      AIP.Buffers.Buffer_Cat (Logbuf, Pbu);

      --  Connect our PCB to the intended destination and send

      Syslogd_IP := AIP.IPaddrs.IP4 (192, 168, 0, 1);
      AIP.UDP.Udp_Connect (Ucb, Syslogd_IP, 514, Err);
      if AIP.No (Err) then
         AIP.UDP.Udp_Send    (Ucb, Logbuf, Err);
      end if;

      --  Release the Buffer chain we have processed and disconnect our PCB so
      --  that it accepts further incoming messages from other endpoints. This
      --  also makes sure that the local IP address object we have used isn't
      --  referenced later on.

      AIP.Buffers.Buffer_Blind_Free (Logbuf);
      AIP.UDP.UDP_Disconnect (Ucb);

   end Syslog_Recv_Cb;

   ----------
   -- Init --
   ----------

   procedure Init
      --# global out Syslog_Recv_Cb_Id;
   is
      Ucb : AIP.UDP.PCB_Id;
      Err : AIP.Err_T;

      procedure Init_CB_IDENTIFIERS
         --# global out Syslog_Recv_Cb_Id;
         --  See AIP.Callbacks for the rationale
      is
         --# hide Init_CB_IDENTIFIERS
      begin
         Syslog_Recv_Cb_Id :=
           AIP.Conversions.To_IPTR (Syslog_Recv_Cb'Address);
      end Init_CB_IDENTIFIERS;
   begin

      --  Initialize the callback identifiers, allocate a UDP Protocol Control
      --  Block, hook the data reception callback and bind to syslog port for
      --  any possible source IP.

      Init_CB_IDENTIFIERS;

      AIP.UDP.Udp_New (Ucb);
      if Ucb = AIP.UDP.NOPCB then
         null;

      else
         AIP.UDP.UDP_Set_Udata (Ucb, AIP.NULIPTR);
         AIP.UDP.UDP_Callback (AIP.UDP.UDP_RECV, Ucb, Syslog_Recv_Cb_Id);
         AIP.UDP.Udp_Bind (Ucb, AIP.IPaddrs.IP_ADDR_ANY, 514, Err);
      end if;
   end Init;

end RAW_Udpsyslog;
