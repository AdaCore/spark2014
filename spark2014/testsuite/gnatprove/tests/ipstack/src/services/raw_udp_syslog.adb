------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with System;

with AIP.Buffers;
with AIP.Inet;
with AIP.IPaddrs;

with RAW_UDP_Callbacks;

package body RAW_UDP_Syslog is
   use type AIP.EID;
   use type AIP.Buffers.Buffer_Id;

   procedure Memcpy (Dst : System.Address; Src : String; Len : Integer);
   pragma Import (C, Memcpy, "memcpy");

   procedure SYSLOG_Process_Recv
     (Ev : AIP.UDP.UDP_Event_T; Pcb : AIP.PCBs.PCB_Id)
   is
      --  Process datagram received on our syslog port.  We build a packet
      --  buffer with a valid user.debug syslog header + the start of an
      --  unstructured data block, catenate the incoming Buffer (expected to
      --  contain some applicative log message), and send that over udp to
      --  the syslog port of a well known peer where we have setup a syslogd
      --  to listen.

      Logheader : constant String
        := "<15>Feb  7 12:00:00 ";
      --  Syslog header per se ...
      --  PRI STAMP HOSTNAME SP APPNAME SP PROCID SP MSGID
      --
      --  Fake everything except PRI, user.debug, 1*8 + 7

      Logdata : constant String := "- AIP syslog bridge: ";
      --  Start of data in syslog message we will send, unstructured.
      --  SD [SP MSG]

      Logmsgstart : constant String := Logheader & " " & Logdata;
      --  Preliminary data (syslog header + start of data), to which
      --  we'll catenate the incoming Buffer

      Logbuf : AIP.Buffers.Buffer_Id;
      --  Packet buffer to hold the message start and to which we'll chain the
      --  incoming Buffer.

      Syslogd_IP : AIP.IPaddrs.IPaddr;
      --  IP of real syslog server to which we'll forward

      Err : AIP.Err_T;

   begin

      --  Allocate the packet buffer for the message start. We will copy data
      --  straight from the payload start and need to make sure that enough
      --  contiguous room is available from there. Request a SPLIT_BUF for
      --  this purpose. This will all be sent over UDP, so declare TRANSPORT
      --  layer to get room for the necessary headers as well.

      AIP.Buffers.Buffer_Alloc
        (Offset => AIP.Inet.HLEN_To (AIP.Inet.TRANSPORT_LAYER),
         Size   => Logmsgstart'Length,
         Kind   => AIP.Buffers.SPLIT_BUF,
         Buf    => Logbuf);

      if Logbuf = AIP.Buffers.NOBUF then

         --  Out of memory

         return;
      end if;

      --  Fill the buffer and catenate the incoming one. We won't free the
      --  latter on its own so use 'cat' and not 'chain' here.

      Memcpy (AIP.Buffers.Buffer_Payload (Logbuf),
              Logmsgstart, Logmsgstart'Length);

      AIP.Buffers.Buffer_Chain (Logbuf, Ev.Buf);

      --  Connect our PCB to the intended destination and send

      Syslogd_IP := AIP.IPaddrs.IP4 (192, 168, 0, 1);
      AIP.UDP.UDP_Connect (Pcb, Syslogd_IP, 514, Err);
      pragma Assert (AIP.No (Err));

      AIP.UDP.UDP_Send (Pcb, Logbuf, Err);
      pragma Assert (AIP.No (Err));

      AIP.Buffers.Buffer_Blind_Free (Logbuf);

      --  Release the Buffer chain we have processed and disconnect our PCB so
      --  that it accepts further incoming messages from other endpoints.

      AIP.UDP.UDP_Disconnect (Pcb);

   end SYSLOG_Process_Recv;

   ----------
   -- Init --
   ----------

   procedure Init is
      Pcb : AIP.PCBs.PCB_Id;
      Err : AIP.Err_T;
   begin

      --  Allocate a UDP Protocol Control Block, hook the data reception
      --  callback and bind to syslog port for any possible source IP.

      AIP.UDP.UDP_New (Pcb);
      pragma Assert (Pcb /= AIP.PCBs.NOPCB);

      AIP.UDP.On_UDP_Recv (Pcb, RAW_UDP_Callbacks.SYSLOG_RECV);

      AIP.UDP.UDP_Bind (Pcb, AIP.IPaddrs.IP_ADDR_ANY, 514, Err);
      pragma Assert (AIP.No (Err));
   end Init;

end RAW_UDP_Syslog;
