------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------


with AIP.Conversions;
with AIP.Support, AIP.IPaddrs, AIP.Inet, AIP.Pbufs, AIP.Callbacks, AIP.UDP;

use type AIP.IPTR_T;

package body RAW_Udpsyslog is

   procedure Memcpy (Dst : AIP.IPTR_T; Src : String; Len : Integer);
   pragma Import (C, Memcpy, "memcpy");

   --------------------
   -- Syslog_Recv_Cb --
   --------------------

   procedure Syslog_Recv_Cb
     (Arg : AIP.IPTR_T;
      Ucb : AIP.UDP.UCB_Id;
      Pbu : AIP.Pbufs.Pbuf_Id;
      Ipa : AIP.IPaddrs.IPaddr_Id;
      Pno : AIP.U16_T)
   is
      --  Process datagram received on our syslog port.  We build a packet
      --  buffer with a valid user.debug syslog header + the start of an
      --  unstructured data block, catenate the incoming pbuf (expected to
      --  contain some applicative log message), and send that over udp to
      --  the syslog port of a well known peer where we have setup a syslogd
      --  to listen.

      --  Craft the preliminary data (syslog header + start of data), to which
      --  we'll catenate the incoming pbuf.

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

      --  Allocate a packet buffer to hold the message start and to which
      --  we'll chain the incoming pbuf. We will copy data straight from the
      --  payload start and need to make sure that enough contiguous room is
      --  available from there. Request a RAM_PBUF for this purpose. This will
      --  all be sent over UDP, so declare TRANSPORT layer to get room for the
      --  necessary headers as well.

      Logbuf : constant AIP.Pbufs.Pbuf_Id
        := AIP.Pbufs.Pbuf_Alloc  (AIP.Pbufs.TRANSPORT_PBUF,
                                  Logmsgstart'Length,
                                  AIP.Pbufs.RAM_PBUF);

      --  Build IP of real syslog server to which we'll forward

      Dest_IP : constant AIP.IPaddrs.IPaddr := AIP.IPaddrs.IP4 (192, 168, 0, 1);

      Err : AIP.Err_T;

   begin

      --  Fill the start packet buffer and catenate the incoming one.  We
      --  won't free the latter on its own so use 'cat' and not 'chain' here.

      Memcpy (AIP.Pbufs.Pbuf_Payload (Logbuf),
              Logmsgstart, Logmsgstart'Length);

      AIP.Pbufs.Pbuf_Cat (Logbuf, Pbu);

      --  Connect our PCB to the intended destination and send

      Err := AIP.UDP.Udp_Connect
        (Ucb, AIP.Conversions.To_IPTR(Dest_Ip'Address), 514);
      Err := AIP.UDP.Udp_Send (Ucb, Logbuf);

      --  Release the pbuf chain we have processed and disconnect our PCB so
      --  that it accepts further incoming messages from other endpoints.

      AIP.Pbufs.Pbuf_Blind_Free (Logbuf);
      AIP.UDP.UDP_Disconnect (Ucb);

   end Syslog_Recv_Cb;

   Syslog_Recv_Cb_Id : constant AIP.UDP.Recv_Cb_Id
     := AIP.Conversions.To_IPTR (Syslog_Recv_Cb'Address);

   ----------
   -- Init --
   ----------

   procedure Init is
      Ucb : AIP.UDP.UCB_Id;
      Err : AIP.Err_T;
   begin

      --  Service initialization : Allocate a UDP Protocol Control Block,
      --  setup the data reception callback and bind to well known syslog
      --  port for any possible source IP.

      Ucb := AIP.UDP.Udp_New;
      if Ucb = AIP.UDP.NOUCB then
         null;
      else
         AIP.UDP.Udp_Recv (Ucb, Syslog_Recv_Cb_Id, AIP.NULIPTR);
         AIP.UDP.Udp_Bind (Ucb, AIP.IPaddrs.IP_ADDR_ANY, 514);
      end if;
   end Init;

end RAW_Udpsyslog;
