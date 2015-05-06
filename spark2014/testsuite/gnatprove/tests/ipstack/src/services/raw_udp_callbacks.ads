------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--         Copyright (C) 2010-2014, Free Software Foundation, Inc.          --
------------------------------------------------------------------------------

--  Callback identifiers for UDP services. In a standalone unit to allow
--  easy sharing without circularities between the callback registrations
--  in service implementations and the events dispatcher.

with AIP.Callbacks;

package RAW_UDP_Callbacks is

   SYSLOG_RECV : constant AIP.Callbacks.CBK_Id := 1;
   --  Datagram received on SYSLOG PCB

end RAW_UDP_Callbacks;
