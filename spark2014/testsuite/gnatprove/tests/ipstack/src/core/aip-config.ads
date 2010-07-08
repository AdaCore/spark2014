------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP configuration parameters

--# inherit AIP;

package AIP.Config is

   -----------------------
   -- UDP configuration --
   -----------------------

   MAX_UDP_PCB : constant := 20;
   --  Maximum number of UDP PCBs in use at one point
   --  [N (UDP_New) - N(UDP_Release)]

   UDP_TTL : constant := 255;
   --  IP TTL for UDP datagrams

   -----------------------
   -- TCP configuration --
   -----------------------

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;

   Enable_Forwarding : constant Boolean := False;

end AIP.Config;
