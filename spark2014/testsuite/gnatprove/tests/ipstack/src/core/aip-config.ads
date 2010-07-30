------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP configuration parameters

--# inherit AIP;

package AIP.Config is

   pragma Pure;

   ---------------------------
   -- Buffers configuration --
   ---------------------------

   --  Data_Buffer_Size, Data_Buffer_Num and No_Data_Buffer_Num can be
   --  changed according to specific project needs. None of these positive
   --  constants should be zero.

   Data_Buffer_Size : constant := 256;
   --  Size of an individual data buffer

   Data_Buffer_Num : constant := 10;
   --  Total number of data buffers statically allocated

   No_Data_Buffer_Num : constant := 64;
   --  Total number of no-data buffers statically allocated

   ----------------------
   -- NIF configuation --
   ----------------------

   MAX_NETIF : constant := 20;
   --  Maximum number of Network Interfaces in use at a time (including down)

   -----------------------
   -- ARP configuration --
   -----------------------

   Max_ARP_Entries : constant := 20;
   --  ARP table size

   -----------------------
   -- UDP configuration --
   -----------------------

   MAX_UDP_PCB : constant := 20;
   --  Maximum number of UDP PCBs in use at a time
   --  [N (UDP_New) - N(UDP_Release)]

   UDP_TTL : constant := 64;
   --  IP TTL for UDP datagrams

   UDP_SHARED_ENDPOINTS : constant Boolean := False;
   --  Whether we should accept binding to an already used local endpoint

   UDP_LOCAL_PORT_FIRST : constant := 32_768;
   UDP_LOCAL_PORT_LAST  : constant := 49_151;
   --  Range of local port numbers examined when an arbitrary choice needs
   --  to be made

   -----------------------
   -- TCP configuration --
   -----------------------

   MAX_TCP_PCB : constant := 20;
   --  Maximum number for TCP PCBs in use at any time

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;

   Enable_Forwarding : constant Boolean := False;

end AIP.Config;
