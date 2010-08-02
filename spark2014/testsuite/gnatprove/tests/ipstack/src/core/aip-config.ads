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

   ----------------------
   -- IP configuration --
   ----------------------

   Enable_Forwarding : constant Boolean := False;

   First_Ephemeral_Port : constant := 32_768;
   Last_Ephemeral_Port  : constant := 49_151;
   --  Range of ephemeral ports for UDP and TCP

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

   -----------------------
   -- TCP configuration --
   -----------------------

   MAX_TCP_PCB : constant := 20;
   --  Maximum number for TCP PCBs in use at any time

   TCP_TTL : constant := 64;
   --  IP TTL for TCP segments

   TCP_MSL : constant := 2 * TCP_TTL;
   --  Maximum Segment Life: 2 * TTL (in seconds)

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;

end AIP.Config;
