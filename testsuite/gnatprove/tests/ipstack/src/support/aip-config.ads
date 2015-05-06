------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  AIP configuration parameters

with System;

package AIP.Config is

   pragma Preelaborate;

   ---------------------------
   -- Buffers configuration --
   ---------------------------

   --  Data_Buffer_Size, Data_Buffer_Num and No_Data_Buffer_Num can be
   --  changed according to specific project needs. None of these positive
   --  constants should be zero.

   Data_Buffer_Size : constant := 256;
   --  Size of an individual data buffer

   Data_Buffer_Num : constant := 32;
   --  Total number of data buffers statically allocated

   No_Data_Buffer_Num : constant := 64;
   --  Total number of no-data buffers statically allocated

   ----------------------
   -- NIF configuation --
   ----------------------

   MAX_NETIF : constant := 20;
   --  Maximum number of Network Interfaces in use at a time (including down)

   function Interface_Parameters return System.Address;
   --  Return the address of interface-specific parameters passed to the
   --  driver's initialization routine.

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

   Max_UDP_PCB : constant := 20;
   --  Maximum number of UDP PCBs in use at a time
   --  [N (UDP_New) - N(UDP_Release)]

   UDP_TTL : constant := 64;
   --  IP TTL for UDP datagrams

   UDP_SHARED_ENDPOINTS : constant Boolean := False;
   --  Whether we should accept binding to an already used local endpoint

   -----------------------
   -- TCP configuration --
   -----------------------

   Max_TCP_PCB : constant := 20;
   --  Maximum number for TCP PCBs in use at any time

   TCP_TTL : constant := 64;
   --  IP TTL for TCP segments

   TCP_MSL : constant := 2 * TCP_TTL;
   --  Maximum Segment Life: 2 * TTL (in seconds)

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;

   TCP_WINDOW : constant := 2048;
   --  TCP window size

   TCP_SND_BUF : constant := 512;
   --  TCP send buffer size

   TCP_MAX_SYN_RTX : constant := 6;
   --  Maximum retransmits for initial (SYN) segments

   TCP_MAX_RTX : constant := 12;
   --  Maximum retransmits for data segments

end AIP.Config;
