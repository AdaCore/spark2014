------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  This is the root of the Ada IP stack package hierarchy.

--  The first intended use is in constrained embedded environments, with very
--  little OS facilities, if any. This inspires our design and implementation
--  in two major ways:

--  * We leverage LWIP, an existing open-source implementation aimed at
--    such environments, mirroring its organization and offering the same
--    "raw" callback oriented api as our user level interface.

--  * We constrain our programming idioms to a close superset of SPARK,
--    to allow real SPARKification later on as need be.

---------------------------
-- Organization overview --
---------------------------

--  Toplevel
--  --------

--  AIP                 Common definitions for all the AIP components

--  Configuration
--  -------------

--  AIP.Config          Configuration parameters (default backlog sizes, ...)

--  Internals
--  ---------

--  AIP.Support         Internal services (Assertion checks ...)
--  AIP.Conversions     Conversion routines

--  AIP.Ipaddrs         IP addresses, netmasks, ...
--  AIP.Buffers         Packet buffers
--  AIP.IP              IP layer abstraction
--  AIP.NIF             Network Interface abstactions

--  Generated units
--  ---------------

--  AIP_Constants       Various constants for properties of the target system

--  AIP.ARPH            ARP packet access
--  AIP.IPH             IP packet access
--  AIP.ICMPH           ICMP packet access
--  AIP.UDPH            UDP packet access
--  AIP.TCPH            TCP packet access

--  User level, with internal parts as well
--  ---------------------------------------

--  AIP.UDP             Base UDP services, raw callback API
--  AIP.TCP             Base TCP services, raw callback API
--  AIP.Callbacks       User callback identifiers
--  AIP.Inet            Internetting facilities (hton/ntoh etc)

with AIP_Constants;

--# inherit AIP_Constants;

package AIP is
   pragma Pure;

   -------------------
   -- Numeric types --
   -------------------

   type S8_T  is range -2 ** 7  .. 2 ** 7 - 1;
   type S16_T is range -2 ** 15 .. 2 ** 15 - 1;
   type S32_T is range -2 ** 31 .. 2 ** 31 - 1;

   type U1_T  is range 0 .. 2 ** 1 - 1;
   type U2_T  is range 0 .. 2 ** 2 - 1;
   type U3_T  is range 0 .. 2 ** 3 - 1;
   type U4_T  is range 0 .. 2 ** 4 - 1;
   type U6_T  is range 0 .. 2 ** 6 - 1;
   type U8_T  is range 0 .. 2 ** 8 - 1;
   type U13_T is range 0 .. 2 ** 13 - 1;
   type U16_T is range 0 .. 2 ** 16 - 1;
   type U32_T is range 0 .. 2 ** 32 - 1;

   type M3_T  is mod 2 ** 3;
   type M8_T  is mod 2 ** 8;
   type M16_T is mod 2 ** 16;
   type M32_T is mod 2 ** 32;

   -----------------
   -- Opaque data --
   -----------------

   subtype Ethernet_Address_Range is Integer range 1 .. 6;
   type Ethernet_Address is array (Ethernet_Address_Range) of U8_T;
   --  48 bit Ethernet address

   subtype Opaque64_Range is Integer range 1 .. 8;
   type Opaque64 is array (Opaque64_Range) of U8_T;
   --  64 bit opaque data (used for copy of original datagram in ICMP messages)

   ----------------------------
   -- Error characterization --
   ----------------------------

   subtype Err_T is S8_T;
   NOERR    : constant Err_T := 0;   -- No error
   ERR_MEM  : constant Err_T := -1;  -- Out of memory
   ERR_ABRT : constant Err_T := -4;  -- ???
   ERR_VAL  : constant Err_T := -8;  -- Illegal Value
   ERR_USE  : constant Err_T := -10; -- ???
   ERR_RTE  : constant Err_T := -3;  -- Routing Error

   function No (Err : Err_T) return Boolean;
   --  True when Err is NOERR

   function Any (Err : Err_T) return Boolean;
   --  True when Err is not NOERR

   ------------------------
   -- Entity identifiers --
   ------------------------

   --  We have no access types in SPARK, so typically expose private
   --  object/entity identifiers which internally are array indices.

   subtype EID is S32_T;
   --  Entity ID. Negative values denote invalid indices

   NULID : constant EID := 0;

   -------------------
   -- Address types --
   -------------------

   IPTR_BITS : constant := AIP_Constants.Address_Size;
   type IPTR_T is mod 2 ** IPTR_BITS;
   --  Integer type with the same size as an address

   NULIPTR : constant IPTR_T := 0;

   ---------------------
   -- Host endianness --
   ---------------------

   HOST_BIG_ENDIAN : constant Boolean :=
                       (AIP_Constants.Default_Bit_Order = 0);

private
   pragma Inline (No);
   pragma Inline (Any);
end AIP;
