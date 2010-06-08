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

--  A high level view of the package hierarchy contents follows:

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
--  AIP.Callbacks

--  AIP.Ipaddrs         IP addresses, netmasks, ...
--  AIP.Pbufs           Packet buffers

--  User level
--  ----------
--  AIP.Tcp             Base TCP services, raw callback API

with AIP_Constants;
--# inherit AIP_Constants;

package AIP is
   --# accept W, 3, "Pragma - ignored by the SPARK Examiner";
   pragma Pure;
   --# end accept;

   -------------------------
   -- Original LWIP types --
   -------------------------

   --  We need these for straight LWIP binding purposes, as a first step, and
   --  we might as well reuse them for our own internal needs.

   type S8_T is range -2 ** 7 .. 2 ** 7 - 1;
   type S16_T is range -2 ** 15 .. 2 ** 15 - 1;

   type U8_T is mod 2 ** 8;
   type U16_T is mod 2 ** 16;
   type U32_T is mod 2 ** 32;

   subtype Err_T is S8_T;
   NOERR : constant Err_T := 0;
   ERR_MEM  : constant Err_T := -1;
   ERR_ABRT : constant Err_T := -4;
   ERR_USE  : constant Err_T := -10;

   ----------------------------
   -- Software Pointer types --
   ----------------------------

   --  We have no access types in SPARK, so rely on bare unsigned integers to
   --  index into static arrays. These need to be machine address size as long
   --  as we use them as machine pointers to interface with the original LWIP
   --  implementation.

   IPTR_BITS : constant := AIP_Constants.Address_Size;
   type IPTR_T is mod 2 ** IPTR_BITS;

   NULIPTR, NULID : constant IPTR_T := 0;

   ---------------------
   -- Host endianness --
   ---------------------

   HOST_BIG_ENDIAN : constant Boolean :=
                       (AIP_Constants.Default_Bit_Order = 0);

end AIP;
