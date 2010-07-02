------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP Header definition and accessors (internal)

with AIP.IPaddrs;
--# inherit AIP.IPaddrs, AIP.Inet, AIP.Conversions;

package AIP.IPH is

   IP_FIXED_HLEN : constant := 20;

   IP_PROTO_UDP  : constant := 17;
   IP_PROTO_TCP  : constant := 6;
   IP_PROTO_ICMP : constant := 1;

   type IP_Header is record
      Ver     : U4_T;
      Hlen    : U4_T;
      TOS     : U8_T;
      Tlen    : U16_T;
      Id      : U16_T;
      Flags   : M3_T;
      Fragoff : U13_T;
      TTL     : U8_T;
      Proto   : U8_T;
      Sum     : U16_T;
      Src_IP  : IPaddrs.IPaddr;
      Dst_IP  : IPaddrs.IPaddr;
   end record;
   --  ??? rep clause needed here

   function IPH_HLEN (Ihdr : AIP.IPTR_T) return U4_T;

   function IPH_SRC (Ihdr : AIP.IPTR_T) return IPaddrs.IPaddr;
   function IPH_DST (Ihdr : AIP.IPTR_T) return IPaddrs.IPaddr;

private

   pragma Inline (IPH_HLEN);
   pragma Inline (IPH_SRC);
   pragma Inline (IPH_DST);

end AIP.IPH;
