------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  General Internet-ting facilities

--# inherit AIP.Config;

package AIP.Inet is

   -----------------
   -- hton family --
   -----------------

   --  These all return host value V converted as needed to the network byte
   --  ordering ordering scheme.

   function htonlm (V : AIP.M32_T) return AIP.M32_T;
   function htonlu (V : AIP.U32_T) return AIP.U32_T;

   function htonsm (V : AIP.M16_T) return AIP.M16_T;
   function htonsu (V : AIP.U16_T) return AIP.U16_T;

   -----------------
   -- ntoh family --
   -----------------

   --  These all return network ordered value V converted as needed to
   --  host byte ordering scheme.

   function ntohlm (V : AIP.M32_T) return AIP.M32_T;
   function ntohlu (V : AIP.U32_T) return AIP.U32_T;

   function ntohsm (V : AIP.M16_T) return AIP.M16_T;
   function ntohsu (V : AIP.U16_T) return AIP.U16_T;

   -------------------------------------
   -- Basic network layer abstraction --
   -------------------------------------

   type Inet_Layer is (LINK_LAYER, IP_LAYER, TRANSPORT_LAYER);

   function HLEN_To (L : Inet_Layer) return AIP.U16_T;
   --  How much room, in bytes, do we need for protocol headers
   --  for data to be sent from layer L.

end AIP.Inet;
