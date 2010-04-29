------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  General Internet-ting facilities

--# inherit AIP.Config;

package AIP.Inet is

   function htonl (V : AIP.U32_T) return AIP.U32_T;
   --  Return host value V converted as needed to the network byte ordering
   --  ordering scheme.

end AIP.Inet;
