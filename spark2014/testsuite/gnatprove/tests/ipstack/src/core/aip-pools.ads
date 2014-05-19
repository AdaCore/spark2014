------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Expose SPARK abstract global entities

package AIP.Pools with
  Initializes => PBUF_POOL
is
   PBUF_POOL : Integer := 0;
end AIP.Pools;
