------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Expose SPARK abstract global entities

--# inherit AIP;

package AIP.Pools
--# own PBUF_POOL;
--# initializes PBUF_POOL;
is
   PBUF_POOL : Integer := 0;
end AIP.Pools;
