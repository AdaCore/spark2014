------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP configuration parameters

--# inherit AIP;

package AIP.Config is
   HOST_BIG_ENDIAN : constant Boolean := False;

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;
end AIP.Config;
