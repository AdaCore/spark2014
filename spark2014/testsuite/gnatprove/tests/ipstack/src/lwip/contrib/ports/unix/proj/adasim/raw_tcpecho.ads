------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  TCP echo server implementation using the RAW callback API

--# inherit AIP.Support, AIP. AIP.IPaddrs, AIP.Pbufs, AIP.Callbacks;
--# inherit AIP.TCP;

package RAW_Tcpecho is

   procedure Init;
   --  Setup server to wait for and process connections

end RAW_Tcpecho;
