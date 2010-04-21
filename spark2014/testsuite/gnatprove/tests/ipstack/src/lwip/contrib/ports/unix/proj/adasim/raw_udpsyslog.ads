------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP.Support, AIP.IPaddrs, AIP.Pbufs, AIP.Callbacks, AIP.UDP;

--  This unit implements a simplified syslog service over UDP using the RAW
--  API. The service accepts bare string application messages on the well
--  known syslog port (514) and forwards them as real user.debug syslog data
--  to a full fledged syslog server.

package RAW_Udpsyslog is
   
   procedure Init;
   --  Initialize the simplified syslog service
   
end RAW_Udpsyslog;
