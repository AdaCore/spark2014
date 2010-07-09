------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP.Pools, AIP.IPaddrs, AIP.Pbufs, AIP.Inet,
--#         AIP.Callbacks, AIP.UDP, AIP.Conversions;

--  This unit implements a simplified syslog service over UDP using the RAW
--  API. The service accepts bare string application messages on the well
--  known syslog port (514) and forwards them as real user.debug syslog data
--  to a full fledged syslog server.

package RAW_Udpsyslog
   --# own CB_IDENTIFIERS;
is
   procedure Init;
   --# global out CB_IDENTIFIERS;
   --  Initialize the simplified syslog service
end RAW_Udpsyslog;
