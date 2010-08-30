------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  TCP echo server implementation using the RAW callback API

--# inherit AIP.IPaddrs, AIP.Buffers, AIP.Callbacks, AIP.TCP;

package RAW_TCP_Echo
   --# own ECHO_STATE_POOL;
is

   procedure Init;
   --# global in out ECHO_STATE_POOL;
   --  Setup server to wait for and process connections

end RAW_TCP_Echo;
