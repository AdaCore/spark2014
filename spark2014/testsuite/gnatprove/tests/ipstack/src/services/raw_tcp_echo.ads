------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--         Copyright (C) 2010-2014, Free Software Foundation, Inc.          --
------------------------------------------------------------------------------

--  TCP echo server implementation using the RAW callback API

package RAW_TCP_Echo with
  Abstract_State => ECHO_STATE_POOL
is

   procedure Init
   --  Setup server to wait for and process connections
   with
     Global => (In_Out => ECHO_STATE_POOL);

end RAW_TCP_Echo;
