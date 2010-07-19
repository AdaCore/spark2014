------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP stack OS adaptation layer, Single task version

--  This unit provides the required facilities to integrate the IP stack
--  within a single task environment.

package AIP.OSAL.Single is

   function Process_Interface_Events return Integer;
   --  Process any events on network interfaces, and return count of processed
   --  events.

end AIP.OSAL.Single;
