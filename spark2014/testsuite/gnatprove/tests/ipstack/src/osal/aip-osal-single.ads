------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IP stack OS adaptation layer, Single task version

--  This unit provides the required facilities to integrate the IP stack
--  within a single task environment.

with AIP.Time_Types;

package AIP.OSAL.Single is

   function Process_Interface_Events return Integer;
   --  Process any events on network interfaces, and return count of processed
   --  events.

   procedure Process_Timers (Now : Time_Types.Time);
   --  Process all timers that have fired since the last check

end AIP.OSAL.Single;
