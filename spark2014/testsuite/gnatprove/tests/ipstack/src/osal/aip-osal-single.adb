------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP_Support.Platform;

package body AIP.OSAL.Single is

   function Netif_Isr return Integer;
   pragma Import (C, Netif_Isr, AIP_Support.Platform.If_ISR_Linkname);

   ------------------------------
   -- Process_Interface_Events --
   ------------------------------

   function Process_Interface_Events return Integer is
   begin
      return Netif_Isr;
   end Process_Interface_Events;

end AIP.OSAL.Single;
