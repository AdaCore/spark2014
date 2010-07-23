------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.ARP;
with AIP.NIF;
with AIP.Platform;
with AIP.TCP;
with AIP.Timers;

package body AIP.OSAL.Single is

   function Netif_Isr (Nid : NIF.Netif_Id) return Integer;
   pragma Import (C, Netif_Isr, Platform.If_ISR_Linkname);

   ------------------------------
   -- Process_Interface_Events --
   ------------------------------

   function Process_Interface_Events return Integer is
   begin
      return Netif_Isr (If_Id);
   end Process_Interface_Events;

   --------------------
   -- Process_Timers --
   --------------------

   procedure Process_Timers (Now : Time_Types.Time) is
   begin
      if Timers.Timer_Fired (Now, AIP.Timers.TIMER_EVT_TCPFASTTMR) then
         TCP.TCP_Fast_Timer;
      end if;

      if Timers.Timer_Fired (Now, AIP.Timers.TIMER_EVT_TCPSLOWTMR) then
         TCP.TCP_Slow_Timer;
      end if;

      if Timers.Timer_Fired (Now, AIP.Timers.TIMER_EVT_ETHARPTMR) then
         ARP.ARP_Timer;
      end if;
   end Process_Timers;

end AIP.OSAL.Single;
