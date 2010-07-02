------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;

package body AIP.TCP is

   function Tcp_Listen (Pcb : PCB_Id) return PCB_Id is
   begin
      return Tcp_Listen_BL (Pcb, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end Tcp_Listen;

   procedure TCP_Callback
     (Evk : TCP_Event_Kind; Pcb : PCB_Id; Id : Callbacks.Callback_Id)
   is
   begin
      null;
   end TCP_Callback;

end AIP.TCP;
