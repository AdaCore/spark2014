------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;

package body AIP.TCP is

   ------------------
   -- TCP_Callback --
   ------------------

   procedure TCP_Callback
     (Evk : TCP_Event_Kind;
      Pcb : PCB_Id;
      Id  : Callbacks.CBK_Id)
   is
      pragma Unreferenced (Evk, Pcb, Id);
   begin
      null;
   end TCP_Callback;

   ----------------
   -- Tcp_Listen --
   ----------------

   function Tcp_Listen (Pcb : PCB_Id) return PCB_Id is
   begin
      return Tcp_Listen_BL (Pcb, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end Tcp_Listen;

end AIP.TCP;
