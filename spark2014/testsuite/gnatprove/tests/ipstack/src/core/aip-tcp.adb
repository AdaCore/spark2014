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
      PCB : PCB_Id;
      Id  : Callbacks.CBK_Id)
   is
      pragma Unreferenced (Evk, PCB, Id);
   begin
      null;
   end TCP_Callback;

   ----------------
   -- TCP_Listen --
   ----------------

   function TCP_Listen (PCB : PCB_Id) return PCB_Id is
   begin
      return TCP_Listen_BL (PCB, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end TCP_Listen;

end AIP.TCP;
