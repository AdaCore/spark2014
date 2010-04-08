------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP_Config;

package body AIP_TCP is

   procedure Tcp_Listen (Pcb : TCP_PCB_Id) is
   begin
      Tcp_Listen_Bl (Pcb, AIP_Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end Tcp_Listen;

end AIP_TCP;
