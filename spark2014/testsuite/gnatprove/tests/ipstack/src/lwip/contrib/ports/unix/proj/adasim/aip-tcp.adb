------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.Config;

package body AIP.TCP is

   function Tcp_Listen (Pcb : TCB_Id) return TCB_Id is
   begin
      return Tcp_Listen_BL (Pcb, Config.TCP_DEFAULT_LISTEN_BACKLOG);
   end Tcp_Listen;

end AIP.TCP;
