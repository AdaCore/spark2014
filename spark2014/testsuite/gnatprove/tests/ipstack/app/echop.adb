------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Text_IO;

with Raw_TCPEcho;
with AIP.Mainloop;

procedure Echop is
   procedure LWIP_init;
   pragma Import (C, LWIP_init, "C_init");
begin
   Ada.Text_IO.Put_Line ("*** IPStack starting ***");
   LWIP_Init;
   Raw_TCPEcho.Init;
   AIP.Mainloop;
end Echop;
