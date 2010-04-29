------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Strings;
--  Temp hack: force dependency on units required by C code

with Raw_TCPEcho;

with Ada.Text_IO;
with Mainloop;

procedure Echop is
   procedure LWIP_init;
   pragma Import (C, LWIP_init, "C_init");
begin
   Ada.Text_IO.Put_Line ("*** IPStack starting ***");
   LWIP_Init;
   Raw_TCPEcho.Init;
   Mainloop;
end Echop;
