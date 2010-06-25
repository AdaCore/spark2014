------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Text_IO;

with Raw_TCPEcho;
with AIP.Init;
with AIP.Mainloop;

procedure Echop is
begin
   Ada.Text_IO.Put_Line ("*** IPStack starting ***");

   --  Initialize IP stack

   AIP.Init.Initialize;

   --  Initialize application services

   Raw_TCPEcho.Init;

   --  Run application main loop (??? should not be part of AIP)

   AIP.Mainloop;
end Echop;
