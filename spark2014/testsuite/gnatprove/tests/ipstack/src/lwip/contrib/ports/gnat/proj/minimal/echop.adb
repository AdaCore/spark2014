------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Assert, Strings, Mainloop, Memory_Compare, Memory_Copy, Memory_Set,
  PPC_Clock, Timers, Time_Types;
with Ada.Text_IO; use Ada.Text_IO;
procedure Echop is
   procedure C_main;
   pragma Import (C, C_Main, "C_main");
begin
   Put_Line ("*** IPStack starting ***");
   C_main;
end Echop;
