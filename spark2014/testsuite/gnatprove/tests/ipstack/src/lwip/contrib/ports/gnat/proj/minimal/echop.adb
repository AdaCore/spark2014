------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Assert, Mainloop, Memory_Compare, Memory_Copy, Memory_Set,
  Strings, PPC_Clock, Timers, Time_Types;
procedure Echop is
   procedure C_main;
   pragma Import (C, C_Main, "C_main");
begin
   C_main;
end Echop;
