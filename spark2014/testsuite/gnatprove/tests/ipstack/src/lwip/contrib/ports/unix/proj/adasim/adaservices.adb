------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# hide Adaservices;

with System;

with RAW_Tcpecho, RAW_Udpsyslog;
pragma Unreferenced (RAW_Tcpecho);
pragma Unreferenced (RAW_Udpsyslog);

procedure Adaservices is
   Opt : String := "-d" & ASCII.NUL;
   Argv : array (0  .. 1) of System.Address :=
     (0 => Opt'Address, 1 => System.Null_Address);

   procedure Simhost_Main (Argc : Integer; Argv : System.Address);
   pragma Import (C, Simhost_Main, "simhost_main");
begin
   Simhost_Main (1, Argv'Address);
end Adaservices;
