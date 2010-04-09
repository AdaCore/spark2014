------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;

with NCO_Udpecho;
pragma Unreferenced (NCO_Udpecho);

with NCO_Tcpecho;
pragma Unreferenced (NCO_Tcpecho);

with RAW_Tcpecho;
pragma Unreferenced (RAW_Tcpecho);

procedure Adaservices is
   Opt : String := "-d" & ASCII.NUL;
   Argv : array (0  .. 1) of System.Address :=
     (0 => Opt'Address, 1 => System.Null_Address);

   procedure Simhost_Main (Argc : Integer; Argv : System.Address);
   pragma Import (C, Simhost_Main, "simhost_main");
begin
   Simhost_Main (1, Argv'Address);
end Adaservices;
