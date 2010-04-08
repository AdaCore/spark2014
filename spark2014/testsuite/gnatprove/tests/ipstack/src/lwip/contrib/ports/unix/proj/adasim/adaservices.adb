------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System, AIP_Udpecho, AIP_Tcpecho;

procedure Adaservices is
   Argv : array (0  .. 0) of System.Address := (0 => System.Null_Address);

   procedure Simhost_Main (Argc : Integer; Argv : System.Address);
   pragma Import (C, Simhost_Main, "simhost_main");
begin
   Simhost_Main (0, Argv'Address);
end Adaservices;
