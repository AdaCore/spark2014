--
-- Copyright (C) 2016 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

with HW.GFX.GMA.PCH;

private package HW.GFX.GMA.Connectors.FDI
is

   subtype GPU_FDI_Port is GPU_Port range DIGI_B .. DIGI_D;

   type PCH_FDI_Mapping is array (GPU_FDI_Port) of PCH.FDI_Port_Type;
   PCH_FDIs : constant PCH_FDI_Mapping :=
     (DIGI_B => PCH.FDI_A,
      DIGI_C => PCH.FDI_B,
      DIGI_D => PCH.FDI_C);

   type Off_Type is (Link_Off, Clock_Off);

   ----------------------------------------------------------------------------

   procedure Pre_On (Port_Cfg : Port_Config)
   with
      Pre => Port_Cfg.Port in GPU_FDI_Port;

   procedure Post_On
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   with
      Pre => Port_Cfg.Port in GPU_FDI_Port;

   procedure Off (Port : GPU_FDI_Port; OT : Off_Type);

end HW.GFX.GMA.Connectors.FDI;
