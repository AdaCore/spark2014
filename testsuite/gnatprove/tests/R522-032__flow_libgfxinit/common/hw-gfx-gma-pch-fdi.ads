--
-- Copyright (C) 2015-2016 secunet Security Networks AG
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

package HW.GFX.GMA.PCH.FDI is

   type Training_Pattern is (TP_1, TP_2, TP_Idle, TP_None);

   procedure Pre_Train (Port : PCH.FDI_Port_Type; Port_Cfg : Port_Config);
   procedure Train
     (Port     : in     PCH.FDI_Port_Type;
      TP       : in     Training_Pattern;
      Success  :    out Boolean);
   procedure Auto_Train (Port : PCH.FDI_Port_Type);
   procedure Enable_EC (Port : PCH.FDI_Port_Type);

   type Off_Type is (Rx_Off, Lanes_Off, Clock_Off);
   procedure Off (Port : PCH.FDI_Port_Type; OT : Off_Type);

end HW.GFX.GMA.PCH.FDI;
