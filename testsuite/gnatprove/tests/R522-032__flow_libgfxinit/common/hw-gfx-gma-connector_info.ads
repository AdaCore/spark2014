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

with HW.GFX.EDID;

private package HW.GFX.GMA.Connector_Info is

   procedure Preferred_Link_Setting
     (Port_Cfg : in out Port_Config;
      Success  :    out Boolean)
   with
      Post =>
         Port_Cfg.Port = Port_Cfg.Port'Old and
         Port_Cfg.Mode = Port_Cfg.Mode'Old;

   procedure Next_Link_Setting
     (Port_Cfg : in out Port_Config;
      Success  :    out Boolean)
   with
      Post =>
         Port_Cfg.Port = Port_Cfg.Port'Old and
         Port_Cfg.Mode = Port_Cfg.Mode'Old;

   function Default_BPC (Port_Cfg : Port_Config) return BPC_Type;

end HW.GFX.GMA.Connector_Info;
