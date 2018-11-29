--
-- Copyright (C) 2015-2017 secunet Security Networks AG
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

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Panel;
with HW.GFX.GMA.DP_Info;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.Connector_Info is

   procedure Preferred_Link_Setting
     (Port_Cfg    : in out Port_Config;
      Success     :    out Boolean)
   is
      DP_Port : constant GMA.DP_Port :=
        (if Port_Cfg.Port = DIGI_A then
            DP_A
         else
           (case Port_Cfg.PCH_Port is
               when PCH_DP_B  => DP_B,
               when PCH_DP_C  => DP_C,
               when PCH_DP_D  => DP_D,
               when others    => GMA.DP_Port'First));
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Port_Cfg.Display = DP then
         if Port_Cfg.Port = DIGI_A then
            if GMA.Config.Use_PP_VDD_Override then
               Panel.VDD_Override;
            else
               Panel.On;
            end if;
         end if;

         DP_Info.Read_Caps
           (Link     => Port_Cfg.DP,
            Port     => DP_Port,
            Success  => Success);
         if Success then
            DP_Info.Preferred_Link_Setting
              (Link     => Port_Cfg.DP,
               Mode     => Port_Cfg.Mode,
               Success  => Success);
            pragma Debug (Success, DP_Info.Dump_Link_Setting (Port_Cfg.DP));
         end if;
      else
         Success := True;
      end if;
   end Preferred_Link_Setting;

   procedure Next_Link_Setting
     (Port_Cfg : in out Port_Config;
      Success  :    out Boolean)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Port_Cfg.Display = DP then
         DP_Info.Next_Link_Setting
           (Link     => Port_Cfg.DP,
            Mode     => Port_Cfg.Mode,
            Success  => Success);
         pragma Debug (Success, DP_Info.Dump_Link_Setting (Port_Cfg.DP));
      else
         Success := False;
      end if;
   end Next_Link_Setting;

   ----------------------------------------------------------------------------

   function Default_BPC (Port_Cfg : Port_Config) return HW.GFX.BPC_Type
   is
   begin
      return
        (if Port_Cfg.Port = DIGI_A or
           (Port_Cfg.Is_FDI and Port_Cfg.PCH_Port = PCH_LVDS) or
           Port_Cfg.Port = LVDS
         then 6
         else 8);
   end Default_BPC;

end HW.GFX.GMA.Connector_Info;
