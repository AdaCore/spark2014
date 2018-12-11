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

with HW.GFX.GMA.Registers;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.PCH.HDMI
is

   PCH_HDMI_ENABLE               : constant := 1 * 2 ** 31;
   PCH_HDMI_COLOR_FORMAT_8BPC    : constant := 0 * 2 ** 26;
   PCH_HDMI_COLOR_FORMAT_12BPC   : constant := 3 * 2 ** 26;
   PCH_HDMI_COLOR_FORMAT_MASK    : constant := 7 * 2 ** 26;
   PCH_HDMI_SDVO_ENCODING_SDVO   : constant := 0 * 2 ** 10;
   PCH_HDMI_SDVO_ENCODING_HDMI   : constant := 2 * 2 ** 10;
   PCH_HDMI_SDVO_ENCODING_MASK   : constant := 3 * 2 ** 10;
   PCH_HDMI_VSYNC_ACTIVE_HIGH    : constant := 1 * 2 **  4;
   PCH_HDMI_HSYNC_ACTIVE_HIGH    : constant := 1 * 2 **  3;
   PCH_HDMI_PORT_DETECT          : constant := 1 * 2 **  2;

   PCH_HDMI_MASK : constant Word32 :=
      PCH_TRANSCODER_SELECT_MASK or
      PCH_HDMI_ENABLE or
      PCH_HDMI_COLOR_FORMAT_MASK or
      PCH_HDMI_SDVO_ENCODING_MASK or
      PCH_HDMI_HSYNC_ACTIVE_HIGH or
      PCH_HDMI_VSYNC_ACTIVE_HIGH;

   type PCH_HDMI_Array is array (PCH_HDMI_Port) of Registers.Registers_Index;
   PCH_HDMI : constant PCH_HDMI_Array := PCH_HDMI_Array'
     (PCH_HDMI_B => Registers.PCH_HDMIB,
      PCH_HDMI_C => Registers.PCH_HDMIC,
      PCH_HDMI_D => Registers.PCH_HDMID);

   ----------------------------------------------------------------------------

   procedure On (Port_Cfg : Port_Config; FDI_Port : FDI_Port_Type)
   is
      Polarity : constant Word32 :=
        (if Port_Cfg.Mode.H_Sync_Active_High then
            PCH_HDMI_HSYNC_ACTIVE_HIGH else 0) or
        (if Port_Cfg.Mode.V_Sync_Active_High then
            PCH_HDMI_VSYNC_ACTIVE_HIGH else 0);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- registers are just sufficient for setup with DVI adaptor

      Registers.Unset_And_Set_Mask
         (Register   => PCH_HDMI (Port_Cfg.PCH_Port),
          Mask_Unset => PCH_HDMI_MASK,
          Mask_Set   => PCH_HDMI_ENABLE or
                        PCH_TRANSCODER_SELECT (FDI_Port) or
                        PCH_HDMI_SDVO_ENCODING_HDMI or
                        Polarity);
   end On;

   ----------------------------------------------------------------------------

   procedure Off (Port : PCH_HDMI_Port)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
         (Register   => PCH_HDMI (Port),
          Mask_Unset => PCH_HDMI_MASK,
          Mask_Set   => PCH_HDMI_HSYNC_ACTIVE_HIGH or
                        PCH_HDMI_VSYNC_ACTIVE_HIGH);
   end Off;

   procedure All_Off
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      for Port in PCH_HDMI_Port loop
         Off (Port);
      end loop;
   end All_Off;

end HW.GFX.GMA.PCH.HDMI;
