--
-- Copyright (C) 2016-2017 secunet Security Networks AG
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
with HW.GFX.GMA.Registers;
with HW.GFX.GMA.Config_Helpers;

package body HW.GFX.GMA.Port_Detect
is

   DP_PORT_DETECTED                    : constant := 1 * 2 **  2;
   PCH_DIGI_PORT_DETECTED              : constant := 1 * 2 **  2;
   PCH_LVDS_PORT_DETECTED              : constant := 1 * 2 **  1;

   SHOTPLUG_CTL_DETECT_MASK            : constant := 16#0003_0303#;

   type PCH_Digital_Port_Value is array (PCH_HDMI_Port) of Word32;
   SHOTPLUG_CTL_HPD_INPUT_ENABLE : constant PCH_Digital_Port_Value :=
     (PCH_HDMI_B => 1 * 2 **  4,
      PCH_HDMI_C => 1 * 2 ** 12,
      PCH_HDMI_D => 1 * 2 ** 20);
   SHOTPLUG_CTL_SHORT_PULSE_MASK : constant PCH_Digital_Port_Value :=
     (PCH_HDMI_B => 3 * 2 **  2,
      PCH_HDMI_C => 3 * 2 ** 10,
      PCH_HDMI_D => 3 * 2 ** 18);
   SHOTPLUG_CTL_HPD_STATUS : constant PCH_Digital_Port_Value :=
     (PCH_HDMI_B => 3 * 2 **  0,
      PCH_HDMI_C => 3 * 2 **  8,
      PCH_HDMI_D => 3 * 2 ** 16);
   SHOTPLUG_CTL_LONG_DETECT : constant PCH_Digital_Port_Value :=
     (PCH_HDMI_B => 1 * 2 **  1,
      PCH_HDMI_C => 1 * 2 **  9,
      PCH_HDMI_D => 1 * 2 ** 17);

   type PCH_Digital_Regs is array (PCH_HDMI_Port) of Registers.Registers_Index;
   PCH_HDMI : constant PCH_Digital_Regs :=
     (PCH_HDMI_B => Registers.PCH_HDMIB,
      PCH_HDMI_C => Registers.PCH_HDMIC,
      PCH_HDMI_D => Registers.PCH_HDMID);
   PCH_DP : constant PCH_Digital_Regs :=
     (PCH_HDMI_B => Registers.PCH_DP_B,
      PCH_HDMI_C => Registers.PCH_DP_C,
      PCH_HDMI_D => Registers.PCH_DP_D);

   procedure Initialize
   is
      Internal_Detected,
      HDMI_Detected,
      DP_Detected : Boolean;

      type PCH_Port_To_GMA_Port is array (PCH_HDMI_Port) of Port_Type;
      To_Digital_Port : constant PCH_Port_To_GMA_Port :=
        (PCH_HDMI_B => HDMI1,
         PCH_HDMI_C => HDMI2,
         PCH_HDMI_D => HDMI3);
      To_DP_Port : constant PCH_Port_To_GMA_Port :=
        (PCH_HDMI_B => DP1,
         PCH_HDMI_C => DP2,
         PCH_HDMI_D => DP3);
   begin
      case Config.Internal_Display is
         when LVDS =>
            -- PCH_LVDS
            Registers.Is_Set_Mask
              (Register => Registers.PCH_LVDS,
               Mask     => PCH_LVDS_PORT_DETECTED,
               Result   => Internal_Detected);
         when DP =>
            -- eDP
            Registers.Is_Set_Mask
              (Register => Registers.DP_CTL_A,
               Mask     => DP_PORT_DETECTED,
               Result   => Internal_Detected);
         when None =>
            Internal_Detected := False;
      end case;
      Config.Valid_Port (Internal) := Internal_Detected;

      -- PCH_HDMI_[BCD], PCH_DP_[BCD] share hotplug registers
      for PCH_Port in PCH_HDMI_Port loop
         Registers.Is_Set_Mask
           (Register => PCH_HDMI (PCH_Port),
            Mask     => PCH_DIGI_PORT_DETECTED,
            Result   => HDMI_Detected);
         Config.Valid_Port (To_Digital_Port (PCH_Port)) := HDMI_Detected;

         Registers.Is_Set_Mask
           (Register => PCH_DP (PCH_Port),
            Mask     => PCH_DIGI_PORT_DETECTED,
            Result   => DP_Detected);
         Config.Valid_Port (To_DP_Port (PCH_Port)) := DP_Detected;

         if HDMI_Detected or DP_Detected then
            Registers.Unset_And_Set_Mask
              (Register    => Registers.SHOTPLUG_CTL,
               Mask_Unset  => SHOTPLUG_CTL_DETECT_MASK or
                              SHOTPLUG_CTL_SHORT_PULSE_MASK (PCH_Port),
               Mask_Set    => SHOTPLUG_CTL_HPD_INPUT_ENABLE (PCH_Port) or
                              SHOTPLUG_CTL_HPD_STATUS (PCH_Port));   -- clear
         else
            Registers.Unset_Mask
              (Register => Registers.SHOTPLUG_CTL,
               Mask     => SHOTPLUG_CTL_DETECT_MASK or
                           SHOTPLUG_CTL_HPD_INPUT_ENABLE (PCH_Port));
         end if;
      end loop;
   end Initialize;

   procedure Hotplug_Detect (Port : in Active_Port_Type; Detected : out Boolean)
   is
      Ctl32 : Word32;
      PCH_Port : constant GMA.PCH_Port :=
        (case Port is
            when DP1    => PCH_HDMI_B,
            when DP2    => PCH_HDMI_C,
            when DP3    => PCH_HDMI_D,
            when others => Config_Helpers.To_PCH_Port (Port));
   begin
      if PCH_Port in PCH_HDMI_B .. PCH_HDMI_D then
         Registers.Read (Registers.SHOTPLUG_CTL, Ctl32, Verbose => False);
         Detected := (Ctl32 and SHOTPLUG_CTL_LONG_DETECT (PCH_Port)) /= 0;

         if (Ctl32 and SHOTPLUG_CTL_HPD_STATUS (PCH_Port)) /= 0 then
            Registers.Unset_And_Set_Mask
              (Register    => Registers.SHOTPLUG_CTL,
               Mask_Unset  => SHOTPLUG_CTL_DETECT_MASK,
               Mask_Set    => SHOTPLUG_CTL_HPD_STATUS (PCH_Port));
         end if;
      else
         Detected := False;
      end if;
   end Hotplug_Detect;

   procedure Clear_Hotplug_Detect (Port : Active_Port_Type)
   is
      Ignored_HPD : Boolean;
   begin
      pragma Warnings (GNATprove, Off, "unused assignment to ""Ignored_HPD""",
                       Reason => "We want to clear pending events only");
      Port_Detect.Hotplug_Detect (Port, Ignored_HPD);
      pragma Warnings (GNATprove, On, "unused assignment to ""Ignored_HPD""");
   end Clear_Hotplug_Detect;

end HW.GFX.GMA.Port_Detect;
