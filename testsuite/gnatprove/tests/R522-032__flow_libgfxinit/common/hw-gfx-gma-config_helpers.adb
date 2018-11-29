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

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Connector_Info;
with HW.GFX.GMA.DP_Info;
with HW.GFX.GMA.Registers;

with HW.Debug;

package body HW.GFX.GMA.Config_Helpers
is

   function To_GPU_Port
     (Pipe : Pipe_Index;
      Port : Active_Port_Type)
      return GPU_Port
   is
   begin
      return
        (case Config.CPU is
            when G45 =>
               (case Port is
                   when Internal     => LVDS,
                   when HDMI1 | DP1  => DIGI_B,
                   when HDMI2 | DP2  => DIGI_C,
                   when HDMI3 | DP3  => DIGI_D,
                   when Analog       => VGA),
            when Ironlake .. Ivybridge => -- everything but eDP through FDI/PCH
              (if Config.Internal_Is_EDP and then Port = Internal then
                  DIGI_A
               else
                 (case Pipe is
                     -- FDIs are fixed to the CPU pipe
                     when Primary   => DIGI_B,
                     when Secondary => DIGI_C,
                     when Tertiary  => DIGI_D)),
            when Haswell .. Skylake =>    -- everything but VGA directly on CPU
              (case Port is
                  when Internal     => DIGI_A,  -- LVDS not available
                  when HDMI1 | DP1  => DIGI_B,
                  when HDMI2 | DP2  => DIGI_C,
                  when HDMI3 | DP3  => DIGI_D,
                  when Analog       => DIGI_E));
   end To_GPU_Port;

   function To_PCH_Port (Port : Active_Port_Type) return PCH_Port
   is
   begin
      return
        (case Port is
            when Internal  => PCH_LVDS,   -- will be ignored if Internal is DP
            when Analog    => PCH_DAC,
            when HDMI1     => PCH_HDMI_B,
            when HDMI2     => PCH_HDMI_C,
            when HDMI3     => PCH_HDMI_D,
            when DP1       => PCH_DP_B,
            when DP2       => PCH_DP_C,
            when DP3       => PCH_DP_D);
   end To_PCH_Port;

   function To_Display_Type (Port : Active_Port_Type) return Display_Type
   is
   begin
      return Display_Type'
        (case Port is
            when Internal        => Config.Internal_Display,
            when Analog          => VGA,
            when HDMI1 .. HDMI3  => HDMI,
            when DP1 .. DP3      => DP);
   end To_Display_Type;

   ----------------------------------------------------------------------------

   -- Prepares link rate and lane count settings for an FDI connection.
   procedure Configure_FDI_Link
     (Port_Cfg : in out Port_Config;
      Success  :    out Boolean)
   with Pre => True
   is
      procedure Limit_Lane_Count
      is
         FDI_TX_CTL_FDI_TX_ENABLE : constant := 1 * 2 ** 31;
         Enabled : Boolean;
      begin
         -- if DIGI_D enabled: (FDI names are off by one)
         Registers.Is_Set_Mask
           (Register => Registers.FDI_TX_CTL_C,
            Mask     => FDI_TX_CTL_FDI_TX_ENABLE,
            Result   => Enabled);
         if Enabled then
            Port_Cfg.FDI.Receiver_Caps.Max_Lane_Count := DP_Lane_Count_2;
         end if;
      end Limit_Lane_Count;
   begin
      Port_Cfg.FDI.Receiver_Caps.Max_Link_Rate    := DP_Bandwidth_2_7;
      Port_Cfg.FDI.Receiver_Caps.Max_Lane_Count   :=
         Config.FDI_Lane_Count (Port_Cfg.Port);
      Port_Cfg.FDI.Receiver_Caps.Enhanced_Framing := True;
      if Config.Has_FDI_C and then Port_Cfg.Port = DIGI_C then
         Limit_Lane_Count;
      end if;
      DP_Info.Preferred_Link_Setting (Port_Cfg.FDI, Port_Cfg.Mode, Success);
   end Configure_FDI_Link;

   -- Derives an internal port config.
   --
   -- This is where the magic happens that hides the hardware details
   -- from libgfxinit's users. We have to map the pipe (Pipe_Index),
   -- the user visible port (Port_Type) and the modeline (Mode_Type)
   -- that we are supposed to output to an internal representation
   -- (Port_Config) that applies to the selected hardware generation
   -- (in GMA.Config).
   procedure Fill_Port_Config
     (Port_Cfg :    out Port_Config;
      Pipe     : in     Pipe_Index;
      Port     : in     Port_Type;
      Mode     : in     Mode_Type;
      Success  :    out Boolean)
   is
   begin
      Success :=
         (Config.Has_Tertiary_Pipe or Pipe <= Secondary) and then
         Config.Valid_Port (Port) and then
         Port /= Disabled; -- Valid_Port should already cover this, but the
                           -- array is writeable, so it's hard to prove this.

      if Success then
         Port_Cfg := Port_Config'
           (Port     => To_GPU_Port (Pipe, Port),
            PCH_Port => To_PCH_Port (Port),
            Display  => To_Display_Type (Port),
            Mode     => Mode,
            Is_FDI   => Config.Is_FDI_Port (Port),
            FDI      => Default_DP,
            DP       => Default_DP);

         if Port_Cfg.Mode.BPC = Auto_BPC then
            Port_Cfg.Mode.BPC := Connector_Info.Default_BPC (Port_Cfg);
         end if;

         if Port_Cfg.Display = HDMI then
            declare
               pragma Assert (Config.HDMI_Max_Clock_24bpp * 8
                              / Port_Cfg.Mode.BPC >= Frequency_Type'First);
               Max_Dotclock : constant Frequency_Type :=
                  Config.HDMI_Max_Clock_24bpp * 8 / Port_Cfg.Mode.BPC;
            begin
               if Port_Cfg.Mode.Dotclock > Max_Dotclock then
                  pragma Debug (Debug.Put ("Dotclock "));
                  pragma Debug (Debug.Put_Int64 (Port_Cfg.Mode.Dotclock));
                  pragma Debug (Debug.Put (" too high, limiting to "));
                  pragma Debug (Debug.Put_Int64 (Max_Dotclock));
                  pragma Debug (Debug.Put_Line ("."));
                  Port_Cfg.Mode.Dotclock := Max_Dotclock;
               end if;
            end;
         end if;

         if Port_Cfg.Is_FDI then
            Configure_FDI_Link (Port_Cfg, Success);
         end if;
      else
         Port_Cfg := Port_Config'
           (Port     => GPU_Port'First,
            PCH_Port => PCH_Port'First,
            Display  => Display_Type'First,
            Mode     => Invalid_Mode,
            Is_FDI   => False,
            FDI      => Default_DP,
            DP       => Default_DP);
      end if;
   end Fill_Port_Config;

   ----------------------------------------------------------------------------

   -- Validates that a given configuration should work with
   -- a given framebuffer.
   function Validate_Config
     (FB                : Framebuffer_Type;
      Mode              : Mode_Type;
      Pipe              : Pipe_Index;
      Scaler_Available  : Boolean)
      return Boolean
   is
   begin
      -- No downscaling
      -- Respect maximum scalable width
      -- VGA plane is only allowed on the primary pipe
      -- Only 32bpp RGB (ignored for VGA plane)
      -- Stride must be big enough and a multiple of 64 bytes or the tile size
      -- (ignored for VGA plane)
      -- Y-Tiling and rotation are only supported on newer generations (with
      -- Plane_Control)
      -- 90 degree rotations are only supported with Y-tiling
      return
         ((Rotated_Width (FB) = Mode.H_Visible and
           Rotated_Height (FB) = Mode.V_Visible) or
          (Scaler_Available and
           Rotated_Width (FB) <= Config.Maximum_Scalable_Width (Pipe) and
           Rotated_Width (FB) <= Mode.H_Visible and
           Rotated_Height (FB) <= Mode.V_Visible)) and
         (FB.Offset /= VGA_PLANE_FRAMEBUFFER_OFFSET or Pipe = Primary) and
         (FB.Offset = VGA_PLANE_FRAMEBUFFER_OFFSET or
          (FB.BPC = 8 and Valid_Stride (FB) and
           (Config.Has_Plane_Control or
            (FB.Tiling /= Y_Tiled and FB.Rotation = No_Rotation)) and
           (FB.Tiling = Y_Tiled or not Rotation_90 (FB))));
   end Validate_Config;

end HW.GFX.GMA.Config_Helpers;
