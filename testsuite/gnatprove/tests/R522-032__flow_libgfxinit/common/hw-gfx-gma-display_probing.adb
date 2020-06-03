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

with HW.GFX.I2C;
with HW.GFX.EDID;
with HW.GFX.GMA.Config;
with HW.GFX.GMA.Config_Helpers;
with HW.GFX.GMA.I2C;
with HW.GFX.GMA.DP_Aux_Ch;
with HW.GFX.GMA.Panel;
with HW.GFX.GMA.Power_And_Clocks;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.Display_Probing
is

   function Port_Configured (Configs : Pipe_Configs; Port : Port_Type)
      return Boolean is
     (Configs (Primary).Port    = Port or
      Configs (Secondary).Port  = Port or
      Configs (Tertiary).Port   = Port);

   -- DP and HDMI share physical pins.
   function Sibling_Port (Port : Port_Type) return Port_Type is
     (case Port is
         when HDMI1 => DP1,
         when HDMI2 => DP2,
         when HDMI3 => DP3,
         when DP1 => HDMI1,
         when DP2 => HDMI2,
         when DP3 => HDMI3,
         when others => Disabled);

   function Has_Sibling_Port (Port : Port_Type) return Boolean is
     (Sibling_Port (Port) /= Disabled);

   function Is_DVI_I (Port : Active_Port_Type) return Boolean is
     (Config.Have_DVI_I and
      (Port = Analog or
      Config_Helpers.To_PCH_Port (Port) = Config.Analog_I2C_Port));

   procedure Read_EDID
     (Raw_EDID :    out EDID.Raw_EDID_Data;
      Port     : in     Active_Port_Type;
      Success  :    out Boolean)
   with
      Post => (if Success then EDID.Valid (Raw_EDID))
   is
      Raw_EDID_Length : GFX.I2C.Transfer_Length := Raw_EDID'Length;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      for I in 1 .. 2 loop
         if Config_Helpers.To_Display_Type (Port) = DP then
            -- May need power to read edid
            declare
               Temp_Configs : Pipe_Configs := Cur_Configs;
            begin
               Temp_Configs (Primary).Port := Port;
               Power_And_Clocks.Power_Up (Cur_Configs, Temp_Configs);
            end;

            declare
               DP_Port : constant GMA.DP_Port :=
                 (case Port is
                     when Internal  => DP_A,
                     when DP1       => DP_B,
                     when DP2       => DP_C,
                     when DP3       => DP_D,
                     when others    => GMA.DP_Port'First);
            begin
               DP_Aux_Ch.I2C_Read
                 (Port     => DP_Port,
                  Address  => 16#50#,
                  Length   => Raw_EDID_Length,
                  Data     => Raw_EDID,
                  Success  => Success);
            end;
         else
            I2C.I2C_Read
              (Port     => (if Port = Analog
                            then Config.Analog_I2C_Port
                            else Config_Helpers.To_PCH_Port (Port)),
               Address  => 16#50#,
               Length   => Raw_EDID_Length,
               Data     => Raw_EDID,
               Success  => Success);
         end if;
         exit when not Success;  -- don't retry if reading itself failed

         pragma Debug (Debug.Put_Buffer ("EDID", Raw_EDID, Raw_EDID_Length));
         EDID.Sanitize (Raw_EDID, Success);
         exit when Success;
      end loop;
   end Read_EDID;

   procedure Probe_Port
     (Pipe_Cfg : in out Pipe_Config;
      Port     : in     Active_Port_Type;
      Success  :    out Boolean)
   with Pre => True
   is
      Raw_EDID : EDID.Raw_EDID_Data := (others => 16#00#);
   begin
      Success := Config.Valid_Port (Port);

      if Success then
         if Port = Internal then
            Panel.Wait_On;
         end if;
         Read_EDID (Raw_EDID, Port, Success);
      end if;

      if Success and then
         ((not Is_DVI_I (Port) or EDID.Compatible_Display
            (Raw_EDID, Config_Helpers.To_Display_Type (Port))) and
          EDID.Has_Preferred_Mode (Raw_EDID))
      then
         Pipe_Cfg.Port := Port;
         Pipe_Cfg.Mode := EDID.Preferred_Mode (Raw_EDID);

         pragma Warnings (GNATprove, Off, """Raw_EDID"" is set by ""Read_Edid"" but not used after the call",
            Reason => "We just want to check if it's readable.");
         if Has_Sibling_Port (Port) then
            -- Probe sibling port too and bail out if something is detected.
            -- This is a precaution for adapters that expose the pins of a
            -- port for both HDMI/DVI and DP (like some ThinkPad docks). A
            -- user might have attached both by accident and there are ru-
            -- mors of displays that got fried by applying the wrong signal.
            declare
               Have_Sibling_EDID : Boolean;
            begin
               Read_EDID (Raw_EDID, Sibling_Port (Port), Have_Sibling_EDID);
               if Have_Sibling_EDID then
                  Pipe_Cfg.Port := Disabled;
                  Success := False;
               end if;
            end;
         end if;
         pragma Warnings (GNATprove, On, """Raw_EDID"" is set by ""Read_Edid"" but not used after the call");
      else
         Success := False;
      end if;
   end Probe_Port;

   procedure Scan_Ports
     (Configs     :    out Pipe_Configs;
      Ports       : in     Port_List := All_Ports;
      Max_Pipe    : in     Pipe_Index := Pipe_Index'Last;
      Keep_Power  : in     Boolean := False)
   is
      Probe_Internal : Boolean := False;

      Port_Idx : Port_List_Range := Port_List_Range'First;
      Success  : Boolean;
   begin
      Configs := (Pipe_Index =>
                    (Port        => Disabled,
                     Mode        => Invalid_Mode,
                     Cursor      => Default_Cursor,
                     Framebuffer => Default_FB));

      -- Turn panel on early to probe other ports during the power on delay.
      for Idx in Port_List_Range loop
         exit when Ports (Idx) = Disabled;
         if Ports (Idx) = Internal then
            Panel.On (Wait => False);
            Probe_Internal := True;
            exit;
         end if;
      end loop;

      for Pipe in Pipe_Index range
         Pipe_Index'First .. Pipe_Index'Min (Max_Pipe, Config.Max_Pipe)
      loop
         while Ports (Port_Idx) /= Disabled loop
            if not Port_Configured (Configs, Ports (Port_Idx)) and
               (not Has_Sibling_Port (Ports (Port_Idx)) or
                not Port_Configured (Configs, Sibling_Port (Ports (Port_Idx))))
            then
               Probe_Port (Configs (Pipe), Ports (Port_Idx), Success);
            else
               Success := False;
            end if;

            exit when Port_Idx = Port_List_Range'Last;
            Port_Idx := Port_List_Range'Succ (Port_Idx);

            exit when Success;
         end loop;
      end loop;

      -- Restore power settings
      if not Keep_Power then
         Power_And_Clocks.Power_Set_To (Cur_Configs);
      end if;

      -- Turn panel power off if probing failed.
      if Probe_Internal and not Port_Configured (Configs, Internal) then
         Panel.Off;
      end if;
   end Scan_Ports;

end HW.GFX.GMA.Display_Probing;
