--
-- Copyright (C) 2014-2018 secunet Security Networks AG
-- Copyright (C) 2017 Nico Huber <nico.h@gmx.de>
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

with HW.MMIO_Range;
pragma Elaborate_All (HW.MMIO_Range);
with HW.PCI.Dev;
pragma Elaborate_All (HW.PCI.Dev);

with HW.GFX.Framebuffer_Filler;

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Config_Helpers;
with HW.GFX.GMA.Registers;
with HW.GFX.GMA.Power_And_Clocks;
with HW.GFX.GMA.Panel;
with HW.GFX.GMA.PLLs;
with HW.GFX.GMA.Port_Detect;
with HW.GFX.GMA.Connectors;
with HW.GFX.GMA.Connector_Info;
with HW.GFX.GMA.Pipe_Setup;

with HW.Debug;
with GNAT.Source_Info;

use type HW.Int32;

package body HW.GFX.GMA
   with Refined_State =>
     (State =>
        (Dev.Address_State,
         Registers.Address_State,
         PLLs.State, Panel.Panel_State,
         Cur_Configs, Allocated_PLLs,
         HPD_Delay, Wait_For_HPD,
         Linear_FB_Base),
      Init_State => Initialized,
      Config_State => (Config.Valid_Port_GPU, Config.Raw_Clock),
      Device_State =>
        (Dev.PCI_State, Registers.Register_State, Registers.GTT_State))
is
   pragma Disable_Atomic_Synchronization;

   subtype Port_Name is String (1 .. 8);
   type Port_Name_Array is array (Port_Type) of Port_Name;
   Port_Names : constant Port_Name_Array :=
     (Disabled => "Disabled",
      Internal => "Internal",
      DP1      => "DP1     ",
      DP2      => "DP2     ",
      DP3      => "DP3     ",
      HDMI1    => "HDMI1   ",
      HDMI2    => "HDMI2   ",
      HDMI3    => "HDMI3   ",
      Analog   => "Analog  ");

   package Dev is new HW.PCI.Dev (PCI.Address'(0, 2, 0));

   package Display_Controller renames Pipe_Setup;

   type PLLs_Type is array (Pipe_Index) of PLLs.T;

   type HPD_Type is array (Port_Type) of Boolean;
   type HPD_Delay_Type is array (Active_Port_Type) of Time.T;

   Allocated_PLLs : PLLs_Type;
   HPD_Delay : HPD_Delay_Type;
   Wait_For_HPD : HPD_Type;
   Initialized : Boolean := False;

   Linear_FB_Base : Word64;

   ----------------------------------------------------------------------------

   PCH_RAWCLK_FREQ_MASK                : constant := 16#3ff# * 2 ** 0;

   function PCH_RAWCLK_FREQ (Freq : Frequency_Type) return Word32
   is
   begin
      return Word32 (Freq / 1_000_000);
   end PCH_RAWCLK_FREQ;

   ----------------------------------------------------------------------------

   procedure Enable_Output
     (Pipe     : in     Pipe_Index;
      Pipe_Cfg : in     Pipe_Config;
      Success  :    out Boolean)
   with
      Pre => Pipe_Cfg.Port in Active_Port_Type
   is
      Port_Cfg : Port_Config;
      Scaler_Available : Boolean;
   begin
      pragma Debug (Debug.New_Line);
      pragma Debug (Debug.Put_Line
        ("Trying to enable port " & Port_Names (Pipe_Cfg.Port)));

      Config_Helpers.Fill_Port_Config
        (Port_Cfg, Pipe, Pipe_Cfg.Port, Pipe_Cfg.Mode, Success);

      if Success then
         Display_Controller.Scaler_Available (Scaler_Available, Pipe);
         Success := Config_Helpers.Validate_Config
           (Pipe_Cfg.Framebuffer, Port_Cfg.Mode, Pipe, Scaler_Available);
      end if;

      if Success then
         Connector_Info.Preferred_Link_Setting (Port_Cfg, Success);
      end if;

      -- loop over all possible DP-lane configurations
      -- (non-DP ports use a single fake configuration)
      while Success loop
         pragma Loop_Invariant
           (Pipe_Cfg.Port in Active_Port_Type and
            Port_Cfg.Mode = Port_Cfg.Mode'Loop_Entry);

         PLLs.Alloc
           (Port_Cfg => Port_Cfg,
            PLL      => Allocated_PLLs (Pipe),
            Success  => Success);

         if Success then
            -- try each DP-lane configuration twice
            for Try in 1 .. 2 loop
               pragma Loop_Invariant
                 (Pipe_Cfg.Port in Active_Port_Type);

               -- Clear pending hot-plug events before every try
               Port_Detect.Clear_Hotplug_Detect (Pipe_Cfg.Port);

               Connectors.Pre_On
                 (Pipe        => Pipe,
                  Port_Cfg    => Port_Cfg,
                  PLL_Hint    => PLLs.Register_Value (Allocated_PLLs (Pipe)),
                  Success     => Success);

               if Success then
                  Display_Controller.On
                    (Pipe        => Pipe,
                     Port_Cfg    => Port_Cfg,
                     Framebuffer => Pipe_Cfg.Framebuffer,
                     Cursor      => Pipe_Cfg.Cursor);

                  Connectors.Post_On
                    (Pipe     => Pipe,
                     Port_Cfg => Port_Cfg,
                     PLL_Hint => PLLs.Register_Value (Allocated_PLLs (Pipe)),
                     Success  => Success);

                  if not Success then
                     Display_Controller.Off (Pipe);
                     Connectors.Post_Off (Port_Cfg);
                  end if;
               end if;

               exit when Success;
            end loop;
            exit when Success;   -- connection established => stop loop

            -- connection failed
            PLLs.Free (Allocated_PLLs (Pipe));
         end if;

         Connector_Info.Next_Link_Setting (Port_Cfg, Success);
      end loop;

      if Success then
         pragma Debug (Debug.Put_Line
           ("Enabled port " & Port_Names (Pipe_Cfg.Port)));
      else
         Wait_For_HPD (Pipe_Cfg.Port) := True;
         if Pipe_Cfg.Port = Internal then
            Panel.Off;
         end if;
      end if;
   end Enable_Output;

   procedure Disable_Output (Pipe : Pipe_Index; Pipe_Cfg : Pipe_Config)
   is
      Port_Cfg : Port_Config;
      Success  : Boolean;
   begin
      Config_Helpers.Fill_Port_Config
        (Port_Cfg, Pipe, Pipe_Cfg.Port, Pipe_Cfg.Mode, Success);
      if Success then
         pragma Debug (Debug.New_Line);
         pragma Debug (Debug.Put_Line
           ("Disabling port " & Port_Names (Pipe_Cfg.Port)));
         pragma Debug (Debug.New_Line);

         Connectors.Pre_Off (Port_Cfg);
         Display_Controller.Off (Pipe);
         Connectors.Post_Off (Port_Cfg);

         PLLs.Free (Allocated_PLLs (Pipe));
      end if;
   end Disable_Output;

   procedure Update_Outputs (Configs : Pipe_Configs)
   is
      procedure Check_HPD (Port : in Active_Port_Type; Detected : out Boolean)
      is
         HPD_Delay_Over : constant Boolean := Time.Timed_Out (HPD_Delay (Port));
      begin
         if HPD_Delay_Over then
            Port_Detect.Hotplug_Detect (Port, Detected);
            HPD_Delay (Port) := Time.MS_From_Now (333);
         else
            Detected := False;
         end if;
      end Check_HPD;

      Power_Changed  : Boolean := False;
      Old_Configs    : Pipe_Configs;

      -- Only called when we actually tried to change something
      -- so we don't congest the log with unnecessary messages.
      procedure Update_Power
      is
      begin
         if not Power_Changed then
            Power_And_Clocks.Power_Up (Old_Configs, Configs);
            Power_Changed := True;
         end if;
      end Update_Power;

      function Full_Update (Cur_Config, New_Config : Pipe_Config) return Boolean
      is
      begin
         return
            Cur_Config.Port /= New_Config.Port
            or else
            Cur_Config.Mode /= New_Config.Mode
            or else
            (Config.Use_PDW_For_EDP_Scaling and then
             (Cur_Config.Port = Internal and
              Requires_Scaling (Cur_Config) /= Requires_Scaling (New_Config)))
            or else
            (Config.Has_GMCH_PFIT_CONTROL and then
             (Requires_Scaling (Cur_Config) /= Requires_Scaling (New_Config) or
              Scaling_Type (Cur_Config) /= Scaling_Type (New_Config)));
      end Full_Update;
   begin
      Old_Configs := Cur_Configs;

      -- disable all pipes that changed or had a hot-plug event
      for Pipe in Pipe_Index loop
         declare
            Unplug_Detected : Boolean;
            Cur_Config : Pipe_Config renames Cur_Configs (Pipe);
            New_Config : Pipe_Config renames Configs (Pipe);
         begin
            if Cur_Config.Port /= Disabled then
               Check_HPD (Cur_Config.Port, Unplug_Detected);

               if Full_Update (Cur_Config, New_Config) or Unplug_Detected then
                  Disable_Output (Pipe, Cur_Config);
                  Cur_Config.Port := Disabled;
                  Update_Power;
               end if;
            end if;
         end;
      end loop;

      -- enable all pipes that changed and should be active
      for Pipe in Pipe_Index loop
         declare
            Success : Boolean;
            Scaler_Available : Boolean;
            Cur_Config : Pipe_Config renames Cur_Configs (Pipe);
            New_Config : Pipe_Config renames Configs (Pipe);
         begin
            if New_Config.Port /= Disabled and
               Full_Update (Cur_Config, New_Config)
            then
               if Wait_For_HPD (New_Config.Port) then
                  Check_HPD (New_Config.Port, Success);
                  Wait_For_HPD (New_Config.Port) := not Success;
               else
                  Success := True;
               end if;

               if Success then
                  Update_Power;
                  Enable_Output (Pipe, New_Config, Success);
               end if;

               if Success then
                  Cur_Config := New_Config;
               end if;

            -- update framebuffer offset only
            elsif New_Config.Port /= Disabled and
                  Cur_Config.Framebuffer /= New_Config.Framebuffer
            then
               Display_Controller.Scaler_Available (Scaler_Available, Pipe);
               if Config_Helpers.Validate_Config
                    (New_Config.Framebuffer, New_Config.Mode,
                     Pipe, Scaler_Available)
               then
                  Display_Controller.Setup_FB
                    (Pipe, New_Config.Mode, New_Config.Framebuffer);
                  Display_Controller.Update_Cursor
                    (Pipe, New_Config.Framebuffer, New_Config.Cursor);
                  Cur_Config := New_Config;
               end if;
            end if;
         end;
      end loop;

      if Power_Changed then
         Power_And_Clocks.Power_Down (Old_Configs, Configs, Cur_Configs);
      end if;
   end Update_Outputs;

   ----------------------------------------------------------------------------

   procedure Update_Cursor (Pipe : Pipe_Index; Cursor : Cursor_Type)
   is
   begin
      Cur_Configs (Pipe).Cursor := Cursor;
      Display_Controller.Update_Cursor
        (Pipe, Cur_Configs (Pipe).Framebuffer, Cur_Configs (Pipe).Cursor);
   end Update_Cursor;

   procedure Place_Cursor
     (Pipe  : Pipe_Index;
      X     : Cursor_Pos;
      Y     : Cursor_Pos)
   is
   begin
      Cur_Configs (Pipe).Cursor.Center_X := X;
      Cur_Configs (Pipe).Cursor.Center_Y := Y;
      Display_Controller.Place_Cursor
        (Pipe, Cur_Configs (Pipe).Framebuffer, Cur_Configs (Pipe).Cursor);
   end Place_Cursor;

   procedure Move_Cursor
     (Pipe  : Pipe_Index;
      X     : Cursor_Pos;
      Y     : Cursor_Pos)
   is
      function Cap_Add (A, B : Cursor_Pos) return Cursor_Pos is
        (if A + B < 0
         then Int32'Max (Cursor_Pos'First, A + B)
         else Int32'Min (Cursor_Pos'Last, A + B));
   begin
      Place_Cursor
        (Pipe  => Pipe,
         X     => Cap_Add (Cur_Configs (Pipe).Cursor.Center_X, X),
         Y     => Cap_Add (Cur_Configs (Pipe).Cursor.Center_Y, Y));
   end Move_Cursor;

   ----------------------------------------------------------------------------

   procedure Initialize
     (Write_Delay : in     Word64 := 0;
      Clean_State : in     Boolean := False;
      Success     :    out Boolean)
   with
      Refined_Global =>
        (In_Out =>
           (Config.Valid_Port_GPU, Dev.PCI_State,
            Registers.Register_State, Port_IO.State,
            Config.Raw_Clock),
         Input =>
           (Time.State),
         Output =>
           (Dev.Address_State,
            Registers.Address_State,
            PLLs.State, Panel.Panel_State,
            Cur_Configs, Allocated_PLLs,
            HPD_Delay, Wait_For_HPD,
            Linear_FB_Base, Initialized))
   is
      use type HW.Word64;

      PCI_MMIO_Base, PCI_GTT_Base : Word64;

      Now : constant Time.T := Time.Now;

      procedure Check_Platform (Success : out Boolean)
      is
         Audio_VID_DID : Word32;
      begin
         case Config.CPU is
            when G45 =>
               Registers.Read (Registers.G4X_AUD_VID_DID, Audio_VID_DID);
            when Haswell .. Skylake =>
               Registers.Read (Registers.AUD_VID_DID, Audio_VID_DID);
            when Ironlake .. Ivybridge =>
               Registers.Read (Registers.PCH_AUD_VID_DID, Audio_VID_DID);
         end case;
         Success :=
           (case Config.CPU is
               when Broxton      => Audio_VID_DID = 16#8086_280a#,
               when Skylake      => Audio_VID_DID = 16#8086_2809#,
               when Broadwell    => Audio_VID_DID = 16#8086_2808#,
               when Haswell      => Audio_VID_DID = 16#8086_2807#,
               when Ivybridge |
                    Sandybridge  => Audio_VID_DID = 16#8086_2806# or
                                    Audio_VID_DID = 16#8086_2805#,
               when Ironlake     => Audio_VID_DID = 16#0000_0000#,
               when G45          => Audio_VID_DID = 16#8086_2801# or
                                    Audio_VID_DID = 16#8086_2802# or
                                    Audio_VID_DID = 16#8086_2803#);
      end Check_Platform;

      procedure Check_Platform_PCI (Success : out Boolean)
      is
         use type HW.Word16;
         Vendor, Device : Word16;
      begin
         Dev.Read16 (Vendor, PCI.Vendor_Id);
         Dev.Read16 (Device, PCI.Device_Id);

         Success := Vendor = 16#8086# and Config.Compatible_GPU (Device);
      end Check_Platform_PCI;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      pragma Debug (Debug.Set_Register_Write_Delay (Write_Delay));

      Linear_FB_Base := 0;
      Wait_For_HPD := HPD_Type'(others => False);
      HPD_Delay := HPD_Delay_Type'(others => Now);
      Allocated_PLLs := (others => PLLs.Invalid);
      Cur_Configs := Pipe_Configs'
        (others => Pipe_Config'
           (Port        => Disabled,
            Framebuffer => HW.GFX.Default_FB,
            Cursor      => Default_Cursor,
            Mode        => HW.GFX.Invalid_Mode));
      PLLs.Initialize;

      Dev.Initialize (Success);

      if Success then
         Dev.Map (PCI_MMIO_Base, PCI.Res0, Length => Config.GTT_Offset);
         Dev.Map (PCI_GTT_Base, PCI.Res0, Offset => Config.GTT_Offset);
         if PCI_MMIO_Base /= 0 and PCI_GTT_Base /= 0 then
            Registers.Set_Register_Base (PCI_MMIO_Base, PCI_GTT_Base);
         else
            pragma Debug (Debug.Put_Line
              ("ERROR: Couldn't map resoure0."));
            Registers.Set_Register_Base (Config.Default_MMIO_Base);
            Success := Config.Default_MMIO_Base_Set;
         end if;

         if Success then
            Check_Platform_PCI (Success);
         end if;
      else
         pragma Debug (Debug.Put_Line
           ("WARNING: Couldn't initialize PCI dev."));
         Registers.Set_Register_Base (Config.Default_MMIO_Base);
         Success := Config.Default_MMIO_Base_Set;

         if Success then
            Check_Platform (Success);
         end if;
      end if;

      if not Success then
         pragma Debug (Debug.Put_Line ("ERROR: Incompatible CPU or PCH."));

         Panel.Static_Init;   -- for flow analysis

         Initialized := False;
         return;
      end if;

      Panel.Setup_PP_Sequencer;
      Port_Detect.Initialize;
      Connectors.Initialize;

      if Clean_State then
         Power_And_Clocks.Pre_All_Off;
         Connectors.Pre_All_Off;
         Display_Controller.All_Off;
         Connectors.Post_All_Off;
         PLLs.All_Off;
         Power_And_Clocks.Post_All_Off;
         Registers.Clear_Fences;
      else
         -- According to PRMs, VGA plane is the only thing
         -- that's enabled by default after reset...
         Display_Controller.Legacy_VGA_Off;
         -- ... along with some DDI port bits since Skylake.
         Connectors.Post_Reset_Off;
      end if;

      -------------------- Now restart from a clean state ---------------------
      Power_And_Clocks.Initialize;

      if Config.Has_PCH then
         Registers.Unset_And_Set_Mask
           (Register    => Registers.PCH_RAWCLK_FREQ,
            Mask_Unset  => PCH_RAWCLK_FREQ_MASK,
            Mask_Set    => PCH_RAWCLK_FREQ (Config.Default_RawClk_Freq));
      end if;

      Initialized := True;

   end Initialize;

   function Is_Initialized return Boolean
   with
      Refined_Post => Is_Initialized'Result = Initialized
   is
   begin
      return Initialized;
   end Is_Initialized;

   ----------------------------------------------------------------------------

   procedure Power_Up_VGA
   is
      Fake_Config : constant Pipe_Configs :=
        (Primary =>
           (Port        => Analog,
            Framebuffer => HW.GFX.Default_FB,
            Cursor      => Default_Cursor,
            Mode        => HW.GFX.Invalid_Mode),
         others =>
           (Port        => Disabled,
            Framebuffer => HW.GFX.Default_FB,
            Cursor      => Default_Cursor,
            Mode        => HW.GFX.Invalid_Mode));
   begin
      Power_And_Clocks.Power_Up (Cur_Configs, Fake_Config);
   end Power_Up_VGA;

   ----------------------------------------------------------------------------

   function FB_First_Page (FB : Framebuffer_Type) return Natural is
     (Natural (Phys_Offset (FB) / GTT_Page_Size));
   function FB_Pages (FB : Framebuffer_Type) return Natural is
     (Natural (Div_Round_Up (FB_Size (FB), GTT_Page_Size)));
   function FB_Last_Page (FB : Framebuffer_Type) return Natural is
     (FB_First_Page (FB) + FB_Pages (FB) - 1);

   -- Check basics and that it fits in GTT. For 90 degree rotations,
   -- the Offset should be above GTT_Rotation_Offset. The latter will
   -- be subtracted for the aperture mapping.
   function Valid_FB (FB : Framebuffer_Type) return Boolean is
     (Valid_Stride (FB) and
      FB_First_Page (FB) in GTT_Range and
      FB_Last_Page (FB) in GTT_Range and
      (not Rotation_90 (FB) or
       (FB_Last_Page (FB) + GTT_Rotation_Offset in GTT_Range and
        FB.Offset >= Word32 (GTT_Rotation_Offset) * GTT_Page_Size)));

   -- Also check that we don't overflow the GTT's 39-bit space
   -- (always true with a 32-bit base)
   function Valid_Phys_FB (FB : Framebuffer_Type; Phys_Base : Word32)
      return Boolean is
     (Valid_FB (FB) and
      Int64 (Phys_Base) + Int64 (Phys_Offset (FB)) + Int64 (FB_Size (FB)) <=
         Int64 (GTT_Address_Type'Last))
   with
      Ghost;

   procedure Write_GTT
     (GTT_Page       : GTT_Range;
      Device_Address : GTT_Address_Type;
      Valid          : Boolean)
   is
   begin
      Registers.Write_GTT (GTT_Page, Device_Address, Valid);
   end Write_GTT;

   procedure Setup_Default_GTT (FB : Framebuffer_Type; Phys_Base : Word32)
   with
      Pre => Is_Initialized and Valid_Phys_FB (FB, Phys_Base)
   is
      Phys_Addr : GTT_Address_Type :=
         GTT_Address_Type (Phys_Base) + GTT_Address_Type (Phys_Offset (FB));
   begin
      for Idx in FB_First_Page (FB) .. FB_Last_Page (FB) loop
         Registers.Write_GTT
           (GTT_Page       => Idx,
            Device_Address => Phys_Addr,
            Valid          => True);
         Phys_Addr := Phys_Addr + GTT_Page_Size;
      end loop;

      if Rotation_90 (FB) and FB.Tiling = Y_Tiled and FB.V_Stride >= 32 then
         declare
            V_Pages : constant Natural := Natural (FB.V_Stride) / 32;
            Bytes_Per_Row : constant GTT_Address_Type :=
               GTT_Address_Type (Pixel_To_Bytes (32 * FB.Stride, FB));
         begin
            Phys_Addr := GTT_Address_Type (Phys_Base) +
                           GTT_Address_Type (Phys_Offset (FB)) +
                           GTT_Address_Type (FB_Size (FB));
            for Page in FB_First_Page (FB) .. FB_Last_Page (FB) loop
               Phys_Addr := Phys_Addr - Bytes_Per_Row;
               Registers.Write_GTT
                 (GTT_Page       => GTT_Rotation_Offset + Page,
                  Device_Address => Phys_Addr,
                  Valid          => True);

               if (Page - FB_First_Page (FB) + 1) mod V_Pages = 0 then
                  Phys_Addr := Phys_Addr + GTT_Page_Size +
                                 GTT_Address_Type (V_Pages) * Bytes_Per_Row;
               end if;
            end loop;
         end;
      end if;
   end Setup_Default_GTT;

   ----------------------------------------------------------------------------

   use type HW.Word16;
   subtype Stolen_Size_Range is Int64 range 0 .. 2 ** 33;

   function GGMS_Gen4 (GGC : Word16) return Natural is
     (Natural (Shift_Right (GGC, 8) and 16#07#));
   function GTT_Size_Gen4 (GGC : Word16) return Natural is
     (if GGMS_Gen4 (GGC) in 1 .. 3 then
         (GGMS_Gen4 (GGC) + 1) * 2 ** 19 else 0);

   function GMS_Gen4 (GGC : Word16) return Natural is
     (Natural (Shift_Right (GGC, 4) and 16#0f#));
   Valid_Stolen_Size_Gen4 : constant
      array (Natural range 1 .. 13) of Stolen_Size_Range :=
     (1, 4, 8, 16, 32, 48, 64, 128, 256, 96, 160, 224, 352);
   function Stolen_Size_Gen4 (GGC : Word16) return Stolen_Size_Range is
     (if GMS_Gen4 (GGC) in Valid_Stolen_Size_Gen4'Range then
         Valid_Stolen_Size_Gen4 (GMS_Gen4 (GGC)) * 2 ** 20 else 0);

   function GTT_Size_Gen6 (GGC : Word16) return Natural is
     (Natural (Shift_Right (GGC, 8) and 16#03#) * 2 ** 20);

   function Stolen_Size_Gen6 (GGC : Word16) return Stolen_Size_Range is
     (Stolen_Size_Range (Shift_Right (GGC, 3) and 16#1f#) * 32 * 2 ** 20);

   function GTT_Size_Gen8 (GGC : Word16) return Natural is
     (Natural (Shift_Right (GGC, 6) and 16#03#) * 2 ** 20);

   function GMS_Gen8 (GGC : Word16) return Stolen_Size_Range is
     (Stolen_Size_Range (Shift_Right (GGC, 8) and 16#ff#));
   function Stolen_Size_Gen8 (GGC : Word16) return Stolen_Size_Range is
     (GMS_Gen8 (GGC) * 32 * 2 ** 20);

   function Stolen_Size_Gen9 (GGC : Word16) return Stolen_Size_Range is
     (if GMS_Gen8 (GGC) < 16#f0# then
         Stolen_Size_Gen8 (GGC)
      else
         (GMS_Gen8 (GGC) - 16#f0# + 1) * 4 * 2 ** 20);

   procedure Decode_Stolen
     (GTT_Size    : out Natural;
      Stolen_Size : out Stolen_Size_Range)
   with
      Pre => Is_Initialized
   is
      GGC_Reg : constant :=
        (case Config.CPU is
            when G45 | Ironlake           => 16#52#,
            when Sandybridge .. Skylake   => 16#50#);
      GGC : Word16;
   begin
      Dev.Read16 (GGC, GGC_Reg);
      case Config.CPU is
         when G45 | Ironlake =>
            GTT_Size    := GTT_Size_Gen4 (GGC);
            Stolen_Size := Stolen_Size_Gen4 (GGC);
         when Sandybridge .. Haswell =>
            GTT_Size    := GTT_Size_Gen6 (GGC);
            Stolen_Size := Stolen_Size_Gen6 (GGC);
         when Broadwell =>
            GTT_Size    := GTT_Size_Gen8 (GGC);
            Stolen_Size := Stolen_Size_Gen8 (GGC);
         when Broxton .. Skylake =>
            GTT_Size    := GTT_Size_Gen8 (GGC);
            Stolen_Size := Stolen_Size_Gen9 (GGC);
      end case;
   end Decode_Stolen;

   -- Additional runtime validation that FB fits stolen memory and aperture.
   procedure Validate_FB (FB : Framebuffer_Type; Valid : out Boolean)
   with
      Pre => Is_Initialized,
      Post => (if Valid then Valid_FB (FB))
   is
      GTT_Size, Aperture_Size : Natural;
      Stolen_Size : Stolen_Size_Range;
   begin
      Valid := Valid_FB (FB);

      if Valid then
         Decode_Stolen (GTT_Size, Stolen_Size);
         Dev.Resource_Size (Aperture_Size, PCI.Res2);
         Valid :=
            FB_Last_Page (FB) < GTT_Size / Config.GTT_PTE_Size and
            FB_Last_Page (FB) < Natural (Stolen_Size / GTT_Page_Size) and
            FB_Last_Page (FB) < Aperture_Size / GTT_Page_Size;
         pragma Debug (not Valid, Debug.Put_Line
           ("Stolen memory too small to hold framebuffer."));
      end if;
   end Validate_FB;

   procedure Setup_Default_FB
     (FB       : in     Framebuffer_Type;
      Clear    : in     Boolean := True;
      Success  :    out Boolean)
   is
      GMA_Phys_Base      : constant PCI.Index := 16#5c#;
      GMA_Phys_Base_Mask : constant := 16#fff0_0000#;

      Phys_Base : Word32;
   begin
      Validate_FB (FB, Success);

      if Success then
         Dev.Read32 (Phys_Base, GMA_Phys_Base);
         Phys_Base := Phys_Base and GMA_Phys_Base_Mask;
         Success := Phys_Base /= GMA_Phys_Base_Mask and Phys_Base /= 0;
         pragma Debug (not Success, Debug.Put_Line
           ("Failed to read stolen memory base."));

         if Success then
            if FB.Tiling in XY_Tiling then
               Registers.Add_Fence
                 (First_Page  => FB_First_Page (FB),
                  Last_Page   => FB_Last_Page (FB),
                  Tiling      => FB.Tiling,
                  Pitch       => FB_Pitch (FB.Stride, FB),
                  Success     => Success);
            end if;
            pragma Debug (not Success, Debug.Put_Line
              ("Tiled framebuffer but no fence regs available."));
         end if;

         if Success then
            Setup_Default_GTT (FB, Phys_Base);
         end if;
      end if;

      if Success and then Clear then
         declare
            use type HW.Word64;
            Linear_FB : Word64;
         begin
            Map_Linear_FB (Linear_FB, FB);
            if Linear_FB /= 0 then
               Framebuffer_Filler.Fill (Linear_FB, FB);
            end if;
         end;
      end if;
   end Setup_Default_FB;

   procedure Map_Linear_FB (Linear_FB : out Word64; FB : in Framebuffer_Type)
   is
      use type HW.Word64;

      Valid : Boolean;
   begin
      Linear_FB := 0;

      if Linear_FB_Base = 0 then
         Dev.Map (Linear_FB_Base, PCI.Res2);
         pragma Debug
           (Linear_FB_Base = 0, Debug.Put_Line ("Failed to map resource2."));
      end if;

      if Linear_FB_Base /= 0 then
         Validate_FB (FB, Valid);
         if Valid then
            Linear_FB := Linear_FB_Base + Word64 (Phys_Offset (FB));
         end if;
      end if;
   end Map_Linear_FB;

   ----------------------------------------------------------------------------

   procedure Dump_Configs (Configs : Pipe_Configs)
   is
      subtype Pipe_Name is String (1 .. 9);
      type Pipe_Name_Array is array (Pipe_Index) of Pipe_Name;
      Pipe_Names : constant Pipe_Name_Array :=
        (Primary     => "Primary  ",
         Secondary   => "Secondary",
         Tertiary    => "Tertiary ");

      subtype Tiling_Name is String (1 .. 7);
      type Tiling_Name_Array is array (Tiling_Type) of Tiling_Name;
      Tilings : constant Tiling_Name_Array :=
        (Linear   => "Linear ",
         X_Tiled  => "X_Tiled",
         Y_Tiled  => "Y_Tiled");

      subtype Rotation_Name is String (1 .. 11);
      type Rotation_Name_Array is array (Rotation_Type) of Rotation_Name;
      Rotations : constant Rotation_Name_Array :=
        (No_Rotation => "No_Rotation",
         Rotated_90  => "Rotated_90 ",
         Rotated_180 => "Rotated_180",
         Rotated_270 => "Rotated_270");
   begin
      Debug.New_Line;
      Debug.Put_Line ("CONFIG =>");
      for Pipe in Pipe_Index loop
         if Pipe = Pipe_Index'First then
            Debug.Put ("  (");
         else
            Debug.Put ("   ");
         end if;
         Debug.Put_Line (Pipe_Names (Pipe) & " =>");
         Debug.Put_Line
           ("     (Port => " & Port_Names (Configs (Pipe).Port) & ",");
         Debug.Put_Line ("      Framebuffer =>");
         Debug.Put ("        (Width     => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.Width);
         Debug.Put_Line (",");
         Debug.Put ("         Height    => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.Height);
         Debug.Put_Line (",");
         Debug.Put ("         Start_X   => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.Start_X);
         Debug.Put_Line (",");
         Debug.Put ("         Start_Y   => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.Start_Y);
         Debug.Put_Line (",");
         Debug.Put ("         Stride    => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.Stride);
         Debug.Put_Line (",");
         Debug.Put ("         V_Stride  => ");
         Debug.Put_Int32 (Configs (Pipe).Framebuffer.V_Stride);
         Debug.Put_Line (",");
         Debug.Put ("         Tiling    => ");
         Debug.Put_Line (Tilings (Configs (Pipe).Framebuffer.Tiling) & ",");
         Debug.Put ("         Rotation  => ");
         Debug.Put_Line (Rotations (Configs (Pipe).Framebuffer.Rotation) & ",");
         Debug.Put ("         Offset => ");
         Debug.Put_Word32 (Configs (Pipe).Framebuffer.Offset);
         Debug.Put_Line (",");
         Debug.Put ("         BPC    => ");
         Debug.Put_Int64 (Configs (Pipe).Framebuffer.BPC);
         Debug.Put_Line ("),");
         Debug.Put_Line ("      Mode =>");
         Debug.Put ("        (Dotclock           => ");
         Debug.Put_Int64 (Configs (Pipe).Mode.Dotclock);
         Debug.Put_Line (",");
         Debug.Put ("         H_Visible          => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.H_Visible);
         Debug.Put_Line (",");
         Debug.Put ("         H_Sync_Begin       => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.H_Sync_Begin);
         Debug.Put_Line (",");
         Debug.Put ("         H_Sync_End         => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.H_Sync_End);
         Debug.Put_Line (",");
         Debug.Put ("         H_Total            => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.H_Total);
         Debug.Put_Line (",");
         Debug.Put ("         V_Visible          => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.V_Visible);
         Debug.Put_Line (",");
         Debug.Put ("         V_Sync_Begin       => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.V_Sync_Begin);
         Debug.Put_Line (",");
         Debug.Put ("         V_Sync_End         => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.V_Sync_End);
         Debug.Put_Line (",");
         Debug.Put ("         V_Total            => ");
         Debug.Put_Int32 (Configs (Pipe).Mode.V_Total);
         Debug.Put_Line (",");
         Debug.Put_Line ("         H_Sync_Active_High => " &
           (if Configs (Pipe).Mode.H_Sync_Active_High
            then "True,"
            else "False,"));
         Debug.Put_Line ("         V_Sync_Active_High => " &
           (if Configs (Pipe).Mode.V_Sync_Active_High
            then "True,"
            else "False,"));
         Debug.Put ("         BPC                => ");
         Debug.Put_Int64 (Configs (Pipe).Mode.BPC);
         if Pipe /= Pipe_Index'Last then
            Debug.Put_Line (")),");
         else
            Debug.Put_Line (")));");
         end if;
      end loop;
   end Dump_Configs;

end HW.GFX.GMA;
