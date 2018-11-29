--
-- Copyright (C) 2015-2018 secunet Security Networks AG
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

with HW.Config;
with HW.Time;
with HW.Port_IO;

package HW.GFX.GMA
with
   Abstract_State =>
     (State,
      Init_State,
      Config_State,
      (Device_State with External)),
   Initializes =>
     (Init_State,
      Config_State)
is

   GTT_Page_Size : constant := 4096;
   type GTT_Address_Type is mod 2 ** 39;
   subtype GTT_Range is Natural range 0 .. 16#8_0000# - 1;
   GTT_Rotation_Offset : constant GTT_Range := GTT_Range'Last / 2 + 1;

   type CPU_Type is
     (G45,
      Ironlake,
      Sandybridge,
      Ivybridge,
      Haswell,
      Broadwell,
      Broxton,
      Skylake);

   type CPU_Variant is (Normal, ULT);

   type Port_Type is
     (Disabled,
      Internal,
      DP1,
      DP2,
      DP3,
      HDMI1, -- or DVI
      HDMI2, -- or DVI
      HDMI3, -- or DVI
      Analog);

   type Cursor_Mode is (No_Cursor, ARGB_Cursor);
   type Cursor_Size is (Cursor_64x64, Cursor_128x128, Cursor_256x256);
   Cursor_Width : constant array (Cursor_Size) of Width_Type := (64, 128, 256);

   subtype Cursor_Pos is Int32 range Int32'First / 2 .. Int32'Last / 2;

   type Cursor_Type is record
      Mode        : Cursor_Mode;
      Size        : Cursor_Size;
      Center_X    : Cursor_Pos;
      Center_Y    : Cursor_Pos;
      GTT_Offset  : GTT_Range;
   end record;
   Default_Cursor : constant Cursor_Type :=
     (Mode        => No_Cursor,
      Size        => Cursor_Size'First,
      Center_X    => 0,
      Center_Y    => 0,
      GTT_Offset  => 0);

   type Pipe_Config is record
      Port        : Port_Type;
      Framebuffer : Framebuffer_Type;
      Cursor      : Cursor_Type;
      Mode        : Mode_Type;
   end record;
   type Pipe_Index is (Primary, Secondary, Tertiary);
   type Pipe_Configs is array (Pipe_Index) of Pipe_Config;

   -- Special framebuffer offset to indicate legacy VGA plane.
   -- Only valid on primary pipe.
   VGA_PLANE_FRAMEBUFFER_OFFSET : constant := 16#ffff_ffff#;

   pragma Warnings (GNATprove, Off, "unused variable ""Write_Delay""",
      Reason => "Write_Delay is used for debugging only");
   procedure Initialize
     (Write_Delay : in     Word64 := 0;
      Clean_State : in     Boolean := False;
      Success     :    out Boolean)
   with
      Global =>
        (In_Out => (Config_State, Device_State, Port_IO.State),
         Output => (State, Init_State),
         Input  => (Time.State)),
      Post => Success = Is_Initialized;
   function Is_Initialized return Boolean
   with
      Global => (Input => Init_State);
   pragma Warnings (GNATprove, On, "unused variable ""Write_Delay""");

   pragma Warnings (GNATprove, Off, "subprogram ""Power_Up_VGA"" has no effect",
                    Reason => "Effect depends on the platform compiled for");
   procedure Power_Up_VGA
   with
      Pre => Is_Initialized;

   procedure Update_Outputs (Configs : Pipe_Configs);

   procedure Update_Cursor (Pipe : Pipe_Index; Cursor : Cursor_Type);
   procedure Place_Cursor
     (Pipe : Pipe_Index;
      X : Cursor_Pos;
      Y : Cursor_Pos);
   procedure Move_Cursor
     (Pipe : Pipe_Index;
      X : Cursor_Pos;
      Y : Cursor_Pos);

   pragma Warnings (GNATprove, Off, "subprogram ""Dump_Configs"" has no effect",
                    Reason => "It's only used for debugging");
   procedure Dump_Configs (Configs : Pipe_Configs);

   procedure Write_GTT
     (GTT_Page       : GTT_Range;
      Device_Address : GTT_Address_Type;
      Valid          : Boolean);

   procedure Setup_Default_FB
     (FB       : in     Framebuffer_Type;
      Clear    : in     Boolean := True;
      Success  :    out Boolean)
   with
      Pre => Is_Initialized and HW.Config.Dynamic_MMIO;

   procedure Map_Linear_FB (Linear_FB : out Word64; FB : in Framebuffer_Type)
   with
      Pre => Is_Initialized and HW.Config.Dynamic_MMIO;

private

   -- For the default framebuffer setup (see below) with 90 degree rotations,
   -- we expect the offset which is used for the final scanout to be above
   -- `GTT_Rotation_Offset`. So we can use `Offset - GTT_Rotation_Offset` for
   -- the physical memory location and aperture mapping.
   function Phys_Offset (FB : Framebuffer_Type) return Word32 is
     (if Rotation_90 (FB)
      then FB.Offset - Word32 (GTT_Rotation_Offset) * GTT_Page_Size
      else FB.Offset);

   ----------------------------------------------------------------------------
   -- State tracking for the currently configured pipes

   Cur_Configs : Pipe_Configs with Part_Of => State;

   function Requires_Scaling (Pipe_Cfg : Pipe_Config) return Boolean is
     (Requires_Scaling (Pipe_Cfg.Framebuffer, Pipe_Cfg.Mode));

   function Scaling_Type (Pipe_Cfg : Pipe_Config) return Scaling_Aspect is
     (Scaling_Type (Pipe_Cfg.Framebuffer, Pipe_Cfg.Mode));

   ----------------------------------------------------------------------------
   -- Internal representation of a single pipe's configuration

   subtype Active_Port_Type is Port_Type
      range Port_Type'Succ (Disabled) .. Port_Type'Last;

   type GPU_Port is (DIGI_A, DIGI_B, DIGI_C, DIGI_D, DIGI_E, LVDS, VGA);

   subtype Digital_Port is GPU_Port range DIGI_A .. DIGI_E;
   subtype GMCH_DP_Port is GPU_Port range DIGI_B .. DIGI_D;
   subtype GMCH_HDMI_Port is GPU_Port range DIGI_B .. DIGI_C;

   type PCH_Port is
     (PCH_DAC, PCH_LVDS,
      PCH_HDMI_B, PCH_HDMI_C, PCH_HDMI_D,
      PCH_DP_B, PCH_DP_C, PCH_DP_D);

   subtype PCH_HDMI_Port is PCH_Port range PCH_HDMI_B .. PCH_HDMI_D;
   subtype PCH_DP_Port is PCH_Port range PCH_DP_B .. PCH_DP_D;

   type Port_Config is
      record
         Port     : GPU_Port;
         PCH_Port : GMA.PCH_Port;
         Display  : Display_Type;
         Mode     : Mode_Type;
         Is_FDI   : Boolean;
         FDI      : DP_Link;
         DP       : DP_Link;
      end record;

   type FDI_Training_Type is (Simple_Training, Full_Training, Auto_Training);

   ----------------------------------------------------------------------------

   type DP_Port is (DP_A, DP_B, DP_C, DP_D);

   ----------------------------------------------------------------------------

   subtype DDI_HDMI_Buf_Trans_Range is Integer range 0 .. 11;

   ----------------------------------------------------------------------------

   Tile_Width : constant array (Tiling_Type) of Width_Type :=
     (Linear => 16, X_Tiled => 128, Y_Tiled => 32);
   Tile_Rows : constant array (Tiling_Type) of Height_Type :=
     (Linear => 1, X_Tiled => 8, Y_Tiled => 32);

   function FB_Pitch (Px : Pos_Pixel_Type; FB : Framebuffer_Type) return Natural
      is (Natural (Div_Round_Up
           (Pixel_To_Bytes (Px, FB), Tile_Width (FB.Tiling) * 4)));

   function Valid_Stride (FB : Framebuffer_Type) return Boolean is
     (FB.Width + FB.Start_X <= FB.Stride and
      Pixel_To_Bytes (FB.Stride, FB) mod (Tile_Width (FB.Tiling) * 4) = 0 and
      FB.Height + FB.Start_Y <= FB.V_Stride and
      FB.V_Stride mod Tile_Rows (FB.Tiling) = 0);

end HW.GFX.GMA;
