--
-- Copyright (C) 2015-2018 secunet Security Networks AG
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

with HW.Debug;
with GNAT.Source_Info;

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Transcoder;

package body HW.GFX.GMA.Pipe_Setup is

   ILK_DISPLAY_CHICKEN1_VGA_MASK       : constant := 7 * 2 ** 29;
   ILK_DISPLAY_CHICKEN1_VGA_ENABLE     : constant := 5 * 2 ** 29;
   ILK_DISPLAY_CHICKEN2_VGA_MASK       : constant := 1 * 2 ** 25;
   ILK_DISPLAY_CHICKEN2_VGA_ENABLE     : constant := 0 * 2 ** 25;

   DSPCNTR_ENABLE                      : constant :=  1 * 2 ** 31;
   DSPCNTR_GAMMA_CORRECTION            : constant :=  1 * 2 ** 30;
   DSPCNTR_FORMAT_MASK                 : constant := 15 * 2 ** 26;
   DSPCNTR_DISABLE_TRICKLE_FEED        : constant :=  1 * 2 ** 14;
   DSPCNTR_TILED_SURFACE_LINEAR        : constant :=  0 * 2 ** 10;
   DSPCNTR_TILED_SURFACE_X_TILED       : constant :=  1 * 2 ** 10;

   DSPCNTR_TILED_SURFACE : constant array (Tiling_Type) of Word32 :=
     (Linear   => DSPCNTR_TILED_SURFACE_LINEAR,
      X_Tiled  => DSPCNTR_TILED_SURFACE_X_TILED,
      Y_Tiled  => 0); -- unsupported

   DSPCNTR_MASK : constant Word32 :=
      DSPCNTR_ENABLE or
      DSPCNTR_GAMMA_CORRECTION or
      DSPCNTR_FORMAT_MASK or
      DSPCNTR_DISABLE_TRICKLE_FEED or
      DSPCNTR_TILED_SURFACE_X_TILED;

   PLANE_CTL_PLANE_ENABLE              : constant := 1 * 2 ** 31;
   PLANE_CTL_SRC_PIX_FMT_RGB_32B_8888  : constant := 4 * 2 ** 24;
   PLANE_CTL_PLANE_GAMMA_DISABLE       : constant := 1 * 2 ** 13;
   PLANE_CTL_TILED_SURFACE_MASK        : constant := 7 * 2 ** 10;
   PLANE_CTL_TILED_SURFACE_LINEAR      : constant := 0 * 2 ** 10;
   PLANE_CTL_TILED_SURFACE_X_TILED     : constant := 1 * 2 ** 10;
   PLANE_CTL_TILED_SURFACE_Y_TILED     : constant := 4 * 2 ** 10;
   PLANE_CTL_TILED_SURFACE_YF_TILED    : constant := 5 * 2 ** 10;

   PLANE_CTL_TILED_SURFACE : constant array (Tiling_Type) of Word32 :=
     (Linear   => PLANE_CTL_TILED_SURFACE_LINEAR,
      X_Tiled  => PLANE_CTL_TILED_SURFACE_X_TILED,
      Y_Tiled  => PLANE_CTL_TILED_SURFACE_Y_TILED);

   PLANE_CTL_PLANE_ROTATION_MASK       : constant := 3 * 2 ** 0;
   PLANE_CTL_PLANE_ROTATION : constant array (Rotation_Type) of Word32 :=
     (No_Rotation => 0 * 2 ** 0,
      Rotated_90  => 1 * 2 ** 0,
      Rotated_180 => 2 * 2 ** 0,
      Rotated_270 => 3 * 2 ** 0);

   PLANE_WM_ENABLE                     : constant :=        1 * 2 ** 31;
   PLANE_WM_LINES_SHIFT                : constant :=                 14;
   PLANE_WM_LINES_MASK                 : constant := 16#001f# * 2 ** 14;
   PLANE_WM_BLOCKS_MASK                : constant := 16#03ff# * 2 **  0;

   VGA_SR_INDEX                        : constant :=   16#03c4#;
   VGA_SR_DATA                         : constant :=   16#03c5#;
   VGA_SR01                            : constant :=     16#01#;
   VGA_SR01_SCREEN_OFF                 : constant := 1 * 2 ** 5;

   VGA_CONTROL_VGA_DISPLAY_DISABLE     : constant :=        1 * 2 ** 31;
   VGA_CONTROL_BLINK_DUTY_CYCLE_MASK   : constant := 16#0003# * 2 **  6;
   VGA_CONTROL_BLINK_DUTY_CYCLE_50     : constant :=        2 * 2 **  6;
   VGA_CONTROL_VSYNC_BLINK_RATE_MASK   : constant := 16#003f# * 2 **  0;

   CUR_CTL_PIPE_SELECT : constant array (Pipe_Index) of Word32 :=
     (Primary     => 0 * 2 ** 28,
      Secondary   => 1 * 2 ** 28,
      Tertiary    => 2 * 2 ** 28);
   CUR_CTL_MODE : constant array (Cursor_Mode, Cursor_Size) of Word32 :=
     (No_Cursor   => (others => 16#00#),
      ARGB_Cursor =>
        (Cursor_64x64   => 16#27#,
         Cursor_128x128 => 16#22#,
         Cursor_256x256 => 16#23#));

   function CUR_POS_Y (Y : Int32) return Word32 is
     ((if Y >= 0 then 0 else 1 * 2 ** 31) or Shift_Left (Word32 (abs Y), 16))
   with
      Pre => Y > Int32'First;
   function CUR_POS_X (X : Int32) return Word32 is
     ((if X >= 0 then 0 else 1 * 2 ** 15) or Word32 (abs X))
   with
      Pre => X > Int32'First;

   subtype VGA_Cycle_Count is Pos32 range 2 .. 128;
   function VGA_CONTROL_VSYNC_BLINK_RATE
     (Cycles : VGA_Cycle_Count)
      return Word32
   is
   begin
      return Word32 (Cycles) / 2 - 1;
   end VGA_CONTROL_VSYNC_BLINK_RATE;

   PF_CTRL_ENABLE                      : constant := 1 * 2 ** 31;
   PF_CTRL_PIPE_SELECT_MASK            : constant := 3 * 2 ** 29;
   PF_CTRL_FILTER_MED                  : constant := 1 * 2 ** 23;

   PS_CTRL_ENABLE_SCALER               : constant := 1 * 2 ** 31;
   PS_CTRL_SCALER_MODE_7X5_EXTENDED    : constant := 1 * 2 ** 28;
   PS_CTRL_FILTER_SELECT_MEDIUM_2      : constant := 1 * 2 ** 23;

   GMCH_PFIT_CONTROL_SELECT_MASK       : constant := 3 * 2 ** 29;
   GMCH_PFIT_CONTROL_SELECT_PIPE_A     : constant := 0 * 2 ** 29;
   GMCH_PFIT_CONTROL_SELECT_PIPE_B     : constant := 1 * 2 ** 29;
   GMCH_PFIT_CONTROL_SCALING_MASK      : constant := 3 * 2 ** 26;
   GMCH_PFIT_CONTROL_SCALING : constant array (Scaling_Aspect) of Word32 :=
     (Uniform     => 0 * 2 ** 26,
      Pillarbox   => 2 * 2 ** 26,
      Letterbox   => 3 * 2 ** 26);

   VGACNTRL_REG : constant Registers.Registers_Index :=
     (if Config.Has_GMCH_VGACNTRL then
         Registers.GMCH_VGACNTRL
      else Registers.CPU_VGACNTRL);

   ---------------------------------------------------------------------------

   function PLANE_WM_LINES (Lines : Natural) return Word32 is
   begin
      return Shift_Left (Word32 (Lines), PLANE_WM_LINES_SHIFT)
               and PLANE_WM_LINES_MASK;
   end PLANE_WM_LINES;

   function PLANE_WM_BLOCKS (Blocks : Natural) return Word32 is
   begin
      return Word32 (Blocks) and PLANE_WM_BLOCKS_MASK;
   end PLANE_WM_BLOCKS;

   ---------------------------------------------------------------------------

   function Encode (LSW, MSW : Pos32) return Word32 is
   begin
      return Shift_Left (Word32 (MSW) - 1, 16) or (Word32 (LSW) - 1);
   end Encode;

   ----------------------------------------------------------------------------

   procedure Clear_Watermarks (Controller : Controller_Type) is
   begin
      Registers.Write (Controller.CUR_BUF_CFG, 16#0000_0000#);
      for Level in WM_Levels loop
         Registers.Write (Controller.CUR_WM (Level), 16#0000_0000#);
      end loop;
      Registers.Write (Controller.PLANE_BUF_CFG, 16#0000_0000#);
      for Level in WM_Levels loop
         Registers.Write (Controller.PLANE_WM (Level), 16#0000_0000#);
      end loop;
      Registers.Write (Controller.WM_LINETIME, 16#0000_0000#);
   end Clear_Watermarks;

   procedure Setup_Watermarks (Controller : Controller_Type)
   is
      type Per_Plane_Buffer_Range is array (Pipe_Index) of Word32;
      Cur_Buffer_Range : constant Per_Plane_Buffer_Range :=
        (Primary     => Shift_Left (  7, 16) or   0,
         Secondary   => Shift_Left (167, 16) or 160,
         Tertiary    => Shift_Left (327, 16) or 320);
      Plane_Buffer_Range : constant Per_Plane_Buffer_Range :=
        (Primary     => Shift_Left (159, 16) or   8,
         Secondary   => Shift_Left (319, 16) or 168,
         Tertiary    => Shift_Left (479, 16) or 328);
   begin
      Registers.Write
        (Register    => Controller.PLANE_BUF_CFG,
         Value       => Plane_Buffer_Range (Controller.Pipe));
      Registers.Write
        (Register    => Controller.PLANE_WM (0),
         Value       => PLANE_WM_ENABLE or
                        PLANE_WM_LINES (2) or
                        PLANE_WM_BLOCKS (152));
      Registers.Write
        (Register    => Controller.CUR_BUF_CFG,
         Value       => Cur_Buffer_Range (Controller.Pipe));
      Registers.Write
        (Register    => Controller.CUR_WM (0),
         Value       => PLANE_WM_ENABLE or
                        PLANE_WM_LINES (2) or
                        PLANE_WM_BLOCKS (8));
   end Setup_Watermarks;

   ----------------------------------------------------------------------------

   procedure Setup_Hires_Plane
     (Controller  : Controller_Type;
      FB          : HW.GFX.Framebuffer_Type)
   with
      Global => (In_Out => Registers.Register_State),
      Depends =>
        (Registers.Register_State
            =>+
              (Registers.Register_State,
               Controller,
               FB)),
      Pre => FB.Height + FB.Start_Y <= FB.V_Stride
   is
      -- FIXME: setup correct format, based on framebuffer RGB format
      Format : constant Word32 := 6 * 2 ** 26;
      PRI : Word32 := DSPCNTR_ENABLE or Format;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.Has_Plane_Control then
         declare
            Stride, Offset : Word32;
            Width : constant Width_Type := Rotated_Width (FB);
            Height : constant Width_Type := Rotated_Height (FB);
         begin
            if Rotation_90 (FB) then
               Stride   := Word32 (FB_Pitch (FB.V_Stride, FB));
               Offset   := Shift_Left (Word32 (FB.Start_X), 16) or
                           Word32 (FB.V_Stride - FB.Height - FB.Start_Y);
            else
               Stride   := Word32 (FB_Pitch (FB.Stride, FB));
               Offset   := Shift_Left (Word32 (FB.Start_Y), 16) or
                           Word32 (FB.Start_X);
            end if;
            Registers.Write
              (Register    => Controller.PLANE_CTL,
               Value       => PLANE_CTL_PLANE_ENABLE or
                              PLANE_CTL_SRC_PIX_FMT_RGB_32B_8888 or
                              PLANE_CTL_PLANE_GAMMA_DISABLE or
                              PLANE_CTL_TILED_SURFACE (FB.Tiling) or
                              PLANE_CTL_PLANE_ROTATION (FB.Rotation));
            Registers.Write (Controller.PLANE_OFFSET, Offset);
            Registers.Write (Controller.PLANE_SIZE, Encode (Width, Height));
            Registers.Write (Controller.PLANE_STRIDE, Stride);
            Registers.Write (Controller.PLANE_POS, 16#0000_0000#);
            Registers.Write (Controller.PLANE_SURF, FB.Offset and 16#ffff_f000#);
         end;
      else
         if Config.Disable_Trickle_Feed then
            PRI := PRI or DSPCNTR_DISABLE_TRICKLE_FEED;
         end if;
         -- for now, just disable gamma LUT (can't do anything
         -- useful without colorimetry information from display)
         Registers.Unset_And_Set_Mask
            (Register   => Controller.DSPCNTR,
             Mask_Unset => DSPCNTR_MASK,
             Mask_Set   => PRI or DSPCNTR_TILED_SURFACE (FB.Tiling));

         Registers.Write
           (Controller.DSPSTRIDE, Word32 (Pixel_To_Bytes (FB.Stride, FB)));
         if Config.Has_DSP_Linoff and then FB.Tiling = Linear then
            Registers.Write
              (Register => Controller.DSPLINOFF,
               Value    => Word32 (Pixel_To_Bytes
                             (FB.Start_Y * FB.Stride + FB.Start_X, FB)));
            Registers.Write (Controller.DSPTILEOFF, 0);
         else
            if Config.Has_DSP_Linoff then
               Registers.Write (Controller.DSPLINOFF, 0);
            end if;
            Registers.Write
              (Register => Controller.DSPTILEOFF,
               Value    => Shift_Left (Word32 (FB.Start_Y), 16) or
                           Word32 (FB.Start_X));
         end if;
         Registers.Write (Controller.DSPSURF, FB.Offset and 16#ffff_f000#);
      end if;
   end Setup_Hires_Plane;

   procedure Setup_Display
     (Controller  : Controller_Type;
      Framebuffer : Framebuffer_Type;
      Dither_BPC  : BPC_Type;
      Dither      : Boolean)
   with
      Global => (In_Out => (Registers.Register_State, Port_IO.State)),
      Depends =>
        (Registers.Register_State
            =>+
              (Registers.Register_State,
               Controller,
               Framebuffer,
               Dither_BPC,
               Dither),
         Port_IO.State
            =>+
               (Framebuffer)),
      Pre =>
         Framebuffer.Offset = VGA_PLANE_FRAMEBUFFER_OFFSET or
         Framebuffer.Height + Framebuffer.Start_Y <= Framebuffer.V_Stride
   is
      use type Word8;

      Reg8 : Word8;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.Has_Plane_Control then
         Setup_Watermarks (Controller);
      end if;

      if Framebuffer.Offset = VGA_PLANE_FRAMEBUFFER_OFFSET then
         if Config.VGA_Plane_Workaround then
            Registers.Unset_And_Set_Mask
              (Register    => Registers.ILK_DISPLAY_CHICKEN1,
               Mask_Unset  => ILK_DISPLAY_CHICKEN1_VGA_MASK,
               Mask_Set    => ILK_DISPLAY_CHICKEN1_VGA_ENABLE);
            Registers.Unset_And_Set_Mask
              (Register    => Registers.ILK_DISPLAY_CHICKEN2,
               Mask_Unset  => ILK_DISPLAY_CHICKEN2_VGA_MASK,
               Mask_Set    => ILK_DISPLAY_CHICKEN2_VGA_ENABLE);
         end if;

         Registers.Unset_And_Set_Mask
           (Register    => VGACNTRL_REG,
            Mask_Unset  => VGA_CONTROL_VGA_DISPLAY_DISABLE or
                           VGA_CONTROL_BLINK_DUTY_CYCLE_MASK or
                           VGA_CONTROL_VSYNC_BLINK_RATE_MASK,
            Mask_Set    => VGA_CONTROL_BLINK_DUTY_CYCLE_50 or
                           VGA_CONTROL_VSYNC_BLINK_RATE (30));

         Port_IO.OutB (VGA_SR_INDEX, VGA_SR01);
         Port_IO.InB  (Reg8, VGA_SR_DATA);
         Port_IO.OutB (VGA_SR_DATA, Reg8 and not (VGA_SR01_SCREEN_OFF));
      else
         Setup_Hires_Plane (Controller, Framebuffer);
      end if;

      Registers.Write
        (Register => Controller.PIPESRC,
         Value    => Encode
           (Rotated_Height (Framebuffer), Rotated_Width (Framebuffer)));

      if Config.Has_Pipeconf_Misc then
         Registers.Write
           (Register => Controller.PIPEMISC,
            Value    => Transcoder.BPC_Conf (Dither_BPC, Dither));
      end if;
   end Setup_Display;

   ----------------------------------------------------------------------------

   procedure Update_Cursor
     (Pipe     : Pipe_Index;
      FB       : Framebuffer_Type;
      Cursor   : Cursor_Type)
   is
   begin
      -- on some platforms writing CUR_CTL disables self-arming of CUR_POS
      -- so keep it first
      Registers.Write
        (Register => Controllers (Pipe).CUR_CTL,
         Value    => CUR_CTL_PIPE_SELECT (Pipe) or
                     CUR_CTL_MODE (Cursor.Mode, Cursor.Size));
      Place_Cursor (Pipe, FB, Cursor);
   end Update_Cursor;

   procedure Place_Cursor
     (Pipe     : Pipe_Index;
      FB       : Framebuffer_Type;
      Cursor   : Cursor_Type)
   is
      Width : constant Width_Type := Cursor_Width (Cursor.Size);
      X : Int32 := Cursor.Center_X - Width / 2;
      Y : Int32 := Cursor.Center_Y - Width / 2;
   begin
      -- off-screen cursor needs special care
      if X <= -Width or Y <= -Width or
         X >= Rotated_Width (FB) or Y >= Rotated_Height (FB) or
         X > Config.Maximum_Cursor_X or Y > Config.Maximum_Cursor_Y
      then
         X := -Width;
         Y := -Width;
      end if;
      Registers.Write
        (Register => Controllers (Pipe).CUR_POS,
         Value    => CUR_POS_Y (Y) or CUR_POS_X (X));
      -- write to CUR_BASE always arms other CUR_* registers
      Registers.Write
        (Register => Controllers (Pipe).CUR_BASE,
         Value    => Shift_Left (Word32 (Cursor.GTT_Offset), 12));
   end Place_Cursor;

   ----------------------------------------------------------------------------

   function Scale (Val, Max, Num, Denom : Width_Type)
      return Width_Type is ((Val * Num) / Denom)
   with
      Pre => Denom <= Num and Val * Num < Max * Denom,
      Post => Scale'Result < Max;

   procedure Scale_Keep_Aspect
     (Width       :    out Width_Type;
      Height      :    out Height_Type;
      Max_Width   : in     Width_Type;
      Max_Height  : in     Height_Type;
      Framebuffer : in     Framebuffer_Type)
   with
      Pre =>
         Rotated_Width (Framebuffer) <= Max_Width and
         Rotated_Height (Framebuffer) <= Max_Height,
      Post =>
         Width <= Max_Width and Height <= Max_Height
   is
      Src_Width : constant Width_Type := Rotated_Width (Framebuffer);
      Src_Height : constant Height_Type := Rotated_Height (Framebuffer);
   begin
      case Scaling_Type (Src_Width, Src_Height, Max_Width, Max_Height) is
         when Letterbox =>
            Width  := Max_Width;
            Height := Scale (Src_Height, Max_Height, Max_Width, Src_Width);
         when Pillarbox =>
            Width  := Scale (Src_Width, Max_Width, Max_Height, Src_Height);
            Height := Max_Height;
         when Uniform =>
            Width  := Max_Width;
            Height := Max_Height;
      end case;
   end Scale_Keep_Aspect;

   procedure Setup_Skylake_Pipe_Scaler
     (Controller  : in     Controller_Type;
      Mode        : in     HW.GFX.Mode_Type;
      Framebuffer : in     HW.GFX.Framebuffer_Type)
   with
      Pre =>
         Rotated_Width (Framebuffer) <= Mode.H_Visible and
         Rotated_Height (Framebuffer) <= Mode.V_Visible
   is
      use type Registers.Registers_Invalid_Index;

      -- Enable 7x5 extended mode where possible:
      Scaler_Mode : constant Word32 :=
        (if Controller.PS_CTRL_2 /= Registers.Invalid_Register then
            PS_CTRL_SCALER_MODE_7X5_EXTENDED else 0);

      Width_In    : constant Width_Type   := Rotated_Width (Framebuffer);
      Height_In   : constant Height_Type  := Rotated_Height (Framebuffer);

      -- We can scale up to 2.99x horizontally:
      Horizontal_Limit : constant Pos32 := (Width_In * 299) / 100;
      -- The third scaler is limited to 1.99x
      -- vertical scaling for source widths > 2048:
      Vertical_Limit : constant Pos32 :=
        (Height_In *
           (if Controller.PS_CTRL_2 = Registers.Invalid_Register and
               Width_In > 2048
            then
               199
            else
               299)) / 100;

      Width : Width_Type;
      Height : Height_Type;
   begin
      -- Writes to WIN_SZ arm the PS registers.

      Scale_Keep_Aspect
        (Width       => Width,
         Height      => Height,
         Max_Width   => Pos32'Min (Horizontal_Limit, Mode.H_Visible),
         Max_Height  => Pos32'Min (Vertical_Limit, Mode.V_Visible),
         Framebuffer => Framebuffer);

      Registers.Write
        (Register => Controller.PS_CTRL_1,
         Value    => PS_CTRL_ENABLE_SCALER or Scaler_Mode);
      Registers.Write
        (Register => Controller.PS_WIN_POS_1,
         Value    =>
            Shift_Left (Word32 (Mode.H_Visible - Width) / 2, 16) or
            Word32 (Mode.V_Visible - Height) / 2);
      Registers.Write
        (Register => Controller.PS_WIN_SZ_1,
         Value    => Shift_Left (Word32 (Width), 16) or Word32 (Height));
   end Setup_Skylake_Pipe_Scaler;

   procedure Setup_Ironlake_Panel_Fitter
     (Controller  : in     Controller_Type;
      Mode        : in     HW.GFX.Mode_Type;
      Framebuffer : in     HW.GFX.Framebuffer_Type)
   with
      Pre =>
         Rotated_Width (Framebuffer) <= Mode.H_Visible and
         Rotated_Height (Framebuffer) <= Mode.V_Visible
   is
      -- Force 1:1 mapping of panel fitter:pipe
      PF_Ctrl_Pipe_Sel : constant Word32 :=
        (if Config.Has_PF_Pipe_Select then
           (case Controller.PF_CTRL is
               when Registers.PFA_CTL_1 => 0 * 2 ** 29,
               when Registers.PFB_CTL_1 => 1 * 2 ** 29,
               when Registers.PFC_CTL_1 => 2 * 2 ** 29,
               when others              => 0) else 0);

      Width : Width_Type;
      Height : Height_Type;
      X, Y : Int32;
   begin
      -- Writes to WIN_SZ arm the PF registers.

      Scale_Keep_Aspect
        (Width       => Width,
         Height      => Height,
         Max_Width   => Mode.H_Visible,
         Max_Height  => Mode.V_Visible,
         Framebuffer => Framebuffer);

      -- Do not scale to odd width (at least Haswell has trouble with this).
      if Width < Mode.H_Visible and Width mod 2 = 1 then
         Width := Width + 1;
      end if;

      X := (Mode.H_Visible - Width) / 2;
      Y := (Mode.V_Visible - Height) / 2;

      -- Hardware is picky about minimal horizontal gaps.
      if Mode.H_Visible - Width <= 3 then
         Width := Mode.H_Visible;
         X := 0;
      end if;

      Registers.Write
        (Register => Controller.PF_CTRL,
         Value    => PF_CTRL_ENABLE or PF_Ctrl_Pipe_Sel or PF_CTRL_FILTER_MED);
      Registers.Write
        (Register => Controller.PF_WIN_POS,
         Value    => Shift_Left (Word32 (X), 16) or Word32 (Y));
      Registers.Write
        (Register => Controller.PF_WIN_SZ,
         Value    => Shift_Left (Word32 (Width), 16) or Word32 (Height));
   end Setup_Ironlake_Panel_Fitter;

   procedure Setup_Gmch_Panel_Fitter
     (Controller  : in     Controller_Type;
      Mode        : in     HW.GFX.Mode_Type;
      Framebuffer : in     HW.GFX.Framebuffer_Type)
   is
      PF_Ctrl_Pipe_Sel : constant Word32 :=
           (case Controller.Pipe is
               when Primary   => GMCH_PFIT_CONTROL_SELECT_PIPE_A,
               when Secondary => GMCH_PFIT_CONTROL_SELECT_PIPE_B,
               when others    => 0);

      -- Work around a quirk:
      -- In legacy VGA mode Pillarbox fails to display anything so just force
      -- 'auto' mode on all displays, which will the output stretched to
      -- fullscreen .
      PF_Ctrl_Scaling : constant Word32 :=
        (if Framebuffer.Offset = VGA_PLANE_FRAMEBUFFER_OFFSET then
           GMCH_PFIT_CONTROL_SCALING (Uniform)
         else
           GMCH_PFIT_CONTROL_SCALING (Scaling_Type (Framebuffer, Mode)));

      In_Use : Boolean;
   begin
      Registers.Is_Set_Mask
        (Register => Registers.GMCH_PFIT_CONTROL,
         Mask     => PF_CTRL_ENABLE,
         Result   => In_Use);

      if not In_Use then
         Registers.Write
           (Register => Registers.GMCH_PFIT_CONTROL,
            Value    => PF_CTRL_ENABLE or PF_Ctrl_Pipe_Sel or PF_Ctrl_Scaling);
      else
         pragma Debug (Debug.Put_Line
           ("GMCH Pannel fitter already in use, skipping..."));
      end if;
   end Setup_Gmch_Panel_Fitter;

   procedure Gmch_Panel_Fitter_Pipe (Pipe : out Pipe_Index)
   is
      Used_For_Secondary : Boolean;
   begin
      Registers.Is_Set_Mask
        (Register => Registers.GMCH_PFIT_CONTROL,
         Mask     => GMCH_PFIT_CONTROL_SELECT_PIPE_B,
         Result   => Used_For_Secondary);
      Pipe := (if Used_For_Secondary then Secondary else Primary);
   end;

   procedure Panel_Fitter_Off (Controller : Controller_Type)
   is
      use type HW.GFX.GMA.Registers.Registers_Invalid_Index;
      Pipe_Using_PF : Pipe_Index;
   begin
      -- Writes to WIN_SZ arm the PS/PF registers.
      if Config.Has_Plane_Control then
         Registers.Unset_Mask (Controller.PS_CTRL_1, PS_CTRL_ENABLE_SCALER);
         Registers.Write (Controller.PS_WIN_SZ_1, 16#0000_0000#);
         if Controller.PS_CTRL_2 /= Registers.Invalid_Register and
            Controller.PS_WIN_SZ_2 /= Registers.Invalid_Register
         then
            Registers.Unset_Mask (Controller.PS_CTRL_2, PS_CTRL_ENABLE_SCALER);
            Registers.Write (Controller.PS_WIN_SZ_2, 16#0000_0000#);
         end if;
      elsif Config.Has_GMCH_PFIT_CONTROL then
         Gmch_Panel_Fitter_Pipe (Pipe_Using_PF);
         if Pipe_Using_PF = Controller.Pipe then
            Registers.Unset_Mask (Registers.GMCH_PFIT_CONTROL, PF_CTRL_ENABLE);
         end if;
      else
         Registers.Unset_Mask (Controller.PF_CTRL, PF_CTRL_ENABLE);
         Registers.Write (Controller.PF_WIN_SZ, 16#0000_0000#);
      end if;
   end Panel_Fitter_Off;

   procedure Setup_Scaling
     (Controller  : in     Controller_Type;
      Mode        : in     HW.GFX.Mode_Type;
      Framebuffer : in     HW.GFX.Framebuffer_Type)
   with
      Pre =>
         Rotated_Width (Framebuffer) <= Mode.H_Visible and
         Rotated_Height (Framebuffer) <= Mode.V_Visible
   is
   begin
      if Requires_Scaling (Framebuffer, Mode) then
         if Config.Has_Plane_Control then
            Setup_Skylake_Pipe_Scaler (Controller, Mode, Framebuffer);
         elsif Config.Has_GMCH_PFIT_CONTROL then
            Setup_Gmch_Panel_Fitter (Controller, Mode, Framebuffer);
         else
            Setup_Ironlake_Panel_Fitter (Controller, Mode, Framebuffer);
         end if;
      else
         Panel_Fitter_Off (Controller);
      end if;
   end Setup_Scaling;

   procedure Scaler_Available (Available : out Boolean; Pipe : Pipe_Index)
   is
      Pipe_Using_PF : Pipe_Index := Pipe_Index'First;
      PF_Enabled : Boolean;
   begin
      if Config.Has_GMCH_PFIT_CONTROL then
         Registers.Is_Set_Mask
           (Register => Registers.GMCH_PFIT_CONTROL,
            Mask     => PF_CTRL_ENABLE,
            Result   => PF_Enabled);
         if PF_Enabled then
            Gmch_Panel_Fitter_Pipe (Pipe_Using_PF);
         end if;

         Available := not PF_Enabled or Pipe_Using_PF = Pipe;
      else
         Available := True;
      end if;
   end Scaler_Available;

   ----------------------------------------------------------------------------

   procedure Setup_FB
     (Pipe        : Pipe_Index;
      Mode        : Mode_Type;
      Framebuffer : Framebuffer_Type)
   is
      -- Enable dithering if framebuffer BPC differs from port BPC,
      -- as smooth gradients look really bad without.
      Dither : constant Boolean := Framebuffer.BPC /= Mode.BPC;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- Disable the cursor first.
      Update_Cursor (Pipe, Framebuffer, Default_Cursor);

      Setup_Display (Controllers (Pipe), Framebuffer, Mode.BPC, Dither);
      Setup_Scaling (Controllers (Pipe), Mode, Framebuffer);
   end Setup_FB;

   procedure On
     (Pipe        : Pipe_Index;
      Port_Cfg    : Port_Config;
      Framebuffer : Framebuffer_Type;
      Cursor      : Cursor_Type)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Transcoder.Setup (Pipe, Port_Cfg);

      Setup_FB (Pipe, Port_Cfg.Mode, Framebuffer);
      Update_Cursor (Pipe, Framebuffer, Cursor);

      Transcoder.On
        (Pipe     => Pipe,
         Port_Cfg => Port_Cfg,
         Dither   => Framebuffer.BPC /= Port_Cfg.Mode.BPC,
         Scale    => Requires_Scaling (Framebuffer, Port_Cfg.Mode));
   end On;

   ----------------------------------------------------------------------------

   procedure Planes_Off (Controller : Controller_Type) is
   begin
      Registers.Write (Controller.CUR_CTL, 16#0000_0000#);
      if Config.Has_Cursor_FBC_Control then
         Registers.Write (Controller.CUR_FBC_CTL, 16#0000_0000#);
      end if;
      Registers.Unset_Mask (Controller.SPCNTR, DSPCNTR_ENABLE);
      if Config.Has_Plane_Control then
         Clear_Watermarks (Controller);
         Registers.Unset_Mask (Controller.PLANE_CTL, PLANE_CTL_PLANE_ENABLE);
         Registers.Write (Controller.PLANE_SURF, 16#0000_0000#);
      else
         Registers.Unset_Mask (Controller.DSPCNTR, DSPCNTR_ENABLE);
      end if;
   end Planes_Off;

   procedure Off (Pipe : Pipe_Index)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Planes_Off (Controllers (Pipe));
      Transcoder.Off (Pipe);
      Panel_Fitter_Off (Controllers (Pipe));
      Transcoder.Clk_Off (Pipe);
   end Off;

   procedure Legacy_VGA_Off
   is
      use type HW.Word8;
      Reg8 : Word8;
   begin
      Port_IO.OutB (VGA_SR_INDEX, VGA_SR01);
      Port_IO.InB  (Reg8, VGA_SR_DATA);
      Port_IO.OutB (VGA_SR_DATA, Reg8 or VGA_SR01_SCREEN_OFF);
      Time.U_Delay (100); -- PRM says 100us, Linux does 300
      Registers.Set_Mask (VGACNTRL_REG, VGA_CONTROL_VGA_DISPLAY_DISABLE);
   end Legacy_VGA_Off;

   procedure All_Off
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Legacy_VGA_Off;

      for Pipe in Pipe_Index loop
         Planes_Off (Controllers (Pipe));
         Transcoder.Off (Pipe);
         Panel_Fitter_Off (Controllers (Pipe));
         Transcoder.Clk_Off (Pipe);
      end loop;
   end All_Off;

end HW.GFX.GMA.Pipe_Setup;
