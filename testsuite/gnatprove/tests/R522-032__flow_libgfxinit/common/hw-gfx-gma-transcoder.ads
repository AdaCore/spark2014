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

with HW.GFX.GMA.Registers;
with HW.GFX.GMA.Config;

private package HW.GFX.GMA.Transcoder
is

   procedure Setup (Pipe : Pipe_Index; Port_Cfg : Port_Config);
   procedure On
     (Pipe     : Pipe_Index;
      Port_Cfg : Port_Config;
      Dither   : Boolean;
      Scale    : Boolean);

   procedure Off (Pipe : Pipe_Index);
   procedure Clk_Off (Pipe : Pipe_Index);

   function BPC_Conf (BPC : BPC_Type; Dither : Boolean) return Word32;

private

   type Transcoder_Index is (Trans_EDP, Trans_A, Trans_B, Trans_C);

   type Transcoder_Regs is
      record
         HTOTAL         : Registers.Registers_Index;
         HBLANK         : Registers.Registers_Index;
         HSYNC          : Registers.Registers_Index;
         VTOTAL         : Registers.Registers_Index;
         VBLANK         : Registers.Registers_Index;
         VSYNC          : Registers.Registers_Index;
         CONF           : Registers.Registers_Index;
         DATA_M1        : Registers.Registers_Index;
         DATA_N1        : Registers.Registers_Index;
         LINK_M1        : Registers.Registers_Index;
         LINK_N1        : Registers.Registers_Index;
         DDI_FUNC_CTL   : Registers.Registers_Index;
         MSA_MISC       : Registers.Registers_Index;
         CLK_SEL        : Registers.Registers_Invalid_Index;
      end record;

   type Transcoder_Array is array (Transcoder_Index) of Transcoder_Regs;

   PIPE_DATA_M1 : constant array (0 .. 1) of Registers.Registers_Index :=
     (if Config.Has_GMCH_DP_Transcoder then
        (0 => Registers.PIPEA_GMCH_DATA_M,
         1 => Registers.PIPEB_GMCH_DATA_M)
      else
        (0 => Registers.PIPEA_DATA_M1,
         1 => Registers.PIPEB_DATA_M1));
   PIPE_DATA_N1 : constant array (0 .. 1) of Registers.Registers_Index :=
     (if Config.Has_GMCH_DP_Transcoder then
        (0 => Registers.PIPEA_GMCH_DATA_N,
         1 => Registers.PIPEB_GMCH_DATA_N)
      else
        (0 => Registers.PIPEA_DATA_N1,
         1 => Registers.PIPEB_DATA_N1));
   PIPE_LINK_M1 : constant array (0 .. 1) of Registers.Registers_Index :=
     (if Config.Has_GMCH_DP_Transcoder then
        (0 => Registers.PIPEA_GMCH_LINK_M,
         1 => Registers.PIPEB_GMCH_LINK_M)
      else
        (0 => Registers.PIPEA_LINK_M1,
         1 => Registers.PIPEB_LINK_M1));
   PIPE_LINK_N1 : constant array (0 .. 1) of Registers.Registers_Index :=
     (if Config.Has_GMCH_DP_Transcoder then
        (0 => Registers.PIPEA_GMCH_LINK_N,
         1 => Registers.PIPEB_GMCH_LINK_N)
      else
        (0 => Registers.PIPEA_LINK_N1,
         1 => Registers.PIPEB_LINK_N1));

   Transcoders : constant Transcoder_Array :=
     (Trans_EDP =>
        (HTOTAL         => Registers.HTOTAL_EDP,
         HBLANK         => Registers.HBLANK_EDP,
         HSYNC          => Registers.HSYNC_EDP,
         VTOTAL         => Registers.VTOTAL_EDP,
         VBLANK         => Registers.VBLANK_EDP,
         VSYNC          => Registers.VSYNC_EDP,
         CONF           => Registers.PIPE_EDP_CONF,
         DATA_M1        => Registers.PIPE_EDP_DATA_M1,
         DATA_N1        => Registers.PIPE_EDP_DATA_N1,
         LINK_M1        => Registers.PIPE_EDP_LINK_M1,
         LINK_N1        => Registers.PIPE_EDP_LINK_N1,
         DDI_FUNC_CTL   => Registers.PIPE_EDP_DDI_FUNC_CTL,
         MSA_MISC       => Registers.PIPE_EDP_MSA_MISC,
         CLK_SEL        => Registers.Invalid_Register),
      Trans_A =>
        (HTOTAL         => Registers.HTOTAL_A,
         HBLANK         => Registers.HBLANK_A,
         HSYNC          => Registers.HSYNC_A,
         VTOTAL         => Registers.VTOTAL_A,
         VBLANK         => Registers.VBLANK_A,
         VSYNC          => Registers.VSYNC_A,
         CONF           => Registers.PIPEACONF,
         DATA_M1        => PIPE_DATA_M1 (0),
         DATA_N1        => PIPE_DATA_N1 (0),
         LINK_M1        => PIPE_LINK_M1 (0),
         LINK_N1        => PIPE_LINK_N1 (0),
         DDI_FUNC_CTL   => Registers.PIPEA_DDI_FUNC_CTL,
         MSA_MISC       => Registers.PIPEA_MSA_MISC,
         CLK_SEL        => Registers.TRANSA_CLK_SEL),
      Trans_B =>
        (HTOTAL         => Registers.HTOTAL_B,
         HBLANK         => Registers.HBLANK_B,
         HSYNC          => Registers.HSYNC_B,
         VTOTAL         => Registers.VTOTAL_B,
         VBLANK         => Registers.VBLANK_B,
         VSYNC          => Registers.VSYNC_B,
         CONF           => Registers.PIPEBCONF,
         DATA_M1        => PIPE_DATA_M1 (1),
         DATA_N1        => PIPE_DATA_N1 (1),
         LINK_M1        => PIPE_LINK_M1 (1),
         LINK_N1        => PIPE_LINK_N1 (1),
         DDI_FUNC_CTL   => Registers.PIPEB_DDI_FUNC_CTL,
         MSA_MISC       => Registers.PIPEB_MSA_MISC,
         CLK_SEL        => Registers.TRANSB_CLK_SEL),
      Trans_C =>
        (HTOTAL         => Registers.HTOTAL_C,
         HBLANK         => Registers.HBLANK_C,
         HSYNC          => Registers.HSYNC_C,
         VTOTAL         => Registers.VTOTAL_C,
         VBLANK         => Registers.VBLANK_C,
         VSYNC          => Registers.VSYNC_C,
         CONF           => Registers.PIPECCONF,
         DATA_M1        => Registers.PIPEC_DATA_M1,
         DATA_N1        => Registers.PIPEC_DATA_N1,
         LINK_M1        => Registers.PIPEC_LINK_M1,
         LINK_N1        => Registers.PIPEC_LINK_N1,
         DDI_FUNC_CTL   => Registers.PIPEC_DDI_FUNC_CTL,
         MSA_MISC       => Registers.PIPEC_MSA_MISC,
         CLK_SEL        => Registers.TRANSC_CLK_SEL));

end HW.GFX.GMA.Transcoder;
