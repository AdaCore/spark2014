--
-- Copyright (C) 2015-2016 secunet Security Networks AG
-- Copyright (C) 2016 Nico Huber <nico.h@gmx.de>
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
with HW.GFX.GMA.DP_Info;
with HW.GFX.GMA.Registers;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.PCH.Transcoder is

   type DPLL_SEL_Array is array (FDI_Port_Type) of Word32;
   DPLL_SEL_TRANSCODER_x_DPLL_ENABLE : constant DPLL_SEL_Array :=
     (FDI_A => 1 * 2 **  3,
      FDI_B => 1 * 2 **  7,
      FDI_C => 1 * 2 ** 11);
   DPLL_SEL_TRANSCODER_x_DPLL_SEL_MASK : constant DPLL_SEL_Array :=
     (FDI_A => 1 * 2 **  0,
      FDI_B => 1 * 2 **  4,
      FDI_C => 1 * 2 **  8);
   function DPLL_SEL_TRANSCODER_x_DPLL_SEL
     (Port : FDI_Port_Type;
      PLL  : Word32)
      return Word32
   is
   begin
      return Shift_Left (PLL,
        (case Port is
            when FDI_A => 0,
            when FDI_B => 4,
            when FDI_C => 8));
   end DPLL_SEL_TRANSCODER_x_DPLL_SEL;

   TRANS_CONF_TRANSCODER_ENABLE        : constant := 1 * 2 ** 31;
   TRANS_CONF_TRANSCODER_STATE         : constant := 1 * 2 ** 30;

   TRANS_CHICKEN2_TIMING_OVERRIDE      : constant := 1 * 2 ** 31;

   TRANS_DP_CTL_OUTPUT_ENABLE          : constant := 1 * 2 ** 31;
   TRANS_DP_CTL_PORT_SELECT_MASK       : constant := 3 * 2 ** 29;
   TRANS_DP_CTL_PORT_SELECT_NONE       : constant := 3 * 2 ** 29;
   TRANS_DP_CTL_ENHANCED_FRAMING       : constant := 1 * 2 ** 18;
   TRANS_DP_CTL_VSYNC_ACTIVE_HIGH      : constant := 1 * 2 **  4;
   TRANS_DP_CTL_HSYNC_ACTIVE_HIGH      : constant := 1 * 2 **  3;

   type TRANS_DP_CTL_PORT_SELECT_Array is array (PCH_Port) of Word32;
   TRANS_DP_CTL_PORT_SELECT : constant TRANS_DP_CTL_PORT_SELECT_Array :=
     (PCH_DP_B => 0 * 2 ** 29,
      PCH_DP_C => 1 * 2 ** 29,
      PCH_DP_D => 2 * 2 ** 29,
      others   => 0);

   function TRANS_DP_CTL_BPC (BPC : BPC_Type) return Word32
   is
   begin
      return
        (case BPC is
            when      6 => 2 * 2 ** 9,
            when     10 => 1 * 2 ** 9,
            when     12 => 3 * 2 ** 9,
            when others => 0 * 2 ** 9);
   end TRANS_DP_CTL_BPC;

   function TRANS_DATA_M_TU (Transfer_Unit : Positive) return Word32 is
   begin
      return Shift_Left (Word32 (Transfer_Unit - 1), 25);
   end TRANS_DATA_M_TU;

   ----------------------------------------------------------------------------

   type Transcoder_Registers is record
      HTOTAL   : Registers.Registers_Index;
      HBLANK   : Registers.Registers_Index;
      HSYNC    : Registers.Registers_Index;
      VTOTAL   : Registers.Registers_Index;
      VBLANK   : Registers.Registers_Index;
      VSYNC    : Registers.Registers_Index;
      CONF     : Registers.Registers_Index;
      DP_CTL   : Registers.Registers_Index;
      DATA_M   : Registers.Registers_Index;
      DATA_N   : Registers.Registers_Index;
      LINK_M   : Registers.Registers_Index;
      LINK_N   : Registers.Registers_Index;
      CHICKEN2 : Registers.Registers_Index;
   end record;

   type Transcoder_Registers_Array is
      array (FDI_Port_Type) of Transcoder_Registers;

   TRANS : constant Transcoder_Registers_Array := Transcoder_Registers_Array'
     (FDI_A =>
        (HTOTAL   => Registers.TRANS_HTOTAL_A,
         HBLANK   => Registers.TRANS_HBLANK_A,
         HSYNC    => Registers.TRANS_HSYNC_A,
         VTOTAL   => Registers.TRANS_VTOTAL_A,
         VBLANK   => Registers.TRANS_VBLANK_A,
         VSYNC    => Registers.TRANS_VSYNC_A,
         CONF     => Registers.TRANSACONF,
         DP_CTL   => Registers.TRANS_DP_CTL_A,
         DATA_M   => Registers.TRANSA_DATA_M1,
         DATA_N   => Registers.TRANSA_DATA_N1,
         LINK_M   => Registers.TRANSA_DP_LINK_M1,
         LINK_N   => Registers.TRANSA_DP_LINK_N1,
         CHICKEN2 => Registers.TRANSA_CHICKEN2),
      FDI_B =>
        (HTOTAL   => Registers.TRANS_HTOTAL_B,
         HBLANK   => Registers.TRANS_HBLANK_B,
         HSYNC    => Registers.TRANS_HSYNC_B,
         VTOTAL   => Registers.TRANS_VTOTAL_B,
         VBLANK   => Registers.TRANS_VBLANK_B,
         VSYNC    => Registers.TRANS_VSYNC_B,
         CONF     => Registers.TRANSBCONF,
         DP_CTL   => Registers.TRANS_DP_CTL_B,
         DATA_M   => Registers.TRANSB_DATA_M1,
         DATA_N   => Registers.TRANSB_DATA_N1,
         LINK_M   => Registers.TRANSB_DP_LINK_M1,
         LINK_N   => Registers.TRANSB_DP_LINK_N1,
         CHICKEN2 => Registers.TRANSB_CHICKEN2),
      FDI_C =>
        (HTOTAL   => Registers.TRANS_HTOTAL_C,
         HBLANK   => Registers.TRANS_HBLANK_C,
         HSYNC    => Registers.TRANS_HSYNC_C,
         VTOTAL   => Registers.TRANS_VTOTAL_C,
         VBLANK   => Registers.TRANS_VBLANK_C,
         VSYNC    => Registers.TRANS_VSYNC_C,
         CONF     => Registers.TRANSCCONF,
         DP_CTL   => Registers.TRANS_DP_CTL_C,
         DATA_M   => Registers.TRANSC_DATA_M1,
         DATA_N   => Registers.TRANSC_DATA_N1,
         LINK_M   => Registers.TRANSC_DP_LINK_M1,
         LINK_N   => Registers.TRANSC_DP_LINK_N1,
         CHICKEN2 => Registers.TRANSC_CHICKEN2));

   ----------------------------------------------------------------------------

   procedure On
     (Port_Cfg : Port_Config;
      Port     : FDI_Port_Type;
      PLL      : Word32)
   is
      Mode : constant Mode_Type := Port_Cfg.Mode;

      function Encode (LSW, MSW : Pos32) return Word32 is
      begin
         return (Word32 (LSW) - 1) or ((Word32 (MSW) - 1) * 2 ** 16);
      end Encode;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.Has_DPLL_SEL then
         Registers.Unset_And_Set_Mask
           (Register    => Registers.PCH_DPLL_SEL,
            Mask_Unset  => DPLL_SEL_TRANSCODER_x_DPLL_SEL_MASK (Port),
            Mask_Set    => DPLL_SEL_TRANSCODER_x_DPLL_ENABLE (Port) or
                           DPLL_SEL_TRANSCODER_x_DPLL_SEL (Port, PLL));
      end if;

      Registers.Write
        (Register => TRANS (Port).HTOTAL,
         Value    => Encode (Mode.H_Visible,    Mode.H_Total));
      Registers.Write
        (Register => TRANS (Port).HBLANK,
         Value    => Encode (Mode.H_Visible,    Mode.H_Total));
      Registers.Write
        (Register => TRANS (Port).HSYNC,
         Value    => Encode (Mode.H_Sync_Begin, Mode.H_Sync_End));
      Registers.Write
        (Register => TRANS (Port).VTOTAL,
         Value    => Encode (Mode.V_Visible,    Mode.V_Total));
      Registers.Write
        (Register => TRANS (Port).VBLANK,
         Value    => Encode (Mode.V_Visible,    Mode.V_Total));
      Registers.Write
        (Register => TRANS (Port).VSYNC,
         Value    => Encode (Mode.V_Sync_Begin, Mode.V_Sync_End));

      if Port_Cfg.Display = DP then
         declare
            Data_M, Link_M : DP_Info.M_Type;
            Data_N, Link_N : DP_Info.N_Type;
         begin
            DP_Info.Calculate_M_N
              (Link     => Port_Cfg.DP,
               Mode     => Port_Cfg.Mode,
               Data_M   => Data_M,
               Data_N   => Data_N,
               Link_M   => Link_M,
               Link_N   => Link_N);
            Registers.Write
              (Register => TRANS (Port).DATA_M,
               Value    => TRANS_DATA_M_TU (64) or
                           Word32 (Data_M));
            Registers.Write
              (Register => TRANS (Port).DATA_N,
               Value    => Word32 (Data_N));
            Registers.Write
              (Register => TRANS (Port).LINK_M,
               Value    => Word32 (Link_M));
            Registers.Write
              (Register => TRANS (Port).LINK_N,
               Value    => Word32 (Link_N));
         end;

         if Config.Has_Trans_DP_Ctl then
            declare
               Polarity : constant Word32 :=
                 (if Port_Cfg.Mode.H_Sync_Active_High then
                     TRANS_DP_CTL_HSYNC_ACTIVE_HIGH else 0) or
                 (if Port_Cfg.Mode.V_Sync_Active_High then
                     TRANS_DP_CTL_VSYNC_ACTIVE_HIGH else 0);
               Enhanced_Framing : constant Word32 :=
                 (if Port_Cfg.DP.Enhanced_Framing then
                     TRANS_DP_CTL_ENHANCED_FRAMING else 0);
            begin
               Registers.Write
                 (Register => TRANS (Port).DP_CTL,
                  Value    => TRANS_DP_CTL_OUTPUT_ENABLE or
                              TRANS_DP_CTL_PORT_SELECT (Port_Cfg.PCH_Port) or
                              Enhanced_Framing or
                              TRANS_DP_CTL_BPC (Port_Cfg.Mode.BPC) or
                              Polarity);
            end;
         end if;
      end if;

      if Config.Has_Trans_Timing_Ovrrde then
         Registers.Set_Mask
           (Register => TRANS (Port).CHICKEN2,
            Mask     => TRANS_CHICKEN2_TIMING_OVERRIDE);
      end if;

      Registers.Write
        (Register => TRANS (Port).CONF,
         Value    => TRANS_CONF_TRANSCODER_ENABLE);
   end On;

   procedure Off (Port : FDI_Port_Type) is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_Mask
        (Register => TRANS (Port).CONF,
         Mask     => TRANS_CONF_TRANSCODER_ENABLE);
      Registers.Wait_Unset_Mask
        (Register => TRANS (Port).CONF,
         Mask     => TRANS_CONF_TRANSCODER_STATE,
         TOut_MS  => 50);

      if Config.Has_Trans_Timing_Ovrrde then
         Registers.Unset_Mask
           (Register => TRANS (Port).CHICKEN2,
            Mask     => TRANS_CHICKEN2_TIMING_OVERRIDE);
      end if;

      if Config.Has_Trans_DP_Ctl then
         Registers.Write
           (Register => TRANS (Port).DP_CTL,
            Value    => TRANS_DP_CTL_PORT_SELECT_NONE);
      end if;

      if Config.Has_DPLL_SEL then
         Registers.Unset_Mask
           (Register => Registers.PCH_DPLL_SEL,
            Mask     => DPLL_SEL_TRANSCODER_x_DPLL_ENABLE (Port));
      end if;
   end Off;

end HW.GFX.GMA.PCH.Transcoder;
