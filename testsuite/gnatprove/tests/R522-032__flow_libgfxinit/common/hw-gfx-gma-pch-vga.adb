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
with HW.GFX.GMA.Registers;
with HW.GFX.GMA.PCH.Sideband;

with HW.Debug;
with GNAT.Source_Info;

use type HW.Word64;

package body HW.GFX.GMA.PCH.VGA is

   PCH_ADPA_DAC_ENABLE        : constant := 1 * 2 ** 31;
   PCH_ADPA_VSYNC_DISABLE     : constant := 1 * 2 ** 11;
   PCH_ADPA_HSYNC_DISABLE     : constant := 1 * 2 ** 10;
   PCH_ADPA_VSYNC_ACTIVE_HIGH : constant := 1 * 2 **  4;
   PCH_ADPA_HSYNC_ACTIVE_HIGH : constant := 1 * 2 **  3;

   PCH_ADPA_MASK : constant Word32 :=
      PCH_TRANSCODER_SELECT_MASK or
      PCH_ADPA_DAC_ENABLE        or
      PCH_ADPA_VSYNC_DISABLE     or
      PCH_ADPA_HSYNC_DISABLE     or
      PCH_ADPA_VSYNC_ACTIVE_HIGH or
      PCH_ADPA_HSYNC_ACTIVE_HIGH;

   ----------------------------------------------------------------------------

   procedure On
     (Port : FDI_Port_Type;
      Mode : Mode_Type)
   is
      Polarity : Word32 := 0;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Mode.H_Sync_Active_High then
         Polarity := Polarity or PCH_ADPA_HSYNC_ACTIVE_HIGH;
      end if;
      if Mode.V_Sync_Active_High then
         Polarity := Polarity or PCH_ADPA_VSYNC_ACTIVE_HIGH;
      end if;

      Registers.Unset_And_Set_Mask
        (Register    => Registers.PCH_ADPA,
         Mask_Unset  => PCH_ADPA_MASK,
         Mask_Set    => PCH_ADPA_DAC_ENABLE or
                        PCH_TRANSCODER_SELECT (Port) or
                        Polarity);
   end On;

   ----------------------------------------------------------------------------

   procedure Off
   is
      Sync_Disable : Word32 := 0;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.VGA_Has_Sync_Disable then
         Sync_Disable := PCH_ADPA_HSYNC_DISABLE or PCH_ADPA_VSYNC_DISABLE;
      end if;

      Registers.Unset_And_Set_Mask
        (Register    => Registers.PCH_ADPA,
         Mask_Unset  => PCH_ADPA_DAC_ENABLE,
         Mask_Set    => Sync_Disable);
   end Off;

   ----------------------------------------------------------------------------

   PCH_PIXCLK_GATE_GATE    : constant := 0 * 2 ** 0;
   PCH_PIXCLK_GATE_UNGATE  : constant := 1 * 2 ** 0;

   SBI_SSCCTL_DISABLE               : constant :=      1 * 2 **  0;
   SBI_SSCDIVINTPHASE_DIVSEL_SHIFT  : constant :=                1;
   SBI_SSCDIVINTPHASE_DIVSEL_MASK   : constant := 16#7f# * 2 **  1;
   SBI_SSCDIVINTPHASE_INCVAL_SHIFT  : constant :=                8;
   SBI_SSCDIVINTPHASE_INCVAL_MASK   : constant := 16#7f# * 2 **  8;
   SBI_SSCDIVINTPHASE_DIR_SHIFT     : constant :=               15;
   SBI_SSCDIVINTPHASE_DIR_MASK      : constant := 16#01# * 2 ** 15;
   SBI_SSCDIVINTPHASE_PROPAGATE     : constant :=      1 * 2 **  0;
   SBI_SSCAUXDIV_FINALDIV2SEL_SHIFT : constant :=                4;
   SBI_SSCAUXDIV_FINALDIV2SEL_MASK  : constant := 16#01# * 2 **  4;

   function SBI_SSCDIVINTPHASE_DIVSEL (Val : Word32) return Word32 is
   begin
      return Shift_Left (Val, SBI_SSCDIVINTPHASE_DIVSEL_SHIFT);
   end SBI_SSCDIVINTPHASE_DIVSEL;

   function SBI_SSCDIVINTPHASE_INCVAL (Val : Word32) return Word32 is
   begin
      return Shift_Left (Val, SBI_SSCDIVINTPHASE_INCVAL_SHIFT);
   end SBI_SSCDIVINTPHASE_INCVAL;

   function SBI_SSCDIVINTPHASE_DIR (Val : Word32) return Word32 is
   begin
      return Shift_Left (Val, SBI_SSCDIVINTPHASE_DIR_SHIFT);
   end SBI_SSCDIVINTPHASE_DIR;

   function SBI_SSCAUXDIV_FINALDIV2SEL (Val : Word32) return Word32 is
   begin
      return Shift_Left (Val, SBI_SSCAUXDIV_FINALDIV2SEL_SHIFT);
   end SBI_SSCAUXDIV_FINALDIV2SEL;

   procedure Clock_On (Mode : Mode_Type)
   is
      Refclock : constant := 2_700_000_000;

      Aux_Div,
      Div_Sel,
      Phase_Inc,
      Phase_Dir   : Word32;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Write (Registers.PCH_PIXCLK_GATE, PCH_PIXCLK_GATE_GATE);

      Sideband.Set_Mask
        (Dest     => Sideband.SBI_ICLK,
         Register => Sideband.SBI_SSCCTL6,
         Mask     => SBI_SSCCTL_DISABLE);

      Aux_Div     := 16#0000_0000#;
      Div_Sel     := Word32 (Refclock / Mode.Dotclock - 2);
      Phase_Inc   := Word32 ((Refclock * 64) / Mode.Dotclock) and 16#0000_003f#;
      Phase_Dir   := 16#0000_0000#;

      pragma Debug (Debug.Put_Reg32 ("Aux_Div  ", Aux_Div));
      pragma Debug (Debug.Put_Reg32 ("Div_Sel  ", Div_Sel));
      pragma Debug (Debug.Put_Reg32 ("Phase_Inc", Phase_Inc));
      pragma Debug (Debug.Put_Reg32 ("Phase_Dir", Phase_Dir));

      Sideband.Unset_And_Set_Mask
        (Dest        => Sideband.SBI_ICLK,
         Register    => Sideband.SBI_SSCDIVINTPHASE6,
         Mask_Unset  => SBI_SSCDIVINTPHASE_DIVSEL_MASK or
                        SBI_SSCDIVINTPHASE_INCVAL_MASK or
                        SBI_SSCDIVINTPHASE_DIR_MASK,
         Mask_Set    => SBI_SSCDIVINTPHASE_DIVSEL (Div_Sel) or
                        SBI_SSCDIVINTPHASE_INCVAL (Phase_Inc) or
                        SBI_SSCDIVINTPHASE_DIR (Phase_Dir) or
                        SBI_SSCDIVINTPHASE_PROPAGATE);

      Sideband.Unset_And_Set_Mask
        (Dest        => Sideband.SBI_ICLK,
         Register    => Sideband.SBI_SSCAUXDIV,
         Mask_Unset  => SBI_SSCAUXDIV_FINALDIV2SEL_MASK,
         Mask_Set    => SBI_SSCAUXDIV_FINALDIV2SEL (Aux_Div));

      Sideband.Unset_Mask
        (Dest     => Sideband.SBI_ICLK,
         Register => Sideband.SBI_SSCCTL6,
         Mask     => SBI_SSCCTL_DISABLE);

      Registers.Write (Registers.PCH_PIXCLK_GATE, PCH_PIXCLK_GATE_UNGATE);
   end Clock_On;

end HW.GFX.GMA.PCH.VGA;
