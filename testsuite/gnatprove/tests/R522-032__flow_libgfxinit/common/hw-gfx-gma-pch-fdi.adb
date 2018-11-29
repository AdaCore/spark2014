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

with HW.Time;
with HW.GFX.GMA.Config;
with HW.GFX.GMA.Registers;

package body HW.GFX.GMA.PCH.FDI is

   FDI_RX_CTL_FDI_RX_ENABLE               : constant := 1 * 2 ** 31;
   FDI_RX_CTL_FS_ERROR_CORRECTION_ENABLE  : constant := 1 * 2 ** 27;
   FDI_RX_CTL_FE_ERROR_CORRECTION_ENABLE  : constant := 1 * 2 ** 26;
   FDI_RX_CTL_PORT_WIDTH_SEL_SHIFT        : constant :=          19;
   FDI_RX_CTL_FDI_PLL_ENABLE              : constant := 1 * 2 ** 13;
   FDI_RX_CTL_COMPOSITE_SYNC_SELECT       : constant := 1 * 2 ** 11;
   FDI_RX_CTL_FDI_AUTO_TRAIN              : constant := 1 * 2 ** 10;
   FDI_RX_CTL_ENHANCED_FRAMING_ENABLE     : constant := 1 * 2 **  6;
   FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_MASK   : constant := 1 * 2 **  4;
   FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_RAWCLK : constant := 0 * 2 **  4;
   FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_PCDCLK : constant := 1 * 2 **  4;

   TP_SHIFT : constant := (if Config.CPU = Ironlake then 28 else 8);
   FDI_RX_CTL_TRAINING_PATTERN_MASK       : constant := 3 * 2 ** TP_SHIFT;

   type TP_Array is array (Training_Pattern) of Word32;
   FDI_RX_CTL_TRAINING_PATTERN : constant TP_Array :=
     (TP_1     => 0 * 2 ** TP_SHIFT,
      TP_2     => 1 * 2 ** TP_SHIFT,
      TP_Idle  => 2 * 2 ** TP_SHIFT,
      TP_None  => 3 * 2 ** TP_SHIFT);

   function FDI_RX_CTL_PORT_WIDTH_SEL (Lane_Count : DP_Lane_Count) return Word32
   is
   begin
      return Shift_Left
        (Word32 (Lane_Count_As_Integer (Lane_Count)) - 1,
         FDI_RX_CTL_PORT_WIDTH_SEL_SHIFT);
   end FDI_RX_CTL_PORT_WIDTH_SEL;

   function FDI_RX_CTL_BPC (BPC : BPC_Type) return Word32
   with Pre => True
   is
   begin
      return
        (case BPC is
            when      6 => 2 * 2 ** 16,
            when     10 => 1 * 2 ** 16,
            when     12 => 3 * 2 ** 16,
            when others => 0 * 2 ** 16);
   end FDI_RX_CTL_BPC;

   FDI_RX_MISC_FDI_RX_PWRDN_LANE1_SHIFT   : constant :=               26;
   FDI_RX_MISC_FDI_RX_PWRDN_LANE1_MASK    : constant :=      3 * 2 ** 26;
   FDI_RX_MISC_FDI_RX_PWRDN_LANE0_SHIFT   : constant :=               24;
   FDI_RX_MISC_FDI_RX_PWRDN_LANE0_MASK    : constant :=      3 * 2 ** 24;
   FDI_RX_MISC_TP1_TO_TP2_TIME_48         : constant :=      2 * 2 ** 20;
   FDI_RX_MISC_FDI_DELAY_90               : constant := 16#90# * 2 **  0;

   function FDI_RX_MISC_FDI_RX_PWRDN_LANE1 (Value : Word32) return Word32
   with Pre => True
   is
   begin
      return Shift_Left (Value, FDI_RX_MISC_FDI_RX_PWRDN_LANE1_SHIFT);
   end FDI_RX_MISC_FDI_RX_PWRDN_LANE1;

   function FDI_RX_MISC_FDI_RX_PWRDN_LANE0 (Value : Word32) return Word32
   with Pre => True
   is
   begin
      return Shift_Left (Value, FDI_RX_MISC_FDI_RX_PWRDN_LANE0_SHIFT);
   end FDI_RX_MISC_FDI_RX_PWRDN_LANE0;

   FDI_RX_TUSIZE_SHIFT                    : constant :=          25;

   function FDI_RX_TUSIZE (Value : Word32) return Word32 is
   begin
      return Shift_Left (Value - 1, FDI_RX_TUSIZE_SHIFT);
   end FDI_RX_TUSIZE;

   FDI_RX_INTERLANE_ALIGNMENT             : constant := 1 * 2 ** 10;
   FDI_RX_SYMBOL_LOCK                     : constant := 1 * 2 **  9;
   FDI_RX_BIT_LOCK                        : constant := 1 * 2 **  8;

   ----------------------------------------------------------------------------

   type FDI_Registers is record
      RX_CTL      : Registers.Registers_Index;
      RX_MISC     : Registers.Registers_Index;
      RX_TUSIZE   : Registers.Registers_Index;
      RX_IMR      : Registers.Registers_Index;
      RX_IIR      : Registers.Registers_Index;
   end record;
   type FDI_Registers_Array is array (PCH.FDI_Port_Type) of FDI_Registers;
   FDI_Regs : constant FDI_Registers_Array := FDI_Registers_Array'
     (PCH.FDI_A => FDI_Registers'
        (RX_CTL      => Registers.FDI_RXA_CTL,
         RX_MISC     => Registers.FDI_RX_MISC_A,
         RX_TUSIZE   => Registers.FDI_RXA_TUSIZE1,
         RX_IMR      => Registers.FDI_RXA_IMR,
         RX_IIR      => Registers.FDI_RXA_IIR),
      PCH.FDI_B => FDI_Registers'
        (RX_CTL      => Registers.FDI_RXB_CTL,
         RX_MISC     => Registers.FDI_RX_MISC_B,
         RX_TUSIZE   => Registers.FDI_RXB_TUSIZE1,
         RX_IMR      => Registers.FDI_RXB_IMR,
         RX_IIR      => Registers.FDI_RXB_IIR),
      PCH.FDI_C => FDI_Registers'
        (RX_CTL      => Registers.FDI_RXC_CTL,
         RX_MISC     => Registers.FDI_RX_MISC_C,
         RX_TUSIZE   => Registers.FDI_RXC_TUSIZE1,
         RX_IMR      => Registers.FDI_RXC_IMR,
         RX_IIR      => Registers.FDI_RXC_IIR));

   ----------------------------------------------------------------------------

   procedure Pre_Train (Port : PCH.FDI_Port_Type; Port_Cfg : Port_Config)
   is
      Power_Down_Lane_Bits : constant Word32 :=
        (if Config.Has_FDI_RX_Power_Down then
            FDI_RX_MISC_FDI_RX_PWRDN_LANE1 (2) or
            FDI_RX_MISC_FDI_RX_PWRDN_LANE0 (2)
         else 0);
      RX_CTL_Settings : constant Word32 :=
         FDI_RX_CTL_PORT_WIDTH_SEL (Port_Cfg.FDI.Lane_Count) or
        (if Config.Has_FDI_BPC then
            FDI_RX_CTL_BPC (Port_Cfg.Mode.BPC) else 0) or
        (if Config.Has_FDI_Composite_Sel then
            FDI_RX_CTL_COMPOSITE_SYNC_SELECT else 0) or
        (if Port_Cfg.FDI.Enhanced_Framing then
            FDI_RX_CTL_ENHANCED_FRAMING_ENABLE else 0);
   begin
      -- TODO: HSW: check DISPIO_CR_TX_BMU_CR4, seems Linux doesn't know it

      Registers.Write
        (Register => FDI_Regs (Port).RX_MISC,
         Value    => Power_Down_Lane_Bits or
                     FDI_RX_MISC_TP1_TO_TP2_TIME_48 or
                     FDI_RX_MISC_FDI_DELAY_90);

      Registers.Write
        (Register => FDI_Regs (Port).RX_TUSIZE,
         Value    => FDI_RX_TUSIZE (64));

      Registers.Unset_Mask
        (Register => FDI_Regs (Port).RX_IMR,
         Mask     => FDI_RX_INTERLANE_ALIGNMENT or
                     FDI_RX_SYMBOL_LOCK or
                     FDI_RX_BIT_LOCK);
      Registers.Posting_Read (FDI_Regs (Port).RX_IMR);
      -- clear stale lock bits
      Registers.Write
        (Register => FDI_Regs (Port).RX_IIR,
         Value    => FDI_RX_INTERLANE_ALIGNMENT or
                     FDI_RX_SYMBOL_LOCK or
                     FDI_RX_BIT_LOCK);

      Registers.Write
        (Register => FDI_Regs (Port).RX_CTL,
         Value    => FDI_RX_CTL_FDI_PLL_ENABLE or
                     RX_CTL_Settings);
      Registers.Posting_Read (FDI_Regs (Port).RX_CTL);
      Time.U_Delay (220);

      Registers.Set_Mask
        (Register => FDI_Regs (Port).RX_CTL,
         Mask     => FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_PCDCLK);
   end Pre_Train;

   procedure Train
     (Port     : in     PCH.FDI_Port_Type;
      TP       : in     Training_Pattern;
      Success  :    out Boolean)
   is
      Lock_Bit : constant Word32 :=
        (if TP = TP_1 then FDI_RX_BIT_LOCK else FDI_RX_SYMBOL_LOCK);

      procedure Check_Lock (Lock_Bit : Word32)
      is
      begin
         for I in 1 .. 5 loop
            Registers.Is_Set_Mask
              (Register => FDI_Regs (Port).RX_IIR,
               Mask     => Lock_Bit,
               Result   => Success);
            if Success then
               -- clear the lock bit
               Registers.Write
                 (Register => FDI_Regs (Port).RX_IIR,
                  Value    => Lock_Bit);
            end if;
            exit when Success;
            Time.U_Delay (1);
         end loop;
      end Check_Lock;
   begin
      Registers.Unset_And_Set_Mask
        (Register    => FDI_Regs (Port).RX_CTL,
         Mask_Unset  => FDI_RX_CTL_TRAINING_PATTERN_MASK,
         Mask_Set    => FDI_RX_CTL_FDI_RX_ENABLE or
                        FDI_RX_CTL_TRAINING_PATTERN (TP));
      Registers.Posting_Read (FDI_Regs (Port).RX_CTL);

      if TP <= TP_2 then
         Time.U_Delay (1);
         if TP = TP_1 then
            Check_Lock (FDI_RX_BIT_LOCK);
         else
            Check_Lock (FDI_RX_SYMBOL_LOCK);
            if Success then
               Check_Lock (FDI_RX_INTERLANE_ALIGNMENT);
            end if;
         end if;
      else
         Time.U_Delay (31);
         Success := True;
      end if;
   end Train;

   procedure Auto_Train (Port : PCH.FDI_Port_Type)
   is
   begin
      Registers.Set_Mask
        (Register => FDI_Regs (Port).RX_CTL,
         Mask     => FDI_RX_CTL_FDI_RX_ENABLE or
                     FDI_RX_CTL_FDI_AUTO_TRAIN);
      Registers.Posting_Read (FDI_Regs (Port).RX_CTL);

      if Config.Has_FDI_RX_Power_Down then
         Time.U_Delay (30);
         Registers.Unset_And_Set_Mask
           (Register    => FDI_Regs (Port).RX_MISC,
            Mask_Unset  => FDI_RX_MISC_FDI_RX_PWRDN_LANE1_MASK or
                           FDI_RX_MISC_FDI_RX_PWRDN_LANE0_MASK,
            Mask_Set    => FDI_RX_MISC_FDI_RX_PWRDN_LANE1 (0) or
                           FDI_RX_MISC_FDI_RX_PWRDN_LANE0 (0));
         Registers.Posting_Read (FDI_Regs (Port).RX_MISC);
      end if;

      Time.U_Delay (5);
   end Auto_Train;

   procedure Enable_EC (Port : PCH.FDI_Port_Type)
   is
   begin
      Registers.Set_Mask
        (Register => FDI_Regs (Port).RX_CTL,
         Mask     => FDI_RX_CTL_FS_ERROR_CORRECTION_ENABLE or
                     FDI_RX_CTL_FE_ERROR_CORRECTION_ENABLE);
   end Enable_EC;

   ----------------------------------------------------------------------------

   procedure Off (Port : PCH.FDI_Port_Type; OT : Off_Type)
   is
   begin
      Registers.Unset_Mask
        (Register => FDI_Regs (Port).RX_CTL,
         Mask     => FDI_RX_CTL_FDI_RX_ENABLE or
                     FDI_RX_CTL_FDI_AUTO_TRAIN);

      if Config.Has_FDI_RX_Power_Down and then OT >= Lanes_Off then
         Registers.Unset_And_Set_Mask
           (Register    => FDI_Regs (Port).RX_MISC,
            Mask_Unset  => FDI_RX_MISC_FDI_RX_PWRDN_LANE1_MASK or
                           FDI_RX_MISC_FDI_RX_PWRDN_LANE0_MASK,
            Mask_Set    => FDI_RX_MISC_FDI_RX_PWRDN_LANE1 (2) or
                           FDI_RX_MISC_FDI_RX_PWRDN_LANE0 (2));
         Registers.Posting_Read (FDI_Regs (Port).RX_MISC);
      end if;

      if OT >= Clock_Off then
         Registers.Unset_And_Set_Mask
           (Register    => FDI_Regs (Port).RX_CTL,
            Mask_Unset  => FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_MASK,
            Mask_Set    => FDI_RX_CTL_RAWCLK_TO_PCDCLK_SEL_RAWCLK);

         Registers.Unset_Mask
           (Register    => FDI_Regs (Port).RX_CTL,
            Mask        => FDI_RX_CTL_FDI_PLL_ENABLE);
      end if;
   end Off;

end HW.GFX.GMA.PCH.FDI;
