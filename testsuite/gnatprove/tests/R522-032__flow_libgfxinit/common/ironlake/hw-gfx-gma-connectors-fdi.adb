--
-- Copyright (C) 2016 secunet Security Networks AG
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
with HW.GFX.GMA.PCH.FDI;
with HW.GFX.GMA.Registers;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.Connectors.FDI
is

   PCH_FDI_CHICKEN_B_AND_C             : constant :=      1 * 2 ** 12;

   type TX_CTL_Regs is array (GPU_FDI_Port) of Registers.Registers_Index;
   TX_CTL : constant TX_CTL_Regs :=
     (DIGI_B => Registers.FDI_TX_CTL_A,
      DIGI_C => Registers.FDI_TX_CTL_B,
      DIGI_D => Registers.FDI_TX_CTL_C);

   FDI_TX_CTL_FDI_TX_ENABLE            : constant :=      1 * 2 ** 31;
   FDI_TX_CTL_VP_MASK                  : constant := 16#3f# * 2 ** 22;
   FDI_TX_CTL_PORT_WIDTH_SEL_SHIFT     : constant :=               19;
   FDI_TX_CTL_ENHANCED_FRAMING_ENABLE  : constant :=      1 * 2 ** 18;
   FDI_TX_CTL_FDI_PLL_ENABLE           : constant :=      1 * 2 ** 14;
   FDI_TX_CTL_COMPOSITE_SYNC_SELECT    : constant :=      1 * 2 ** 11;
   FDI_TX_CTL_AUTO_TRAIN_ENABLE        : constant :=      1 * 2 ** 10;
   FDI_TX_CTL_AUTO_TRAIN_DONE          : constant :=      1 * 2 **  1;

   TP_SHIFT : constant := (if Config.CPU <= Sandybridge then 28 else 8);
   FDI_TX_CTL_TRAINING_PATTERN_MASK    : constant := 3 * 2 ** TP_SHIFT;
   FDI_TX_CTL_TRAINING_PATTERN_1       : constant := 0 * 2 ** TP_SHIFT;
   FDI_TX_CTL_TRAINING_PATTERN_2       : constant := 1 * 2 ** TP_SHIFT;
   FDI_TX_CTL_TRAINING_PATTERN_IDLE    : constant := 2 * 2 ** TP_SHIFT;
   FDI_TX_CTL_TRAINING_PATTERN_NORMAL  : constant := 3 * 2 ** TP_SHIFT;

   subtype FDI_TX_CTL_VP_T is Natural range 0 .. 3;
   type Vswing_Preemph_Values is array (FDI_TX_CTL_VP_T) of Word32;
   FDI_TX_CTL_VSWING_PREEMPH : constant Vswing_Preemph_Values :=
     (0 => 16#00# * 2 ** 22,
      1 => 16#3a# * 2 ** 22,
      2 => 16#39# * 2 ** 22,
      3 => 16#38# * 2 ** 22);

   function FDI_TX_CTL_PORT_WIDTH_SEL (Lane_Count : DP_Lane_Count) return Word32
   is
   begin
      return Shift_Left
        (Word32 (Lane_Count_As_Integer (Lane_Count)) - 1,
         FDI_TX_CTL_PORT_WIDTH_SEL_SHIFT);
   end FDI_TX_CTL_PORT_WIDTH_SEL;

   ----------------------------------------------------------------------------

   --
   -- This is usually used with Ivy Bridge.
   --
   procedure Auto_Training
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   with
      Pre => Port_Cfg.Port in GPU_FDI_Port
   is
      PCH_FDI_Port : constant PCH.FDI_Port_Type := PCH_FDIs (Port_Cfg.Port);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- try each preemph/voltage pair twice
      for VP2 in Natural range 0 .. FDI_TX_CTL_VP_T'Last * 2 + 1
      loop
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_VP_MASK or
                           FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_FDI_TX_ENABLE or
                           FDI_TX_CTL_VSWING_PREEMPH (VP2 / 2) or
                           FDI_TX_CTL_AUTO_TRAIN_ENABLE or
                           FDI_TX_CTL_TRAINING_PATTERN_1);
         Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

         PCH.FDI.Auto_Train (PCH_FDI_Port);

         -- read at least twice
         for I in 0 .. 3 loop
            Registers.Is_Set_Mask
              (Register => TX_CTL (Port_Cfg.Port),
               Mask     => FDI_TX_CTL_AUTO_TRAIN_DONE,
               Result   => Success);
            exit when Success or I = 3;
            Time.U_Delay (1);
         end loop;
         exit when Success;

         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_FDI_TX_ENABLE or
                           FDI_TX_CTL_AUTO_TRAIN_ENABLE or
                           FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_1);

         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Rx_Off);
      end loop;

      if Success then
         PCH.FDI.Enable_EC (PCH_FDI_Port);
      else
         Registers.Unset_Mask
           (Register => TX_CTL (Port_Cfg.Port),
            Mask     => FDI_TX_CTL_FDI_PLL_ENABLE);

         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Clock_Off);
      end if;
   end Auto_Training;

   ----------------------------------------------------------------------------

   --
   -- Used with Sandy Bridge (should work with Ivy Bridge too)
   --
   procedure Full_Training
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   with
      Pre => Port_Cfg.Port in GPU_FDI_Port
   is
      PCH_FDI_Port : constant PCH.FDI_Port_Type := PCH_FDIs (Port_Cfg.Port);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- try each preemph/voltage pair twice
      for VP2 in Natural range 0 .. FDI_TX_CTL_VP_T'Last * 2 + 1
      loop
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_VP_MASK or
                           FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_FDI_TX_ENABLE or
                           FDI_TX_CTL_VSWING_PREEMPH (VP2 / 2) or
                           FDI_TX_CTL_TRAINING_PATTERN_1);
         Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

         PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_1, Success);

         if Success then
            Registers.Unset_And_Set_Mask
              (Register    => TX_CTL (Port_Cfg.Port),
               Mask_Unset  => FDI_TX_CTL_TRAINING_PATTERN_MASK,
               Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_2);
            Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

            PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_2, Success);
         end if;
         exit when Success;

         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_FDI_TX_ENABLE or
                           FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_1);

         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Rx_Off);
      end loop;

      if Success then
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_NORMAL);
         Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

         PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_None, Success);
      else
         Registers.Unset_Mask
           (Register => TX_CTL (Port_Cfg.Port),
            Mask     => FDI_TX_CTL_FDI_PLL_ENABLE);

         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Clock_Off);
      end if;
   end Full_Training;

   ----------------------------------------------------------------------------

   --
   -- Used with original Ironlake (Nehalem CPU)
   --
   -- This is close to what Linux' i915 does. A comment in i915_reg.h
   -- states that it uses only the lowest voltage / pre-emphasis levels
   -- which is why we leave them at zero here and don't try different
   -- values.
   --
   -- It's actually not clear from i915's code if the values really are
   -- at zero or if it's just reusing what the Video BIOS set. Some code
   -- in coreboot sets them to zero explicitly.
   --
   procedure Simple_Training
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   with
      Pre => Port_Cfg.Port in GPU_FDI_Port
   is
      PCH_FDI_Port : constant PCH.FDI_Port_Type := PCH_FDIs (Port_Cfg.Port);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => TX_CTL (Port_Cfg.Port),
         Mask_Unset  => FDI_TX_CTL_TRAINING_PATTERN_MASK,
         Mask_Set    => FDI_TX_CTL_FDI_TX_ENABLE or
                        FDI_TX_CTL_TRAINING_PATTERN_1);
      Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

      PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_1, Success);

      if Success then
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_2);
         Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

         PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_2, Success);
      end if;

      if Success then
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_NORMAL);
         Registers.Posting_Read (TX_CTL (Port_Cfg.Port));

         PCH.FDI.Train (PCH_FDI_Port, PCH.FDI.TP_None, Success);
      else
         Registers.Unset_And_Set_Mask
           (Register    => TX_CTL (Port_Cfg.Port),
            Mask_Unset  => FDI_TX_CTL_FDI_TX_ENABLE or
                           FDI_TX_CTL_TRAINING_PATTERN_MASK,
            Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_1);
         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Rx_Off);

         Registers.Unset_Mask
           (Register => TX_CTL (Port_Cfg.Port),
            Mask     => FDI_TX_CTL_FDI_PLL_ENABLE);
         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Clock_Off);
      end if;
   end Simple_Training;

   ----------------------------------------------------------------------------

   procedure Pre_On (Port_Cfg : Port_Config)
   is
      Composite_Sel : constant :=
        (if Config.Has_FDI_Composite_Sel then
            FDI_TX_CTL_COMPOSITE_SYNC_SELECT else 0);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- The PCH_FDI_CHICKEN_B_AND_C bit may not be changed when any of
      -- both ports is active. Bandwidth calculations before calling us
      -- should ensure this.
      if Config.Has_FDI_C then
         if Port_Cfg.Port = DIGI_D or
            (Port_Cfg.Port = DIGI_C and
             Port_Cfg.FDI.Lane_Count <= DP_Lane_Count_2)
         then
            Registers.Set_Mask
              (Register => Registers.PCH_FDI_CHICKEN_B_C,
               Mask     => PCH_FDI_CHICKEN_B_AND_C);
         elsif Port_Cfg.Port = DIGI_C then
            Registers.Unset_Mask
              (Register => Registers.PCH_FDI_CHICKEN_B_C,
               Mask     => PCH_FDI_CHICKEN_B_AND_C);
         end if;
      end if;

      PCH.FDI.Pre_Train (PCH_FDIs (Port_Cfg.Port), Port_Cfg);

      Registers.Write
        (Register => TX_CTL (Port_Cfg.Port),
         Value    => FDI_TX_CTL_PORT_WIDTH_SEL (Port_Cfg.FDI.Lane_Count) or
                     FDI_TX_CTL_ENHANCED_FRAMING_ENABLE or
                     FDI_TX_CTL_FDI_PLL_ENABLE or
                     Composite_Sel or
                     FDI_TX_CTL_TRAINING_PATTERN_1);
      Registers.Posting_Read (TX_CTL (Port_Cfg.Port));
      Time.U_Delay (100);
   end Pre_On;

   ----------------------------------------------------------------------------

   procedure Post_On
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      case Config.FDI_Training is
         when GMA.Simple_Training   => Simple_Training (Port_Cfg, Success);
         when GMA.Full_Training     => Full_Training (Port_Cfg, Success);
         when GMA.Auto_Training     => Auto_Training (Port_Cfg, Success);
      end case;
   end Post_On;

   ----------------------------------------------------------------------------

   procedure Off (Port : GPU_FDI_Port; OT : Off_Type)
   is
      PCH_FDI_Port : constant PCH.FDI_Port_Type := PCH_FDIs (Port);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => TX_CTL (Port),
         Mask_Unset  => FDI_TX_CTL_FDI_TX_ENABLE or
                        FDI_TX_CTL_AUTO_TRAIN_ENABLE or
                        FDI_TX_CTL_TRAINING_PATTERN_MASK,
         Mask_Set    => FDI_TX_CTL_TRAINING_PATTERN_1);

      PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Rx_Off);

      if OT >= Clock_Off then
         Registers.Unset_Mask
           (Register => TX_CTL (Port),
            Mask     => FDI_TX_CTL_FDI_PLL_ENABLE);

         PCH.FDI.Off (PCH_FDI_Port, PCH.FDI.Clock_Off);
      end if;
   end Off;

end HW.GFX.GMA.Connectors.FDI;
