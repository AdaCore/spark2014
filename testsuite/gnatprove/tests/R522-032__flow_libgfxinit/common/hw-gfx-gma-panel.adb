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

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.Panel
with
   Refined_State =>
     (Panel_State =>
        (Delays_US, Power_Cycle_Timer, Power_Up_Timer))
is
   type Delays_Enum is
     (Power_Up_Delay,
      Power_Up_To_BL_On,
      Power_Down_Delay,
      BL_Off_To_Power_Down,
      Power_Cycle_Delay);

   type Panel_Power_Delays is array (Delays_Enum) of Natural;
   Default_EDP_Delays_US : constant Panel_Power_Delays := Panel_Power_Delays'
     (Power_Up_Delay       => 210_000,
      Power_Up_To_BL_On    =>  50_000,
      Power_Down_Delay     => 500_000,
      BL_Off_To_Power_Down =>  50_000,
      Power_Cycle_Delay    => 510_000);

   Delays_US : Panel_Power_Delays;

   ----------------------------------------------------------------------------

   -- And here the mess starts: We have this pretty hardware power sequencer
   -- that should ensure the panel's timing constraints are satisfied. But
   -- (at least on some generations) it doesn't do it's job. On Haswell, it
   -- seems to ignore the Power_Cycle_Delay, so we ensure the delay in soft-
   -- ware. On at least Ivy Bridge and Broadwell Power_Up_Delay is ignored.
   --
   -- If we ever do all delays in software, there are two ways: Either confi-
   -- gure the hardware to zero delays or wait for both the software timeout
   -- and the hardware power sequencer. The latter option would be less error
   -- prone, as the hardware might just don't work as expected.

   Power_Cycle_Timer : Time.T;
   Power_Up_Timer    : Time.T;

   ----------------------------------------------------------------------------

   function Div_Round_Up32 (Num : Natural; Denom : Positive) return Word32 is
     ((Word32 (Num) + Word32 (Denom) - 1) / Word32 (Denom));

   PCH_PP_STATUS_ENABLED               : constant := 16#00_0001# * 2 ** 31;
   PCH_PP_STATUS_REQUIRE_ASSET         : constant := 16#00_0001# * 2 ** 30;
   PCH_PP_STATUS_PWR_SEQ_PROGRESS_MASK : constant := 16#00_0003# * 2 ** 28;
   PCH_PP_STATUS_PWR_SEQ_PROGRESS_NONE : constant := 16#00_0000# * 2 ** 28;
   PCH_PP_STATUS_PWR_SEQ_PROGRESS_UP   : constant := 16#00_0001# * 2 ** 28;
   PCH_PP_STATUS_PWR_SEQ_PROGRESS_DOWN : constant := 16#00_0002# * 2 ** 28;
   PCH_PP_STATUS_PWR_CYC_DELAY_ACTIVE  : constant := 16#00_0001# * 2 ** 27;

   PCH_PP_CONTROL_WRITE_PROTECT_MASK   : constant := 16#00_ffff# * 2 ** 16;
   PCH_PP_CONTROL_WRITE_PROTECT_KEY    : constant := 16#00_abcd# * 2 ** 16;
   PCH_PP_CONTROL_VDD_OVERRIDE         : constant := 16#00_0001# * 2 **  3;
   PCH_PP_CONTROL_BACKLIGHT_ENABLE     : constant := 16#00_0001# * 2 **  2;
   PCH_PP_CONTROL_POWER_DOWN_ON_RESET  : constant := 16#00_0001# * 2 **  1;
   PCH_PP_CONTROL_TARGET_ON            : constant := 16#00_0001# * 2 **  0;

   PCH_PP_ON_DELAYS_PORT_SELECT_MASK   : constant := 16#00_0003# * 2 ** 30;
   PCH_PP_ON_DELAYS_PORT_SELECT_LVDS   : constant := 16#00_0000# * 2 ** 30;
   PCH_PP_ON_DELAYS_PORT_SELECT_DP_A   : constant := 16#00_0001# * 2 ** 30;
   PCH_PP_ON_DELAYS_PORT_SELECT_DP_C   : constant := 16#00_0002# * 2 ** 30;
   PCH_PP_ON_DELAYS_PORT_SELECT_DP_D   : constant := 16#00_0003# * 2 ** 30;
   PCH_PP_ON_DELAYS_PWR_UP_MASK        : constant := 16#00_1fff# * 2 ** 16;
   PCH_PP_ON_DELAYS_PWR_UP_BL_ON_MASK  : constant := 16#00_1fff# * 2 **  0;

   type PP_Regs is record
      STATUS     : Registers.Registers_Index;
      CONTROL    : Registers.Registers_Index;
      ON_DELAYS  : Registers.Registers_Index;
      OFF_DELAYS : Registers.Registers_Index;
      DIVISOR    : Registers.Registers_Index;
   end record;

   Panel_PP_Regs : constant PP_Regs := (if Config.Has_PCH_Panel_Power then
     (STATUS     => Registers.PCH_PP_STATUS,
      CONTROL    => Registers.PCH_PP_CONTROL,
      ON_DELAYS  => Registers.PCH_PP_ON_DELAYS,
      OFF_DELAYS => Registers.PCH_PP_OFF_DELAYS,
      DIVISOR    => Registers.PCH_PP_DIVISOR)
   else
     (STATUS     => Registers.GMCH_PP_STATUS,
      CONTROL    => Registers.GMCH_PP_CONTROL,
      ON_DELAYS  => Registers.GMCH_PP_ON_DELAYS,
      OFF_DELAYS => Registers.GMCH_PP_OFF_DELAYS,
      DIVISOR    => Registers.GMCH_PP_DIVISOR));

   function PCH_PP_ON_DELAYS_PWR_UP (US : Natural) return Word32 is
   begin
      return Shift_Left (Div_Round_Up32 (US, 100), 16);
   end PCH_PP_ON_DELAYS_PWR_UP;
   function PCH_PP_ON_DELAYS_PWR_UP_BL_ON (US : Natural) return Word32 is
   begin
      return Div_Round_Up32 (US, 100);
   end PCH_PP_ON_DELAYS_PWR_UP_BL_ON;

   PCH_PP_OFF_DELAYS_PWR_DOWN_MASK        : constant := 16#1fff# * 2 ** 16;
   PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN_MASK : constant := 16#1fff# * 2 **  0;
   function PCH_PP_OFF_DELAYS_PWR_DOWN (US : Natural) return Word32 is
   begin
      return Shift_Left (Div_Round_Up32 (US, 100), 16);
   end PCH_PP_OFF_DELAYS_PWR_DOWN;
   function PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN (US : Natural) return Word32 is
   begin
      return Div_Round_Up32 (US, 100);
   end PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN;

   PCH_PP_DIVISOR_REF_DIVIDER_MASK     : constant := 16#ff_ffff# * 2 **  8;
   PCH_PP_DIVISOR_PWR_CYC_DELAY_MASK   : constant := 16#00_001f# * 2 **  0;
   function PCH_PP_DIVISOR_PWR_CYC_DELAY (US : Natural) return Word32 is
   begin
      return Div_Round_Up32 (US, 100_000) + 1;
   end PCH_PP_DIVISOR_PWR_CYC_DELAY;

   CPU_BLC_PWM_CTL_ENABLE              : constant := 16#00_0001# * 2 ** 31;
   CPU_BLC_PWM_CTL_PIPE_SELECT_MASK    : constant := 16#00_0003# * 2 ** 29;
   CPU_BLC_PWM_CTL_PIPE_SELECT_PIPE_A  : constant := 16#00_0000# * 2 ** 29;
   CPU_BLC_PWM_CTL_PIPE_SELECT_PIPE_B  : constant := 16#00_0001# * 2 ** 29;
   CPU_BLC_PWM_CTL_PIPE_SELECT_PIPE_C  : constant := 16#00_0002# * 2 ** 29;

   CPU_BLC_PWM_DATA_BL_DUTY_CYC_MASK   : constant := 16#00_ffff# * 2 **  0;

   PCH_BLC_PWM_CTL1_ENABLE             : constant := 16#00_0001# * 2 ** 31;
   PCH_BLC_PWM_CTL1_BL_POLARITY_MASK   : constant := 16#00_0001# * 2 ** 29;
   PCH_BLC_PWM_CTL1_PHASE_IN_INTR_STAT : constant := 16#00_0001# * 2 ** 26;
   PCH_BLC_PWM_CTL1_PHASE_IN_ENABLE    : constant := 16#00_0001# * 2 ** 25;
   PCH_BLC_PWM_CTL1_PHASE_IN_INTR_EN   : constant := 16#00_0001# * 2 ** 24;
   PCH_BLC_PWM_CTL1_PHASE_IN_TIME_BASE : constant := 16#00_00ff# * 2 ** 16;
   PCH_BLC_PWM_CTL1_PHASE_IN_COUNT     : constant := 16#00_00ff# * 2 **  8;
   PCH_BLC_PWM_CTL1_PHASE_IN_INCREMENT : constant := 16#00_00ff# * 2 **  0;

   PCH_BLC_PWM_CTL2_BL_MOD_FREQ_MASK   : constant := 16#00_ffff# * 2 ** 16;
   PCH_BLC_PWM_CTL2_BL_DUTY_CYC_MASK   : constant := 16#00_ffff# * 2 **  0;

   ----------------------------------------------------------------------------

   procedure Static_Init
   with
      Refined_Global =>
        (Output => (Power_Cycle_Timer, Power_Up_Timer, Delays_US),
         Input  => (Time.State))
   is
   begin
      Power_Cycle_Timer := Time.Now;
      Power_Up_Timer    := Power_Cycle_Timer;

      Delays_US := Default_EDP_Delays_US;
   end Static_Init;

   ----------------------------------------------------------------------------

   procedure Check_PP_Delays
     (Delays   : in out Panel_Power_Delays;
      Override : in out Boolean) is
   begin
      for D in Delays_Enum loop
         if Delays (D) = 0 then
            Delays (D) := Default_EDP_Delays_US (D);
            Override := True;
         end if;
      end loop;
   end Check_PP_Delays;

   procedure Setup_PP_Sequencer (Default_Delays : Boolean := False)
   is
      Power_Delay, Port_Select : Word32;

      Override_Delays : Boolean := False;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Static_Init;

      if Default_Delays then
         Override_Delays := True;
      else
         Registers.Read (Panel_PP_Regs.ON_DELAYS, Power_Delay);
         Delays_US (Power_Up_Delay) := 100 * Natural
           (Shift_Right (Power_Delay and PCH_PP_ON_DELAYS_PWR_UP_MASK, 16));
         Delays_US (Power_Up_To_BL_On) := 100 * Natural
           (Power_Delay and PCH_PP_ON_DELAYS_PWR_UP_BL_ON_MASK);

         Registers.Read (Panel_PP_Regs.OFF_DELAYS, Power_Delay);
         Delays_US (Power_Down_Delay) := 100 * Natural
           (Shift_Right (Power_Delay and PCH_PP_OFF_DELAYS_PWR_DOWN_MASK, 16));
         Delays_US (BL_Off_To_Power_Down) := 100 * Natural
           (Power_Delay and PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN_MASK);

         Registers.Read (Panel_PP_Regs.DIVISOR, Power_Delay);
         if (Power_Delay and PCH_PP_DIVISOR_PWR_CYC_DELAY_MASK) > 1 then
            Delays_US (Power_Cycle_Delay) := 100_000 * (Natural
              (Power_Delay and PCH_PP_DIVISOR_PWR_CYC_DELAY_MASK) - 1);
         end if;

         Check_PP_Delays (Delays_US, Override_Delays);
      end if;

      if Override_Delays then
         if Config.Has_PP_Port_Select then
            if Config.Internal_Is_EDP then
               Port_Select := PCH_PP_ON_DELAYS_PORT_SELECT_DP_A;
            else
               Port_Select := PCH_PP_ON_DELAYS_PORT_SELECT_LVDS;
            end if;
         else
            Port_Select := 0;
         end if;

         -- Force power-up to backlight-on delay to 100us as recommended by PRM.
         Registers.Unset_And_Set_Mask
           (Register    => Panel_PP_Regs.ON_DELAYS,
            Mask_Unset  => PCH_PP_ON_DELAYS_PORT_SELECT_MASK or
                           PCH_PP_ON_DELAYS_PWR_UP_MASK or
                           PCH_PP_ON_DELAYS_PWR_UP_BL_ON_MASK,
            Mask_Set    => Port_Select or
                           PCH_PP_ON_DELAYS_PWR_UP (Delays_US (Power_Up_Delay))
                           or PCH_PP_ON_DELAYS_PWR_UP_BL_ON (100));

         Registers.Unset_And_Set_Mask
           (Register    => Panel_PP_Regs.OFF_DELAYS,
            Mask_Unset  => PCH_PP_OFF_DELAYS_PWR_DOWN_MASK or
                           PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN_MASK,
            Mask_Set    => PCH_PP_OFF_DELAYS_PWR_DOWN
                             (Delays_US (Power_Down_Delay)) or
                           PCH_PP_OFF_DELAYS_BL_OFF_PWR_DOWN
                             (Delays_US (BL_Off_To_Power_Down)));

         Registers.Unset_And_Set_Mask
           (Register    => Panel_PP_Regs.DIVISOR,
            Mask_Unset  => PCH_PP_DIVISOR_PWR_CYC_DELAY_MASK,
            Mask_Set    => PCH_PP_DIVISOR_PWR_CYC_DELAY
                             (Delays_US (Power_Cycle_Delay)));
      end if;

      if Config.Has_PP_Write_Protection then
         Registers.Unset_And_Set_Mask
           (Register    => Panel_PP_Regs.CONTROL,
            Mask_Unset  => PCH_PP_CONTROL_WRITE_PROTECT_MASK,
            Mask_Set    => PCH_PP_CONTROL_WRITE_PROTECT_KEY or
                           PCH_PP_CONTROL_POWER_DOWN_ON_RESET);
      else
         Registers.Set_Mask
           (Register => Panel_PP_Regs.CONTROL,
            Mask     => PCH_PP_CONTROL_POWER_DOWN_ON_RESET);
      end if;
   end Setup_PP_Sequencer;

   ----------------------------------------------------------------------------

   procedure VDD_Override is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      -- Yeah, We could do, what we are supposed to do here. But OTOH, we
      -- are should wait for the full Power Up Delay, which we would have
      -- to do later again. And just powering on the display seems to work
      -- too. Also this function vanished on newer hardware.
      On;
   end VDD_Override;

   procedure On (Wait : Boolean := True)
   is
      Was_On : Boolean;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Is_Set_Mask (Panel_PP_Regs.CONTROL, PCH_PP_CONTROL_TARGET_ON, Was_On);
      if not Was_On then
         Time.Delay_Until (Power_Cycle_Timer);
      end if;

      Registers.Set_Mask (Panel_PP_Regs.CONTROL, PCH_PP_CONTROL_TARGET_ON);
      if not Was_On then
         Power_Up_Timer := Time.US_From_Now (Delays_US (Power_Up_Delay));
      end if;
      if Wait then
         Wait_On;
      end if;
   end On;

   procedure Wait_On is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Time.Delay_Until (Power_Up_Timer);
      Registers.Wait_Unset_Mask
        (Register => Panel_PP_Regs.STATUS,
         Mask     => PCH_PP_STATUS_PWR_SEQ_PROGRESS_MASK,
         TOut_MS  => 300);

      Registers.Unset_Mask (Panel_PP_Regs.CONTROL, PCH_PP_CONTROL_VDD_OVERRIDE);
   end Wait_On;

   procedure Off
   is
      Was_On : Boolean;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Is_Set_Mask (Panel_PP_Regs.CONTROL, PCH_PP_CONTROL_TARGET_ON, Was_On);
      Registers.Unset_Mask
        (Register => Panel_PP_Regs.CONTROL,
         Mask     => PCH_PP_CONTROL_TARGET_ON or
                     PCH_PP_CONTROL_VDD_OVERRIDE);
      if Was_On then
         Time.U_Delay (Delays_US (Power_Down_Delay));
      end if;
      Registers.Wait_Unset_Mask
        (Register => Panel_PP_Regs.STATUS,
         Mask     => PCH_PP_STATUS_PWR_SEQ_PROGRESS_MASK,
         TOut_MS  => 600);
      if Was_On then
         Power_Cycle_Timer := Time.US_From_Now (Delays_US (Power_Cycle_Delay));
      end if;
   end Off;

   ----------------------------------------------------------------------------

   procedure Backlight_On is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Set_Mask
         (Register   => Panel_PP_Regs.CONTROL,
          Mask       => PCH_PP_CONTROL_BACKLIGHT_ENABLE);
   end Backlight_On;

   procedure Backlight_Off is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_Mask
        (Register   => Panel_PP_Regs.CONTROL,
         Mask       => PCH_PP_CONTROL_BACKLIGHT_ENABLE);
   end Backlight_Off;

   procedure Set_Backlight (Level : Word16) is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => Registers.BLC_PWM_CPU_CTL,
         Mask_Unset  => CPU_BLC_PWM_DATA_BL_DUTY_CYC_MASK,
         Mask_Set    => Word32 (Level));
   end Set_Backlight;

   procedure Get_Max_Backlight (Level : out Word16)
   is
      Reg : Word32;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Read (Registers.BLC_PWM_PCH_CTL2, Reg);
      Level := Word16
        (Shift_Right (Reg and PCH_BLC_PWM_CTL2_BL_MOD_FREQ_MASK, 16));
   end Get_Max_Backlight;

end HW.GFX.GMA.Panel;
