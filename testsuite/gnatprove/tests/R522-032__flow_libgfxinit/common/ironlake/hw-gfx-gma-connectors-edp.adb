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
with HW.GFX.DP_Training;
with HW.GFX.GMA.DP_Info;
with HW.GFX.GMA.DP_Aux_Ch;
with HW.GFX.GMA.Registers;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.Connectors.EDP
is

   DP_CTL_DISPLAYPORT_ENABLE        : constant :=  1 * 2 ** 31;
   DP_CTL_VSWING_EMPH_SET_MASK      : constant := 63 * 2 ** 22;
   DP_CTL_PORT_WIDTH_MASK           : constant :=  7 * 2 ** 19;
   DP_CTL_PORT_WIDTH_1_LANE         : constant :=  0 * 2 ** 19;
   DP_CTL_PORT_WIDTH_2_LANES        : constant :=  1 * 2 ** 19;
   DP_CTL_PORT_WIDTH_4_LANES        : constant :=  3 * 2 ** 19;
   DP_CTL_ENHANCED_FRAMING_ENABLE   : constant :=  1 * 2 ** 18;
   DP_CTL_PLL_FREQUENCY_MASK        : constant :=  3 * 2 ** 16;
   DP_CTL_PLL_FREQUENCY_270         : constant :=  0 * 2 ** 16;
   DP_CTL_PLL_FREQUENCY_162         : constant :=  1 * 2 ** 16;
   DP_CTL_PORT_REVERSAL             : constant :=  1 * 2 ** 15;
   DP_CTL_PLL_ENABLE                : constant :=  1 * 2 ** 14;
   DP_CTL_LINK_TRAIN_MASK           : constant :=  3 * 2 **  8;
   DP_CTL_LINK_TRAIN_PAT1           : constant :=  0 * 2 **  8;
   DP_CTL_LINK_TRAIN_PAT2           : constant :=  1 * 2 **  8;
   DP_CTL_LINK_TRAIN_IDLE           : constant :=  2 * 2 **  8;
   DP_CTL_LINK_TRAIN_NORMAL         : constant :=  3 * 2 **  8;
   DP_CTL_ALT_SCRAMBLER_RESET       : constant :=  1 * 2 **  6;
   DP_CTL_VSYNC_ACTIVE_HIGH         : constant :=  1 * 2 **  4;
   DP_CTL_HSYNC_ACTIVE_HIGH         : constant :=  1 * 2 **  3;
   DP_CTL_PORT_DETECT               : constant :=  1 * 2 **  2;

   type Pipe_Value_Array is array (Pipe_Index) of Word32;
   DP_CTL_PIPE_SELECT : constant Pipe_Value_Array :=
     (Primary     => 0 * 2 ** 29,
      Secondary   => 1 * 2 ** 29,
      Tertiary    => 2 * 2 ** 29);

   -- TODO? Values are for Ivy Bridge only
   DP_CTL_VSWING_0_EMPH_0 : constant := 1 * 2 ** 27 + 1 * 2 ** 24 + 0 * 2 ** 22;
   DP_CTL_VSWING_0_EMPH_1 : constant := 1 * 2 ** 27 + 2 * 2 ** 24 + 2 * 2 ** 22;
   DP_CTL_VSWING_0_EMPH_2 : constant := 1 * 2 ** 27 + 3 * 2 ** 24 + 3 * 2 ** 22;
   DP_CTL_VSWING_1_EMPH_0 : constant := 1 * 2 ** 27 + 4 * 2 ** 24 + 0 * 2 ** 22;
   DP_CTL_VSWING_1_EMPH_1 : constant := 1 * 2 ** 27 + 5 * 2 ** 24 + 2 * 2 ** 22;
   DP_CTL_VSWING_2_EMPH_0 : constant := 1 * 2 ** 27 + 6 * 2 ** 24 + 0 * 2 ** 22;
   DP_CTL_VSWING_2_EMPH_1 : constant := 1 * 2 ** 27 + 7 * 2 ** 24 + 2 * 2 ** 22;

   type DP_CTL_PORT_WIDTH_T is array (DP_Lane_Count) of Word32;
   DP_CTL_PORT_WIDTH : constant DP_CTL_PORT_WIDTH_T :=
      DP_CTL_PORT_WIDTH_T'
     (DP_Lane_Count_1 => DP_CTL_PORT_WIDTH_1_LANE,
      DP_Lane_Count_2 => DP_CTL_PORT_WIDTH_2_LANES,
      DP_Lane_Count_4 => DP_CTL_PORT_WIDTH_4_LANES);

   type DP_CTL_LINK_TRAIN_Array is array (DP_Info.Training_Pattern) of Word32;
   DP_CTL_LINK_TRAIN : constant DP_CTL_LINK_TRAIN_Array :=
      DP_CTL_LINK_TRAIN_Array'
     (DP_Info.TP_1      => DP_CTL_LINK_TRAIN_PAT1,
      DP_Info.TP_2      => DP_CTL_LINK_TRAIN_PAT2,
      DP_Info.TP_3      => DP_CTL_LINK_TRAIN_PAT2,
      DP_Info.TP_Idle   => DP_CTL_LINK_TRAIN_IDLE,
      DP_Info.TP_None   => DP_CTL_LINK_TRAIN_NORMAL);

   ----------------------------------------------------------------------------

   procedure Pre_Training is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => Registers.DP_CTL_A,
         Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
         Mask_Set    => DP_CTL_LINK_TRAIN (DP_Info.TP_1) or
                        DP_CTL_DISPLAYPORT_ENABLE);
   end Pre_Training;

   ----------------------------------------------------------------------------

   pragma Warnings (GNATprove, Off, "unused variable ""Port""",
                    Reason => "Needed for a common interface");
   function Max_V_Swing
     (Port : Digital_Port)
      return DP_Info.DP_Voltage_Swing
   is
   begin
      return DP_Info.VS_Level_2;
   end Max_V_Swing;

   function Max_Pre_Emph
     (Port        : Digital_Port;
      Train_Set   : DP_Info.Train_Set)
      return DP_Info.DP_Pre_Emph
   is
   begin
      return
        (case Train_Set.Voltage_Swing is
            when DP_Info.VS_Level_0 => DP_Info.Emph_Level_2,
            when DP_Info.VS_Level_1 |
                 DP_Info.VS_Level_2 => DP_Info.Emph_Level_1,
            when others             => DP_Info.Emph_Level_0);
   end Max_Pre_Emph;

   ----------------------------------------------------------------------------

   pragma Warnings (GNATprove, Off, "unused variable ""Link""",
                    Reason => "Needed for a common interface");
   procedure Set_Training_Pattern
     (Port     : Digital_Port;
      Link     : DP_Link;
      Pattern  : DP_Info.Training_Pattern)
   is
      use type DP_Info.Training_Pattern;
   begin
      if Pattern < DP_Info.TP_Idle then
         Registers.Unset_And_Set_Mask
           (Register    => Registers.DP_CTL_A,
            Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
            Mask_Set    => DP_CTL_LINK_TRAIN (Pattern));
      else
         -- send at least 5 idle patterns
         Registers.Unset_And_Set_Mask
           (Register    => Registers.DP_CTL_A,
            Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
            Mask_Set    => DP_CTL_LINK_TRAIN (DP_Info.TP_Idle));

         -- we switch to normal frame delivery later in Post_On procedure
      end if;
   end Set_Training_Pattern;

   procedure Set_Signal_Levels
     (Port        : Digital_Port;
      Link        : DP_Link;
      Train_Set   : DP_Info.Train_Set)
   is
      VSwing_Emph : Word32;
   begin
      VSwing_Emph :=
        (case Train_Set.Voltage_Swing is
            when DP_Info.VS_Level_0 =>
              (case Train_Set.Pre_Emph is
                  when DP_Info.Emph_Level_0  => DP_CTL_VSWING_0_EMPH_0,
                  when DP_Info.Emph_Level_1  => DP_CTL_VSWING_0_EMPH_1,
                  when DP_Info.Emph_Level_2  => DP_CTL_VSWING_0_EMPH_2,
                  when others                => DP_CTL_VSWING_0_EMPH_0),
            when DP_Info.VS_Level_1 =>
              (case Train_Set.Pre_Emph is
                  when DP_Info.Emph_Level_0  => DP_CTL_VSWING_1_EMPH_0,
                  when DP_Info.Emph_Level_1  => DP_CTL_VSWING_1_EMPH_1,
                  when others                => DP_CTL_VSWING_1_EMPH_0),
            when DP_Info.VS_Level_2 =>
              (case Train_Set.Pre_Emph is
                  when DP_Info.Emph_Level_0  => DP_CTL_VSWING_2_EMPH_0,
                  when DP_Info.Emph_Level_1  => DP_CTL_VSWING_2_EMPH_1,
                  when others                => DP_CTL_VSWING_2_EMPH_0),
            when others                      => DP_CTL_VSWING_0_EMPH_0);

      Registers.Unset_And_Set_Mask
        (Register    => Registers.DP_CTL_A,
         Mask_Unset  => DP_CTL_VSWING_EMPH_SET_MASK,
         Mask_Set    => VSwing_Emph);
   end Set_Signal_Levels;
   pragma Warnings (GNATprove, On, "unused variable ""Port""");
   pragma Warnings (GNATprove, On, "unused variable ""Link""");

   ----------------------------------------------------------------------------

   procedure Pre_On (Pipe : Pipe_Index; Port_Cfg : Port_Config)
   is
      DP_CTL_Set : Word32;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      DP_CTL_Set :=
         DP_CTL_PIPE_SELECT (Pipe) or
         DP_CTL_PORT_WIDTH (Port_Cfg.DP.Lane_Count);

      if Port_Cfg.DP.Enhanced_Framing then
         DP_CTL_Set := DP_CTL_Set or DP_CTL_ENHANCED_FRAMING_ENABLE;
      end if;

      case Port_Cfg.DP.Bandwidth is
         when DP_Bandwidth_1_62 =>
            DP_CTL_Set := DP_CTL_Set or DP_CTL_PLL_FREQUENCY_162;
         when DP_Bandwidth_2_7 =>
            DP_CTL_Set := DP_CTL_Set or DP_CTL_PLL_FREQUENCY_270;
         when others =>
            null;
      end case;

      if Port_Cfg.Mode.V_Sync_Active_High then
         DP_CTL_Set := DP_CTL_Set or DP_CTL_VSYNC_ACTIVE_HIGH;
      end if;
      if Port_Cfg.Mode.H_Sync_Active_High then
         DP_CTL_Set := DP_CTL_Set or DP_CTL_HSYNC_ACTIVE_HIGH;
      end if;

      Registers.Write
        (Register => Registers.DP_CTL_A,
         Value    => DP_CTL_Set);

      Registers.Write
        (Register => Registers.DP_CTL_A,
         Value    => DP_CTL_PLL_ENABLE or DP_CTL_Set);
      Registers.Posting_Read (Registers.DP_CTL_A);
      Time.U_Delay (20);
   end Pre_On;

   ----------------------------------------------------------------------------

   procedure Post_On
     (Link     : in     DP_Link;
      Success  :    out Boolean)
   is
      pragma Warnings (GNATprove, Off, "unused variable ""Port""",
                       Reason => "Needed for a common interface");
      function To_DP (Port : Digital_Port) return DP_Port
      is
      begin
         return DP_A;
      end To_DP;
      pragma Warnings (GNATprove, On, "unused variable ""Port""");
      package Training is new DP_Training
        (TPS3_Supported    => False,
         T                 => Digital_Port,
         Aux_T             => DP_Port,
         Aux_Ch            => DP_Aux_Ch,
         DP_Info           => DP_Info,
         To_Aux            => To_DP,
         Max_V_Swing       => Max_V_Swing,
         Max_Pre_Emph      => Max_Pre_Emph,
         Set_Pattern       => Set_Training_Pattern,
         Set_Signal_Levels => Set_Signal_Levels,
         Off               => Off);
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Training.Train_DP
        (Port        => DIGI_A,
         Link        => Link,
         Success     => Success);

      if Success then
         Registers.Unset_And_Set_Mask
           (Register    => Registers.DP_CTL_A,
            Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
            Mask_Set    => DP_CTL_LINK_TRAIN_NORMAL);
      end if;
   end Post_On;

   ----------------------------------------------------------------------------

   procedure Off (Port : Digital_Port)
   is
      Enabled : Boolean;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => Registers.DP_CTL_A,
         Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
         Mask_Set    => DP_CTL_LINK_TRAIN_IDLE);
      Registers.Posting_Read (Registers.DP_CTL_A);

      Registers.Unset_Mask
        (Register => Registers.DP_CTL_A,
         Mask     => DP_CTL_DISPLAYPORT_ENABLE);
      -- implicit Posting_Read below

      Registers.Is_Set_Mask
        (Register => Registers.DP_CTL_A,
         Mask     => DP_CTL_PLL_ENABLE,
         Result   => Enabled);

      Registers.Write
        (Register => Registers.DP_CTL_A,
         Value    => 16#0000_0000#);
      Registers.Posting_Read (Registers.DP_CTL_A);

      if Enabled then
         Time.U_Delay (20);
      end if;
   end Off;

end HW.GFX.GMA.Connectors.EDP;
