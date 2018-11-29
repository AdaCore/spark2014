--
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

with HW.GFX.DP_Training;
with HW.GFX.GMA.DP_Aux_Ch;
with HW.GFX.GMA.DP_Info;
with HW.GFX.GMA.Registers;

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.PCH.DP is

   type DP_Array is array (PCH_DP_Port) of Registers.Registers_Index;
   DP_CTL : constant DP_Array :=
     (PCH_DP_B => Registers.PCH_DP_B,
      PCH_DP_C => Registers.PCH_DP_C,
      PCH_DP_D => Registers.PCH_DP_D);

   DP_CTL_DISPLAY_PORT_ENABLE          : constant := 1 * 2 ** 31;
   DP_CTL_VSWING_LEVEL_SET_SHIFT       : constant :=          25;
   DP_CTL_VSWING_LEVEL_SET_MASK        : constant := 7 * 2 ** 25;
   DP_CTL_PREEMPH_LEVEL_SET_SHIFT      : constant :=          22;
   DP_CTL_PREEMPH_LEVEL_SET_MASK       : constant := 7 * 2 ** 22;
   DP_CTL_PORT_WIDTH_SHIFT             : constant :=          19;
   DP_CTL_PORT_REVERSAL                : constant := 1 * 2 ** 15;
   DP_CTL_LINK_TRAIN_MASK              : constant := 7 * 2 **  8;
   DP_CTL_LINK_TRAIN_PAT1              : constant := 0 * 2 **  8;
   DP_CTL_LINK_TRAIN_PAT2              : constant := 1 * 2 **  8;
   DP_CTL_LINK_TRAIN_IDLE              : constant := 2 * 2 **  8;
   DP_CTL_LINK_TRAIN_NORMAL            : constant := 3 * 2 **  8;
   DP_CTL_AUDIO_OUTPUT_ENABLE          : constant := 1 * 2 **  6;
   DP_CTL_PORT_DETECT                  : constant := 1 * 2 **  2;

   function DP_CTL_VSWING_LEVEL_SET
     (VS : DP_Info.DP_Voltage_Swing)
      return Word32
   is
   begin
      return Shift_Left
        (Word32 (DP_Info.DP_Voltage_Swing'Pos (VS)),
         DP_CTL_VSWING_LEVEL_SET_SHIFT);
   end DP_CTL_VSWING_LEVEL_SET;

   function DP_CTL_PREEMPH_LEVEL_SET (PE : DP_Info.DP_Pre_Emph) return Word32
   is
   begin
      return Shift_Left
        (Word32 (DP_Info.DP_Pre_Emph'Pos (PE)), DP_CTL_PREEMPH_LEVEL_SET_SHIFT);
   end DP_CTL_PREEMPH_LEVEL_SET;

   function DP_CTL_PORT_WIDTH (Lane_Count : DP_Lane_Count) return Word32
   is
   begin
      return Shift_Left
        (Word32 (Lane_Count_As_Integer (Lane_Count)) - 1,
         DP_CTL_PORT_WIDTH_SHIFT);
   end DP_CTL_PORT_WIDTH;

   type DP_CTL_LINK_TRAIN_Array is array (DP_Info.Training_Pattern) of Word32;
   DP_CTL_LINK_TRAIN : constant DP_CTL_LINK_TRAIN_Array :=
     (DP_Info.TP_1      => DP_CTL_LINK_TRAIN_PAT1,
      DP_Info.TP_2      => DP_CTL_LINK_TRAIN_PAT2,
      DP_Info.TP_3      => DP_CTL_LINK_TRAIN_PAT2,
      DP_Info.TP_Idle   => DP_CTL_LINK_TRAIN_IDLE,
      DP_Info.TP_None   => DP_CTL_LINK_TRAIN_NORMAL);

   ----------------------------------------------------------------------------

   pragma Warnings (GNATprove, Off, "unused variable ""Port""",
                    Reason => "Needed for a common interface");
   function Max_V_Swing
     (Port : PCH_DP_Port)
      return DP_Info.DP_Voltage_Swing
   is
   begin
      return DP_Info.VS_Level_3;
   end Max_V_Swing;

   function Max_Pre_Emph
     (Port        : PCH_DP_Port;
      Train_Set   : DP_Info.Train_Set)
      return DP_Info.DP_Pre_Emph
   is
   begin
      return
        (case Train_Set.Voltage_Swing is
            when DP_Info.VS_Level_0 => DP_Info.Emph_Level_3,
            when DP_Info.VS_Level_1 => DP_Info.Emph_Level_2,
            when DP_Info.VS_Level_2 => DP_Info.Emph_Level_1,
            when DP_Info.VS_Level_3 => DP_Info.Emph_Level_0);
   end Max_Pre_Emph;

   ----------------------------------------------------------------------------

   pragma Warnings (GNATprove, Off, "unused variable ""Link""",
                    Reason => "Needed for a common interface");
   procedure Set_Training_Pattern
     (Port     : PCH_DP_Port;
      Link     : DP_Link;
      Pattern  : DP_Info.Training_Pattern)
   is
   begin
      Registers.Unset_And_Set_Mask
        (Register    => DP_CTL (Port),
         Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
         Mask_Set    => DP_CTL_LINK_TRAIN (Pattern));
   end Set_Training_Pattern;

   procedure Set_Signal_Levels
     (Port        : PCH_DP_Port;
      Link        : DP_Link;
      Train_Set   : DP_Info.Train_Set)
   is
   begin
      Registers.Unset_And_Set_Mask
        (Register    => DP_CTL (Port),
         Mask_Unset  => DP_CTL_VSWING_LEVEL_SET_MASK or
                        DP_CTL_PREEMPH_LEVEL_SET_MASK,
         Mask_Set    => DP_CTL_VSWING_LEVEL_SET (Train_Set.Voltage_Swing) or
                        DP_CTL_PREEMPH_LEVEL_SET (Train_Set.Pre_Emph));
   end Set_Signal_Levels;

   procedure Off (Port : PCH_DP_Port)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Unset_And_Set_Mask
        (Register    => DP_CTL (Port),
         Mask_Unset  => DP_CTL_LINK_TRAIN_MASK,
         Mask_Set    => DP_CTL_LINK_TRAIN_IDLE);
      Registers.Posting_Read (DP_CTL (Port));

      Registers.Write (DP_CTL (Port), 0);
      Registers.Posting_Read (DP_CTL (Port));
   end Off;
   pragma Warnings (GNATprove, On, "unused variable ""Port""");
   pragma Warnings (GNATprove, On, "unused variable ""Link""");

   ----------------------------------------------------------------------------

   procedure On
     (Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   is
      function To_DP (Port : PCH_DP_Port) return DP_Port
      is
      begin
         return
           (case Port is
               when PCH_DP_B => DP_B,
               when PCH_DP_C => DP_C,
               when PCH_DP_D => DP_D);
      end To_DP;
      package Training is new DP_Training
        (TPS3_Supported    => False,
         T                 => PCH_DP_Port,
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

      Registers.Write
        (Register => DP_CTL (Port_Cfg.PCH_Port),
         Value    => DP_CTL_DISPLAY_PORT_ENABLE or
                     DP_CTL_PORT_WIDTH (Port_Cfg.DP.Lane_Count) or
                     DP_CTL_LINK_TRAIN_PAT1);

      Training.Train_DP
        (Port     => Port_Cfg.PCH_Port,
         Link     => Port_Cfg.DP,
         Success  => Success);
   end On;

   ----------------------------------------------------------------------------

   procedure All_Off
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      for Port in PCH_DP_Port loop
         Off (Port);
      end loop;
   end All_Off;

end HW.GFX.GMA.PCH.DP;
