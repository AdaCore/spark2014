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

with HW.GFX.GMA.DP_Info;

package body HW.GFX.GMA.Transcoder is

   type Default_Transcoder_Array is array (Pipe_Index) of Transcoder_Index;
   Default_Transcoder : constant Default_Transcoder_Array :=
     (Primary     => Trans_A,
      Secondary   => Trans_B,
      Tertiary    => Trans_C);

   function Get_Idx (Pipe : Pipe_Index; Port : GPU_Port) return Transcoder_Index
   is
   begin
      return
        (if Config.Has_EDP_Transcoder and then Port = DIGI_A then
            Trans_EDP
         else
            Default_Transcoder (Pipe));
   end Get_Idx;

   ----------------------------------------------------------------------------

   TRANS_CLK_SEL_PORT_NONE : constant := 0 * 2 ** 29;

   type TRANS_CLK_SEL_PORT_Array is
      array (Digital_Port) of Word32;
   TRANS_CLK_SEL_PORT : constant TRANS_CLK_SEL_PORT_Array :=
     (DIGI_A => 0 * 2 ** 29,   -- DDI A is not selectable
      DIGI_B => 2 * 2 ** 29,
      DIGI_C => 3 * 2 ** 29,
      DIGI_D => 4 * 2 ** 29,
      DIGI_E => 5 * 2 ** 29);

   TRANS_CONF_ENABLE          : constant := 1 * 2 ** 31;
   TRANS_CONF_ENABLED_STATUS  : constant := 1 * 2 ** 30;
   TRANS_CONF_ENABLE_DITHER   : constant := 1 * 2 **  4;

   type BPC_Array is array (BPC_Type) of Word32;
   TRANS_CONF_BPC : constant BPC_Array :=
     (6        => 2 * 2 ** 5,
      8        => 0 * 2 ** 5,
      10       => 1 * 2 ** 5,
      12       => 3 * 2 ** 5,
      others   => 0 * 2 ** 5);   -- default to 8 BPC

   function BPC_Conf (BPC : BPC_Type; Dither : Boolean) return Word32 is
   begin
      return
        (if Config.Has_Pipeconf_BPC then TRANS_CONF_BPC (BPC) else 0) or
        (if Dither                  then TRANS_CONF_ENABLE_DITHER else 0);
   end BPC_Conf;

   ----------------------------------------------------------------------------

   DDI_FUNC_CTL_ENABLE                 : constant := 1 * 2 ** 31;
   DDI_FUNC_CTL_MODE_SELECT_MASK       : constant := 7 * 2 ** 24;
   DDI_FUNC_CTL_MODE_SELECT_HDMI       : constant := 0 * 2 ** 24;
   DDI_FUNC_CTL_MODE_SELECT_DVI        : constant := 1 * 2 ** 24;
   DDI_FUNC_CTL_MODE_SELECT_DP_SST     : constant := 2 * 2 ** 24;
   DDI_FUNC_CTL_MODE_SELECT_DP_MST     : constant := 3 * 2 ** 24;
   DDI_FUNC_CTL_MODE_SELECT_FDI        : constant := 4 * 2 ** 24;

   type DDI_Select_Array is array (Digital_Port) of Word32;
   DDI_FUNC_CTL_DDI_SELECT : constant DDI_Select_Array :=
     (DIGI_A => 0 * 2 ** 28,
      DIGI_B => 1 * 2 ** 28,
      DIGI_C => 2 * 2 ** 28,
      DIGI_D => 3 * 2 ** 28,
      DIGI_E => 4 * 2 ** 28);

   type DDI_Mode_Array is array (Display_Type) of Word32;
   DDI_FUNC_CTL_MODE_SELECT : constant DDI_Mode_Array :=
     (VGA      => DDI_FUNC_CTL_MODE_SELECT_FDI,
      HDMI     => DDI_FUNC_CTL_MODE_SELECT_DVI,
      DP       => DDI_FUNC_CTL_MODE_SELECT_DP_SST,
      others   => 0);

   type HV_Sync_Array is array (Boolean) of Word32;
   DDI_FUNC_CTL_VSYNC : constant HV_Sync_Array :=
     (False => 0 * 2 ** 17,
      True  => 1 * 2 ** 17);
   DDI_FUNC_CTL_HSYNC : constant HV_Sync_Array :=
     (False => 0 * 2 ** 16,
      True  => 1 * 2 ** 16);

   DDI_FUNC_CTL_EDP_SELECT_MASK        : constant := 7 * 2 ** 12;
   DDI_FUNC_CTL_EDP_SELECT_ALWAYS_ON   : constant := 0 * 2 ** 12;
   DDI_FUNC_CTL_EDP_SELECT : constant array (Pipe_Index) of Word32 :=
     (Primary     => 4 * 2 ** 12,
      Secondary   => 5 * 2 ** 12,
      Tertiary    => 6 * 2 ** 12);

   type Port_Width_Array is array (DP_Lane_Count) of Word32;
   DDI_FUNC_CTL_PORT_WIDTH : constant Port_Width_Array :=
     (DP_Lane_Count_1 => 0 * 2 ** 1,
      DP_Lane_Count_2 => 1 * 2 ** 1,
      DP_Lane_Count_4 => 3 * 2 ** 1);

   DDI_FUNC_CTL_BPC : constant BPC_Array :=
     (6        => 2 * 2 ** 20,
      8        => 0 * 2 ** 20,
      10       => 1 * 2 ** 20,
      12       => 3 * 2 ** 20,
      others   => 0 * 2 ** 20);  -- default to 8 BPC

   ----------------------------------------------------------------------------

   TRANS_MSA_MISC_SYNC_CLK : constant := 1 * 2 ** 0;
   TRANS_MSA_MISC_BPC      : constant BPC_Array :=
     (6        => 0 * 2 ** 5,
      8        => 1 * 2 ** 5,
      10       => 2 * 2 ** 5,
      12       => 3 * 2 ** 5,
      16       => 4 * 2 ** 5,
      others   => 1 * 2 ** 5);   -- default to 8 BPC

   function TRANS_DATA_M_TU (Transfer_Unit : Positive) return Word32 is
   begin
      return Shift_Left (Word32 (Transfer_Unit - 1), 25);
   end TRANS_DATA_M_TU;

   ----------------------------------------------------------------------------

   function Encode (LSW, MSW : Pos32) return Word32 is
   begin
      return Shift_Left (Word32 (MSW - 1), 16) or Word32 (LSW - 1);
   end Encode;

   ----------------------------------------------------------------------------

   procedure Setup_Link
     (Trans : Transcoder_Regs;
      Link  : DP_Link;
      Mode  : Mode_Type)
   with
      Global => (In_Out => Registers.Register_State),
      Depends => (Registers.Register_State =>+ (Trans, Link, Mode))
   is
      Data_M, Link_M : DP_Info.M_Type;
      Data_N, Link_N : DP_Info.N_Type;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      DP_Info.Calculate_M_N
        (Link     => Link,
         Mode     => Mode,
         Data_M   => Data_M,
         Data_N   => Data_N,
         Link_M   => Link_M,
         Link_N   => Link_N);

      Registers.Write
        (Register => Trans.DATA_M1,
         Value    => TRANS_DATA_M_TU (64) or
                     Word32 (Data_M));
      Registers.Write
        (Register => Trans.DATA_N1,
         Value    => Word32 (Data_N));

      Registers.Write
        (Register => Trans.LINK_M1,
         Value    => Word32 (Link_M));
      Registers.Write
        (Register => Trans.LINK_N1,
         Value    => Word32 (Link_N));

      if Config.Has_Pipe_MSA_Misc then
         Registers.Write
           (Register => Trans.MSA_MISC,
            Value    => TRANS_MSA_MISC_SYNC_CLK or
                        TRANS_MSA_MISC_BPC (Mode.BPC));
      end if;
   end Setup_Link;

   ----------------------------------------------------------------------------

   procedure Setup
     (Pipe     : Pipe_Index;
      Port_Cfg : Port_Config)
   is
      use type HW.GFX.GMA.Registers.Registers_Invalid_Index;

      Trans : Transcoder_Regs renames
               Transcoders (Get_Idx (Pipe, Port_Cfg.Port));
      M : constant Mode_Type := Port_Cfg.Mode;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.Has_Trans_Clk_Sel and then
         Trans.CLK_SEL /= Registers.Invalid_Register and then
         Port_Cfg.Port in Digital_Port
      then
         Registers.Write
           (Register => Trans.CLK_SEL,
            Value    => TRANS_CLK_SEL_PORT (Port_Cfg.Port));
      end if;

      if Port_Cfg.Is_FDI then
         Setup_Link (Trans, Port_Cfg.FDI, Port_Cfg.Mode);
      elsif Port_Cfg.Display = DP then
         Setup_Link (Trans, Port_Cfg.DP, Port_Cfg.Mode);
      end if;

      Registers.Write (Trans.HTOTAL,   Encode (M.H_Visible,    M.H_Total));
      Registers.Write (Trans.HBLANK,   Encode (M.H_Visible,    M.H_Total));
      Registers.Write (Trans.HSYNC,    Encode (M.H_Sync_Begin, M.H_Sync_End));
      Registers.Write (Trans.VTOTAL,   Encode (M.V_Visible,    M.V_Total));
      Registers.Write (Trans.VBLANK,   Encode (M.V_Visible,    M.V_Total));
      Registers.Write (Trans.VSYNC,    Encode (M.V_Sync_Begin, M.V_Sync_End));
   end Setup;

   ----------------------------------------------------------------------------

   procedure On
     (Pipe     : Pipe_Index;
      Port_Cfg : Port_Config;
      Dither   : Boolean;
      Scale    : Boolean)
   is
      Trans : Transcoder_Regs renames
               Transcoders (Get_Idx (Pipe, Port_Cfg.Port));
      EDP_Select : constant Word32 :=
        (if Pipe = Primary and not Scale then
            DDI_FUNC_CTL_EDP_SELECT_ALWAYS_ON
         else
            DDI_FUNC_CTL_EDP_SELECT (Pipe));
   begin
      if Config.Has_Pipe_DDI_Func and Port_Cfg.Port in Digital_Port then
         Registers.Write
           (Register => Trans.DDI_FUNC_CTL,
            Value    => DDI_FUNC_CTL_ENABLE or
                        DDI_FUNC_CTL_DDI_SELECT (Port_Cfg.Port) or
                        DDI_FUNC_CTL_MODE_SELECT (Port_Cfg.Display) or
                        DDI_FUNC_CTL_BPC (Port_Cfg.Mode.BPC) or
                        DDI_FUNC_CTL_VSYNC (Port_Cfg.Mode.V_Sync_Active_High) or
                        DDI_FUNC_CTL_HSYNC (Port_Cfg.Mode.H_Sync_Active_High) or
                        EDP_Select or
                        DDI_FUNC_CTL_PORT_WIDTH (Port_Cfg.DP.Lane_Count));
      end if;

      Registers.Write
        (Register => Trans.CONF,
         Value    => TRANS_CONF_ENABLE or
                     (if not Config.Has_Pipeconf_Misc then
                        BPC_Conf (Port_Cfg.Mode.BPC, Dither) else 0));
      Registers.Posting_Read (Trans.CONF);
   end On;

   ----------------------------------------------------------------------------

   procedure Trans_Off (Trans : Transcoder_Regs)
   is
      Enabled : Boolean;
   begin
      Registers.Is_Set_Mask (Trans.CONF, TRANS_CONF_ENABLE, Enabled);

      if Enabled then
         Registers.Unset_Mask (Trans.CONF, TRANS_CONF_ENABLE);
      end if;

      -- Workaround for Broadwell:
      -- Status may be wrong if pipe hasn't been enabled since reset.
      if not Config.Pipe_Enabled_Workaround or else Enabled then
         -- synchronously wait until pipe is truly off
         Registers.Wait_Unset_Mask
           (Register => Trans.CONF,
            Mask     => TRANS_CONF_ENABLED_STATUS,
            TOut_MS  => 40);
      end if;

      if Config.Has_Pipe_DDI_Func then
         Registers.Write (Trans.DDI_FUNC_CTL, 0);
      end if;
   end Trans_Off;

   procedure Off (Pipe : Pipe_Index)
   is
      DDI_Func_Ctl : Word32;
   begin
      if Config.Has_EDP_Transcoder then
         Registers.Read (Registers.PIPE_EDP_DDI_FUNC_CTL, DDI_Func_Ctl);
         DDI_Func_Ctl := DDI_Func_Ctl and DDI_FUNC_CTL_EDP_SELECT_MASK;

         if (Pipe = Primary and
             DDI_Func_Ctl = DDI_FUNC_CTL_EDP_SELECT_ALWAYS_ON) or
            DDI_Func_Ctl = DDI_FUNC_CTL_EDP_SELECT (Pipe)
         then
            Trans_Off (Transcoders (Trans_EDP));
         end if;
      end if;

      Trans_Off (Transcoders (Default_Transcoder (Pipe)));
   end Off;

   procedure Clk_Off (Pipe : Pipe_Index)
   is
      use type Registers.Registers_Invalid_Index;

      Trans : Transcoder_Regs renames Transcoders (Default_Transcoder (Pipe));
   begin
      if Config.Has_Trans_Clk_Sel and then
         Trans.CLK_SEL /= Registers.Invalid_Register
      then
         Registers.Write (Trans.CLK_SEL, TRANS_CLK_SEL_PORT_NONE);
      end if;
   end Clk_Off;

end HW.GFX.GMA.Transcoder;
