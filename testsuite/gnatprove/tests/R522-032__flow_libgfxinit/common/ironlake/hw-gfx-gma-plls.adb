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

with HW.Debug;
with GNAT.Source_Info;

package body HW.GFX.GMA.PLLs
with
   Refined_State => (State => PLLs)
is

   Debug_Clocks : constant Boolean := False;

   type Count_Range is new Natural range 0 .. 2;

   type PLL_State is record
      Use_Count   : Count_Range;
      Used_For_DP : Boolean;
      Link_Rate   : DP_Bandwidth;
      Mode        : Mode_Type;
   end record;

   type PLL_State_Array is array (DPLLs) of PLL_State;

   PLLs : PLL_State_Array;

   ----------------------------------------------------------------------------

   subtype N_Range     is Int64 range          3 ..          8;
   subtype M_Range     is Int64 range         79 ..        128;
   subtype M1_Range    is Int64 range         14 ..         25;
   subtype M2_Range    is Int64 range          7 ..         12;
   subtype P_Range     is Int64 range          5 ..        112;
   subtype P1_Range    is Int64 range          1 ..          8;
   subtype P2_Range    is Int64 range          5 ..         14;
   subtype VCO_Range   is Int64 range 1760000000 .. 3510000000;
   subtype Clock_Range is HW.GFX.Frequency_Type;

   type Clock_Type is
      record
         N               : N_Range;
         M1              : M1_Range;
         M2              : M2_Range;
         P1              : P1_Range;
         P2              : P2_Range;
         M               : M_Range;
         P               : P_Range;
         VCO             : VCO_Range;
         Reference_Clock : Clock_Range;
         Dotclock        : Clock_Range;
      end record;

   Invalid_Clock : constant Clock_Type := Clock_Type'
      (N               => N_Range'Last,
       M1              => M1_Range'Last,
       M2              => M2_Range'Last,
       P1              => P1_Range'Last,
       P2              => P2_Range'Last,
       Reference_Clock => Clock_Range'Last,
       M               => M_Range'Last,
       P               => P_Range'Last,
       VCO             => VCO_Range'Last,
       Dotclock        => Clock_Range'Last);

   type Limits_Type is
      record
         N_Lower      : N_Range;
         N_Upper      : N_Range;
         M_Lower      : M_Range;
         M_Upper      : M_Range;
         M1_Lower     : M1_Range;
         M1_Upper     : M1_Range;
         M2_Lower     : M2_Range;
         M2_Upper     : M2_Range;
         P_Lower      : P_Range;
         P_Upper      : P_Range;
         P1_Lower     : P1_Range;
         P1_Upper     : P1_Range;
         P2_Fast      : P2_Range;
         P2_Slow      : P2_Range;
         P2_Threshold : Clock_Range;
         VCO_Lower    : VCO_Range;
         VCO_Upper    : VCO_Range;
      end record;

   LVDS_Single_Limits : constant Limits_Type := Limits_Type'
     (N_Lower      =>   3,           N_Upper   =>   5,
      M_Lower      =>  79,           M_Upper   => 118,
      M1_Lower     =>  14,           M1_Upper  =>  22, -- this is capped by M_Upper >= 5 * M1 + M2_Lower
      M2_Lower     =>   7,           M2_Upper  =>  11,
      P_Lower      =>  28,           P_Upper   => 112,
      P1_Lower     =>   2,           P1_Upper  =>   8,
      P2_Fast      =>  14,           P2_Slow   =>  14,
      P2_Threshold => Clock_Range'First,
      VCO_Lower    => 1_760_000_000, VCO_Upper => 3_510_000_000);
   LVDS_Dual_Limits : constant Limits_Type := Limits_Type'
     (N_Lower      =>   3,           N_Upper   =>   5,
      M_Lower      =>  79,           M_Upper   => 127,
      M1_Lower     =>  14,           M1_Upper  =>  24,
      M2_Lower     =>   7,           M2_Upper  =>  11,
      P_Lower      =>  14,           P_Upper   =>  56,
      P1_Lower     =>   2,           P1_Upper  =>   8,
      P2_Fast      =>   7,           P2_Slow   =>   7,
      P2_Threshold => Clock_Range'First,
      VCO_Lower    => 1_760_000_000, VCO_Upper => 3_510_000_000);
   All_Other_Limits : constant Limits_Type := Limits_Type'
     (N_Lower      =>   3,           N_Upper   =>   7,
      M_Lower      =>  79,           M_Upper   => 127,
      M1_Lower     =>  14,           M1_Upper  =>  24,
      M2_Lower     =>   7,           M2_Upper  =>  11,
      P_Lower      =>   5,           P_Upper   =>  80,
      P1_Lower     =>   1,           P1_Upper  =>   8,
      -- use P2_Slow if Dotclock <= P2_Threshold, P2_Fast otherwise
      P2_Fast      =>   5,           P2_Slow   =>  10,
      P2_Threshold =>   225_000_000,
      VCO_Lower    => 1_760_000_000, VCO_Upper => 3_510_000_000);

   ----------------------------------------------------------------------------

   type Regs is array (DPLLs) of Registers.Registers_Index;

   DPLL : constant Regs := Regs'(Registers.PCH_DPLL_A, Registers.PCH_DPLL_B);
   DPLL_VCO_ENABLE         : constant := 1 * 2 ** 31;
   DPLL_P2_10_OR_14        : constant := 0 * 2 ** 24;
   DPLL_P2_5_OR_7          : constant := 1 * 2 ** 24;
   DPLL_P1_DIVIDER_SHIFT   : constant := 16;
   DPLL_SDVOCLK            : constant := 2 * 2 ** 13;

   DPLL_HIGH_SPEED : constant := 1 * 2 ** 30;
   DPLL_MODE_LVDS  : constant := 2 * 2 ** 26;
   DPLL_MODE_DAC   : constant := 1 * 2 ** 26;
   DPLL_DREFCLK    : constant := 0 * 2 ** 13;
   DPLL_SSC        : constant := 3 * 2 ** 13;

   MODE_DPLL_DAC_HDMI : constant Word32 := Word32'
      (DPLL_MODE_DAC or DPLL_DREFCLK or DPLL_HIGH_SPEED);

   MODE_DPLL_LVDS : constant Word32 := Word32'
      (DPLL_MODE_LVDS or DPLL_SSC);

   MODE_DPLL_DP : constant Word32 := Word32'
      (DPLL_MODE_DAC or DPLL_SSC or DPLL_HIGH_SPEED);

   type DPLL_Mode_Array is array (Display_Type) of Word32;

   DPLL_Mode : constant DPLL_Mode_Array := DPLL_Mode_Array'
     (LVDS     => MODE_DPLL_LVDS,
      DP       => MODE_DPLL_DP,
      others   => MODE_DPLL_DAC_HDMI);

   FP0 : constant Regs := Regs'(Registers.PCH_FPA0, Registers.PCH_FPB0);
   FP1 : constant Regs := Regs'(Registers.PCH_FPA1, Registers.PCH_FPB1);
   FP_DOUBLE_CLOCK       : constant := 1 * 2 ** 27;
   FP_N_SHIFT            : constant := 16;
   FP_M1_SHIFT           : constant := 8;
   FP_M2_SHIFT           : constant := 0;

   ----------------------------------------------------------------------------

   procedure Verify_Parameters
      (N               : in     N_Range;
       M1              : in     M1_Range;
       M2              : in     M2_Range;
       P1              : in     P1_Range;
       P2              : in     P2_Range;
       Reference_Clock : in     Clock_Range;
       Current_Limits  : in     Limits_Type;
       Result          :    out Clock_Type;
       Valid           :    out Boolean)
   with
      Global => null,
      Pre => True,
      Post => True
   is
      M        : Int64;
      P        : Int64;
      VCO      : Int64;
      Dotclock : Int64;
   begin
      pragma Debug (Debug_Clocks, Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      M        := 5 * M1 + M2;
      P        := P1 * P2;
      VCO      := (Int64 (Reference_Clock) * M) / N;
      Dotclock := VCO / P;

      pragma Debug (Debug_Clocks and not (Current_Limits.P1_Lower  <= P1  and P1  <= Current_Limits.P1_Upper ), Debug.Put_Line ("P1 out of range."));
      pragma Debug (Debug_Clocks and     (Current_Limits.P2_Fast   /= P2  and P2  /= Current_Limits.P2_Slow  ), Debug.Put_Line ("P2 out of range."));
      pragma Debug (Debug_Clocks and not (Current_Limits.P_Lower   <= P   and P   <= Current_Limits.P_Upper  ), Debug.Put_Line ("P out of range."));
      pragma Debug (Debug_Clocks and not (Current_Limits.M1_Lower  <= M1  and M1  <= Current_Limits.M1_Upper ), Debug.Put_Line ("M1 out of range."));
      pragma Debug (Debug_Clocks and not (Current_Limits.M2_Lower  <= M2  and M2  <= Current_Limits.M2_Upper ), Debug.Put_Line ("M2 out of range."));
      -- pragma Debug (Debug_Clocks and not (M2 <= M1                                           ), Debug.Put_Line ("M1 greater thant M2."));
      pragma Debug (Debug_Clocks and not (Current_Limits.N_Lower   <= N   and N   <= Current_Limits.N_Upper  ), Debug.Put_Line ("N out of range."));
      pragma Debug (Debug_Clocks and not (Current_Limits.M_Lower   <= M   and M   <= Current_Limits.M_Upper  ), Debug.Put_Line ("M out of range."));
      pragma Debug (Debug_Clocks and not (Current_Limits.VCO_Lower <= VCO and VCO <= Current_Limits.VCO_Upper), Debug.Put_Line ("VCO out of range."));

      pragma Debug (Debug_Clocks and not (Int64 (Clock_Range'First) <= Dotclock),       Debug.Put_Line ("Dotclock too low."));
      pragma Debug (Debug_Clocks and not (Int64 (Clock_Range'First) <= Dotclock),       Debug.Put_Int64 (Dotclock));
      pragma Debug (Debug_Clocks and not (Int64 (Clock_Range'First) <= Dotclock),       Debug.New_Line);

      pragma Debug (Debug_Clocks and not (Dotclock <= Int64 (Clock_Range'Last)),        Debug.Put_Line ("Dotclock too high."));
      pragma Debug (Debug_Clocks and not (Dotclock <= Int64 (Clock_Range'Last)),        Debug.Put_Int64 (Dotclock));
      pragma Debug (Debug_Clocks and not (Dotclock <= Int64 (Clock_Range'Last)),        Debug.New_Line);

      Valid :=
         Current_Limits.P1_Lower  <= P1  and P1  <= Current_Limits.P1_Upper  and
         (Current_Limits.P2_Fast   = P2   or P2   = Current_Limits.P2_Slow)  and
         Current_Limits.P_Lower   <= P   and P   <= Current_Limits.P_Upper   and
         Current_Limits.M1_Lower  <= M1  and M1  <= Current_Limits.M1_Upper  and
         Current_Limits.M2_Lower  <= M2  and M2  <= Current_Limits.M2_Upper  and
         -- M2 <= M1                                                            and
         Current_Limits.N_Lower   <= N   and N   <= Current_Limits.N_Upper   and
         Current_Limits.M_Lower   <= M   and M   <= Current_Limits.M_Upper   and
         Current_Limits.VCO_Lower <= VCO and VCO <= Current_Limits.VCO_Upper and
         Int64 (Clock_Range'First) <= Dotclock                               and
         Dotclock <= Int64 (Clock_Range'Last);

      if Valid
      then
         Result := Clock_Type'
            (N               => N,
             M1              => M1,
             M2              => M2,
             P1              => P1,
             P2              => P2,
             Reference_Clock => Reference_Clock,
             M               => M,
             P               => P,
             VCO             => VCO,
             Dotclock        => Clock_Range (Dotclock));
      else
         Result := Invalid_Clock;
      end if;

   end Verify_Parameters;

   procedure Calculate_Clock_Parameters
      (Display         : in     Display_Type;
       Target_Dotclock : in     Clock_Range;
       Reference_Clock : in     Clock_Range;
       Best_Clock      :    out Clock_Type;
       Valid           :    out Boolean)
   with
      Global => null,
      Pre => True,
      Post => True
   is
      Limits : constant Limits_Type :=
        (if Display = LVDS then
           (if Target_Dotclock >= Config.LVDS_Dual_Threshold then
               LVDS_Dual_Limits
            else
               LVDS_Single_Limits)
         else
            All_Other_Limits);

      P2               : P2_Range;
      Best_Delta       : Int64 := Int64'Last;
      Current_Delta    : Int64;
      Current_Clock    : Clock_Type;
      Registers_Valid  : Boolean;
   begin
      pragma Debug (Debug_Clocks, Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Valid      := False;
      Best_Clock := Invalid_Clock;

      if Target_Dotclock <= Limits.P2_Threshold then
         P2 := Limits.P2_Slow;
      else
         P2 := Limits.P2_Fast;
      end if;

      for N in N_Range range Limits.N_Lower .. Limits.N_Upper
      loop
         -- reverse loops as hardware prefers higher values
         for M1 in reverse M1_Range range Limits.M1_Lower .. Limits.M1_Upper
         loop
            for M2 in reverse M2_Range range Limits.M2_Lower .. Limits.M2_Upper
            loop
               for P1 in reverse P1_Range range Limits.P1_Lower .. Limits.P1_Upper
               loop
                  Verify_Parameters
                     (N               => N,
                      M1              => M1,
                      M2              => M2,
                      P1              => P1,
                      P2              => P2,
                      Reference_Clock => Reference_Clock,
                      Current_Limits  => Limits,
                      Result          => Current_Clock,
                      Valid           => Registers_Valid);

                  if Registers_Valid
                  then
                     if Current_Clock.Dotclock > Target_Dotclock
                     then
                        Current_Delta := Current_Clock.Dotclock - Target_Dotclock;
                     else
                        Current_Delta := Target_Dotclock - Current_Clock.Dotclock;
                     end if;

                     if Current_Delta < Best_Delta
                     then
                        Best_Delta := Current_Delta;
                        Best_Clock := Current_Clock;
                        Valid      := True;
                     end if;

                     pragma Debug (Debug_Clocks, Debug.Put ("Current/Target/Best_Delta: "));
                     pragma Debug (Debug_Clocks, Debug.Put_Int64 (Current_Clock.Dotclock));
                     pragma Debug (Debug_Clocks, Debug.Put ("/"));
                     pragma Debug (Debug_Clocks, Debug.Put_Int64 (Target_Dotclock));
                     pragma Debug (Debug_Clocks, Debug.Put ("/"));
                     pragma Debug (Debug_Clocks, Debug.Put_Int64 (Best_Delta));
                     pragma Debug (Debug_Clocks, Debug.Put_Line ("."));

                  end if;
               end loop;
            end loop;
         end loop;
      end loop;

      pragma Debug (Valid,     Debug.Put_Line ("Valid clock found."));
      pragma Debug (Valid,     Debug.Put ("Best/Target/Delta: "));
      pragma Debug (Valid,     Debug.Put_Int64 (Best_Clock.Dotclock));
      pragma Debug (Valid,     Debug.Put ("/"));
      pragma Debug (Valid,     Debug.Put_Int64 (Target_Dotclock));
      pragma Debug (Valid,     Debug.Put ("/"));
      pragma Debug (Valid,     Debug.Put_Int64 (Best_Delta));
      pragma Debug (Valid,     Debug.Put_Line ("."));
      pragma Debug (not Valid, Debug.Put_Line ("No valid clock found."));

   end Calculate_Clock_Parameters;

   procedure Program_DPLL
     (PLL      : DPLLs;
      Display  : Display_Type;
      Clk      : Clock_Type)
   with
      Global => (In_Out => Registers.Register_State),
      Pre => True,
      Post => True
   is
      FP, Encoded_P1, Encoded_P2 : Word32;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      FP :=
         Shift_Left (Word32 (Clk.N - 2), FP_N_SHIFT)     or
         Shift_Left (Word32 (Clk.M1 - 2), FP_M1_SHIFT)   or
         Shift_Left (Word32 (Clk.M2 - 2), FP_M2_SHIFT);

      Registers.Write (FP0 (PLL), FP);
      Registers.Write (FP1 (PLL), FP);

      Encoded_P1 := Shift_Left (1, Natural (Clk.P1) - 1);

      if Clk.P2 = 5 or Clk.P2 = 7
      then
         Encoded_P2 := DPLL_P2_5_OR_7;
      else
         Encoded_P2 := DPLL_P2_10_OR_14;
      end if;

      Registers.Write
         (Register => DPLL (PLL),
          Value    => DPLL_Mode (Display)                            or
                      Encoded_P2                                     or
                      Shift_Left (Encoded_P1, DPLL_P1_DIVIDER_SHIFT) or
                      Encoded_P1);
   end Program_DPLL;

   procedure On
     (PLL      : in     T;
      Port_Cfg : in     Port_Config;
      Success  :    out Boolean)
   is
      Target_Clock : constant Frequency_Type :=
        (if Port_Cfg.Display = DP then
            DP_Symbol_Rate (Port_Cfg.DP.Bandwidth)
         else
            Port_Cfg.Mode.Dotclock);
      Clk : Clock_Type;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Success := PLL in DPLLs;
      Clk := Invalid_Clock;

      if Success then
         if Port_Cfg.Display = DP then
            Success := True;
            -- we use static values for DP
            case Port_Cfg.DP.Bandwidth is
               when DP_Bandwidth_1_62 =>
                  Clk.N    :=  3;
                  Clk.M1   := 14;
                  Clk.M2   := 11;
                  Clk.P1   :=  2;
                  Clk.P2   := 10;
               when DP_Bandwidth_2_7 =>
                  Clk.N    :=  4;
                  Clk.M1   := 16;
                  Clk.M2   := 10;
                  Clk.P1   :=  1;
                  Clk.P2   := 10;
               when others =>
                  Success := False;
            end case;
         elsif Target_Clock <= 340_000_000 then
            Calculate_Clock_Parameters
              (Display           => Port_Cfg.Display,
               Target_Dotclock   => Target_Clock,
               -- should be, but doesn't has to be always the same:
               Reference_Clock   => 120_000_000,
               Best_Clock        => Clk,
               Valid             => Success);
         else
            Success := False;
            pragma Debug (Debug.Put ("WARNING: Targeted clock too high: "));
            pragma Debug (Debug.Put_Int64 (Target_Clock));
            pragma Debug (Debug.Put (" > "));
            pragma Debug (Debug.Put_Int32 (340_000_000));
            pragma Debug (Debug.New_Line);
            pragma Debug (Debug.New_Line);
         end if;
      end if;

      if Success then
         Program_DPLL (PLL, Port_Cfg.Display, Clk);

         Registers.Set_Mask (DPLL (PLL), DPLL_VCO_ENABLE);
         Registers.Posting_Read (DPLL (PLL));
         Time.U_Delay (150);
      end if;
   end On;

   procedure Off (PLL : T)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if PLL in DPLLs then
         Registers.Unset_Mask (DPLL (PLL), DPLL_VCO_ENABLE);
      end if;
   end Off;

   ----------------------------------------------------------------------------

   procedure Initialize
   is
   begin
      PLLs :=
        (DPLLs =>
           (Use_Count   => 0,
            Used_For_DP => False,
            Link_Rate   => DP_Bandwidth'First,
            Mode        => Invalid_Mode));
   end Initialize;

   procedure Alloc_Configurable
     (Port_Cfg : in     Port_Config;
      PLL      :    out T;
      Success  :    out Boolean)
   with
      Pre => True
   is
      function Config_Matches (PE : PLL_State) return Boolean
      is
      begin
         return
            PE.Used_For_DP = (Port_Cfg.Display = DP) and
            ((PE.Used_For_DP and PE.Link_Rate = Port_Cfg.DP.Bandwidth) or
             (not PE.Used_For_DP and PE.Mode = Port_Cfg.Mode));
      end Config_Matches;
   begin
      -- try to find shareable PLL
      for P in DPLLs loop
         Success := PLLs (P).Use_Count /= 0 and
                     PLLs (P).Use_Count /= Count_Range'Last and
                     Config_Matches (PLLs (P));
         if Success then
            PLL := P;
            PLLs (PLL).Use_Count := PLLs (PLL).Use_Count + 1;
            return;
         end if;
      end loop;

      -- try to find free PLL
      for P in DPLLs loop
         if PLLs (P).Use_Count = 0 then
            PLL := P;
            On (PLL, Port_Cfg, Success);
            if Success then
               PLLs (PLL) :=
                 (Use_Count   => 1,
                  Used_For_DP => Port_Cfg.Display = DP,
                  Link_Rate   => Port_Cfg.DP.Bandwidth,
                  Mode        => Port_Cfg.Mode);
            end if;
            return;
         end if;
      end loop;

      PLL := Invalid;
   end Alloc_Configurable;

   procedure Alloc
     (Port_Cfg : in     Port_Config;
      PLL      :    out T;
      Success  :    out Boolean)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Port_Cfg.Port = DIGI_A then
         PLL := Invalid;
         Success := True;
      else
         Alloc_Configurable (Port_Cfg, PLL, Success);
      end if;
   end Alloc;

   procedure Free (PLL : T)
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if PLL in DPLLs then
         if PLLs (PLL).Use_Count /= 0 then
            PLLs (PLL).Use_Count := PLLs (PLL).Use_Count - 1;
            if PLLs (PLL).Use_Count = 0 then
               Off (PLL);
            end if;
         end if;
      end if;
   end Free;

   procedure All_Off
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      for PLL in DPLLs loop
         Off (PLL);
      end loop;
   end All_Off;

   function Register_Value (PLL : T) return Word32
   is
   begin
      return (if PLL = DPLL_B then 1 else 0);
   end Register_Value;

end HW.GFX.GMA.PLLs;
