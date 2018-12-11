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
with HW.GFX.GMA.Registers;

package body HW.GFX.GMA.Power_And_Clocks_Ironlake is

   PCH_DREF_CONTROL_120MHZ_CPU_OUTPUT_MASK      : constant := 3 * 2 ** 13;
   PCH_DREF_CONTROL_120MHZ_CPU_OUTPUT_SSC       : constant := 2 * 2 ** 13;
   PCH_DREF_CONTROL_120MHZ_CPU_OUTPUT_NONSSC    : constant := 3 * 2 ** 13;
   PCH_DREF_CONTROL_120MHZ_SSC_EN_MASK          : constant := 3 * 2 ** 11;
   PCH_DREF_CONTROL_120MHZ_SSC_EN               : constant := 2 * 2 ** 11;
   PCH_DREF_CONTROL_120MHZ_NONSSC_EN_MASK       : constant := 3 * 2 **  9;
   PCH_DREF_CONTROL_120MHZ_NONSSC_EN            : constant := 2 * 2 **  9;
   PCH_DREF_CONTROL_120MHZ_SSC4_EN_MASK         : constant := 3 * 2 **  7;
   PCH_DREF_CONTROL_120MHZ_SSC4_EN              : constant := 2 * 2 **  7;
   PCH_DREF_CONTROL_120MHZ_SSC4_DOWNSPREAD      : constant := 0 * 2 **  6;
   PCH_DREF_CONTROL_120MHZ_SSC4_CENTERSPREAD    : constant := 1 * 2 **  6;
   PCH_DREF_CONTROL_120MHZ_SSC_MODULATION_EN    : constant := 1 * 2 **  1;
   PCH_DREF_CONTROL_120MHZ_SSC4_MODULATION_EN   : constant := 1 * 2 **  0;

   procedure Initialize is
   begin
      -- ILK: enable non-spread spectrum clock, enable spread spectrum clock
      Registers.Write
        (Register => Registers.PCH_DREF_CONTROL,
         Value    => PCH_DREF_CONTROL_120MHZ_SSC_EN or
                     PCH_DREF_CONTROL_120MHZ_NONSSC_EN or
                     PCH_DREF_CONTROL_120MHZ_SSC_MODULATION_EN);
      Registers.Posting_Read (Registers.PCH_DREF_CONTROL);
      Time.U_Delay (1);
      if Config.Internal_Is_EDP then   -- TODO: check for presence
         -- always use spread spectrum clock for CPU output
         Registers.Set_Mask
           (Register => Registers.PCH_DREF_CONTROL,
            Mask     => PCH_DREF_CONTROL_120MHZ_CPU_OUTPUT_SSC);
         Registers.Posting_Read (Registers.PCH_DREF_CONTROL);
         Time.U_Delay (20);   -- DMI latency
      end if;

      Config.Raw_Clock := Config.Default_RawClk_Freq;
   end Initialize;

end HW.GFX.GMA.Power_And_Clocks_Ironlake;
