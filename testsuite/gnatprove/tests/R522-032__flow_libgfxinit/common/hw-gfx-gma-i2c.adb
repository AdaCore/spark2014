--
-- Copyright (C) 2015 secunet Security Networks AG
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

with HW.Debug;
with GNAT.Source_Info;

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Registers;

use type HW.Word8;

package body HW.GFX.GMA.I2C is

   PCH_DSPCLK_GATE_D_GMBUS_UNIT_LVL : constant :=   1 * 2 ** 31;

   GMBUS0_GMBUS_RATE_SELECT_MASK    : constant :=   7 * 2 **  8;
   GMBUS0_GMBUS_RATE_SELECT_100KHZ  : constant :=   0 * 2 **  8;
   GMBUS0_GMBUS_RATE_SELECT_50KHZ   : constant :=   1 * 2 **  8;
   GMBUS0_PIN_PAIR_SELECT_MASK      : constant :=   7 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_NONE      : constant :=   0 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_DAC       : constant :=   2 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_LVDS      : constant :=   3 * 2 **  0;
   -- Order is C, B, D: no typo!
   GMBUS0_PIN_PAIR_SELECT_DIGI_C    : constant :=   4 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_DIGI_B    : constant :=   5 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_DIGI_D    : constant :=   6 * 2 **  0;
   -- Broxton uses different pins
   GMBUS0_PIN_PAIR_SELECT_BXT_B     : constant :=   1 * 2 **  0;
   GMBUS0_PIN_PAIR_SELECT_BXT_C     : constant :=   2 * 2 **  0;

   GMBUS1_SOFTWARE_CLEAR_INTERRUPT  : constant :=   1 * 2 ** 31;
   GMBUS1_SOFTWARE_READY            : constant :=   1 * 2 ** 30;
   GMBUS1_ENABLE_TIMEOUT            : constant :=   1 * 2 ** 29;
   GMBUS1_BUS_CYCLE_SELECT_MASK     : constant :=   7 * 2 ** 25;
   GMBUS1_BUS_CYCLE_STOP            : constant :=   1 * 2 ** 27;
   GMBUS1_BUS_CYCLE_INDEX           : constant :=   1 * 2 ** 26;
   GMBUS1_BUS_CYCLE_WAIT            : constant :=   1 * 2 ** 25;
   GMBUS1_TOTAL_BYTE_COUNT_MASK     : constant := 511 * 2 ** 16;
   GMBUS1_TOTAL_BYTE_COUNT_SHIFT    : constant :=            16;
   GMBUS1_8BIT_SLAVE_INDEX_MASK     : constant := 255 * 2 **  8;
   GMBUS1_8BIT_SLAVE_INDEX_SHIFT    : constant :=             8;
   GMBUS1_SLAVE_ADDRESS_MASK        : constant := 127 * 2 **  1;
   GMBUS1_SLAVE_ADDRESS_SHIFT       : constant :=             1;
   GMBUS1_DIRECTION_MASK            : constant :=   1 * 2 **  0;
   GMBUS1_DIRECTION_WRITE           : constant :=   0 * 2 **  0;
   GMBUS1_DIRECTION_READ            : constant :=   1 * 2 **  0;

   GMBUS2_INUSE                     : constant :=   1 * 2 ** 15;
   GMBUS2_HARDWARE_WAIT_PHASE       : constant :=   1 * 2 ** 14;
   GMBUS2_SLAVE_STALL_TIMEOUT_ERROR : constant :=   1 * 2 ** 13;
   GMBUS2_GMBUS_INTERRUPT_STATUS    : constant :=   1 * 2 ** 12;
   GMBUS2_HARDWARE_READY            : constant :=   1 * 2 ** 11;
   GMBUS2_NAK_INDICATOR             : constant :=   1 * 2 ** 10;
   GMBUS2_GMBUS_ACTIVE              : constant :=   1 * 2 **  9;
   GMBUS2_CURRENT_BYTE_COUNT_MASK   : constant := 511 * 2 **  0;

   GMBUS4_INTERRUPT_MASK            : constant :=  31 * 2 **  0;

   GMBUS5_2BYTE_INDEX_ENABLE        : constant :=   1 * 2 ** 31;

   GMBUS_Regs : constant array (0 .. 5) of Registers.Registers_Index :=
     (if Config.Has_PCH_GMBUS then
        (0 => Registers.PCH_GMBUS0,
         1 => Registers.PCH_GMBUS1,
         2 => Registers.PCH_GMBUS2,
         3 => Registers.PCH_GMBUS3,
         4 => Registers.PCH_GMBUS4,
         5 => Registers.PCH_GMBUS5)
      else
        (0 => Registers.GMCH_GMBUS0,
         1 => Registers.GMCH_GMBUS1,
         2 => Registers.GMCH_GMBUS2,
         3 => Registers.GMCH_GMBUS3,
         4 => Registers.GMCH_GMBUS4,
         5 => Registers.GMCH_GMBUS5));

   function GMBUS1_TOTAL_BYTE_COUNT
     (Count : HW.GFX.I2C.Transfer_Length)
      return Word32 is
   begin
      return Shift_Left (Word32 (Count), GMBUS1_TOTAL_BYTE_COUNT_SHIFT);
   end GMBUS1_TOTAL_BYTE_COUNT;

   function GMBUS1_SLAVE_ADDRESS
     (Address : HW.GFX.I2C.Transfer_Address)
      return Word32 is
   begin
      return Shift_Left (Word32 (Address), GMBUS1_SLAVE_ADDRESS_SHIFT);
   end GMBUS1_SLAVE_ADDRESS;

   function GMBUS0_PIN_PAIR_SELECT (Port : PCH_Port) return Word32 is
   begin
      return
        (if Config.GMBUS_Alternative_Pins then
           (case Port is
               when PCH_HDMI_B   => GMBUS0_PIN_PAIR_SELECT_BXT_B,
               when PCH_HDMI_C   => GMBUS0_PIN_PAIR_SELECT_BXT_C,
               when others       => GMBUS0_PIN_PAIR_SELECT_NONE)
         else
           (case Port is
               when PCH_DAC      => GMBUS0_PIN_PAIR_SELECT_DAC,
               when PCH_LVDS     => GMBUS0_PIN_PAIR_SELECT_LVDS,
               when PCH_HDMI_B   => GMBUS0_PIN_PAIR_SELECT_DIGI_B,
               when PCH_HDMI_C   => GMBUS0_PIN_PAIR_SELECT_DIGI_C,
               when PCH_HDMI_D   => GMBUS0_PIN_PAIR_SELECT_DIGI_D,
               when others       => GMBUS0_PIN_PAIR_SELECT_NONE));
   end GMBUS0_PIN_PAIR_SELECT;

   ----------------------------------------------------------------------------

   procedure GMBUS_Ready (Result : out Boolean)
   is
      GMBUS2 : Word32;
   begin
      Registers.Read (GMBUS_Regs (2), GMBUS2);
      Result := (GMBUS2 and (GMBUS2_HARDWARE_WAIT_PHASE or
                              GMBUS2_SLAVE_STALL_TIMEOUT_ERROR or
                              GMBUS2_GMBUS_INTERRUPT_STATUS or
                              GMBUS2_NAK_INDICATOR)) = 0;
   end GMBUS_Ready;

   procedure Reset_GMBUS (Success : out Boolean) is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Write (GMBUS_Regs (1), GMBUS1_SOFTWARE_CLEAR_INTERRUPT);
      Registers.Write (GMBUS_Regs (1), 0);
      Registers.Write (GMBUS_Regs (0), GMBUS0_PIN_PAIR_SELECT_NONE);

      GMBUS_Ready (Success);
   end Reset_GMBUS;

   procedure Init_GMBUS (Port : PCH_Port; Success : out Boolean) is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      if Config.Ungate_GMBUS_Unit_Level then
         Registers.Set_Mask
           (Register => Registers.PCH_DSPCLK_GATE_D,
            Mask     => PCH_DSPCLK_GATE_D_GMBUS_UNIT_LVL);
      end if;

      -- TODO: Refactor + check for timeout.
      Registers.Wait_Unset_Mask (GMBUS_Regs (2), GMBUS2_INUSE);

      GMBUS_Ready (Success);
      if not Success then
         Reset_GMBUS (Success);
      end if;

      if Success then
         Registers.Write
           (Register => GMBUS_Regs (0),
            Value    => GMBUS0_GMBUS_RATE_SELECT_100KHZ or
                        GMBUS0_PIN_PAIR_SELECT (Port));
         Registers.Write
           (Register => GMBUS_Regs (4),
            Value    => 0);
         Registers.Write
           (Register => GMBUS_Regs (5),
            Value    => 0);
      end if;
   end Init_GMBUS;

   procedure Release_GMBUS
   is
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Registers.Write (GMBUS_Regs (0), GMBUS0_PIN_PAIR_SELECT_NONE);

      -- Clear INUSE. TODO: Don't do it, if timeout occured (see above).
      Registers.Write (GMBUS_Regs (2), GMBUS2_INUSE);

      if Config.Ungate_GMBUS_Unit_Level then
         Registers.Unset_Mask
           (Register => Registers.PCH_DSPCLK_GATE_D,
            Mask     => PCH_DSPCLK_GATE_D_GMBUS_UNIT_LVL);
      end if;
   end Release_GMBUS;

   procedure I2C_Read
     (Port     : in     PCH_Port;
      Address  : in     HW.GFX.I2C.Transfer_Address;
      Length   : in out HW.GFX.I2C.Transfer_Length;
      Data     :    out HW.GFX.I2C.Transfer_Data;
      Success  :    out Boolean)
   is
      GMBUS2,
      GMBUS3 : Word32;

      Current     : HW.GFX.I2C.Transfer_Length;
      Transfered  : HW.GFX.I2C.Transfer_Length := 0;
   begin
      pragma Debug (Debug.Put_Line (GNAT.Source_Info.Enclosing_Entity));

      Data := (others => 0);

      Init_GMBUS (Port, Success);
      if Success then
         Registers.Write
           (Register => GMBUS_Regs (1),
            Value    => GMBUS1_SOFTWARE_READY or
                        GMBUS1_BUS_CYCLE_INDEX or
                        GMBUS1_BUS_CYCLE_WAIT or
                        GMBUS1_TOTAL_BYTE_COUNT (Length) or
                        GMBUS1_SLAVE_ADDRESS (Address) or
                        GMBUS1_DIRECTION_READ);

         while Success and then Transfered < Length loop
            Registers.Wait_Set_Mask
              (Register => GMBUS_Regs (2),
               Mask     => GMBUS2_HARDWARE_READY,
               TOut_MS  => 55);

            Registers.Read (GMBUS_Regs (2), GMBUS2);
            Success :=  (GMBUS2 and GMBUS2_HARDWARE_READY) /= 0 and
                        (GMBUS2 and GMBUS2_NAK_INDICATOR) = 0;
            if Success then
               Current := GFX.I2C.Transfer_Length'Min (Length, Transfered + 4);

               Registers.Read (GMBUS_Regs (3), GMBUS3);
               for I in Transfered .. Current - 1 loop
                  Data (I) := Byte (GMBUS3 and 16#ff#);
                  GMBUS3 := Shift_Right (GMBUS3, 8);
               end loop;
               Transfered := Current;
            end if;
         end loop;
         if Success then
            Registers.Wait_Set_Mask
              (Register => GMBUS_Regs (2),
               Mask     => GMBUS2_HARDWARE_WAIT_PHASE);
            Registers.Write
              (Register => GMBUS_Regs (1),
               Value    => GMBUS1_SOFTWARE_READY or GMBUS1_BUS_CYCLE_STOP);
            Registers.Wait_Unset_Mask
              (Register => GMBUS_Regs (2),
               Mask     => GMBUS2_GMBUS_ACTIVE);
         end if;
      end if;
      Length := Transfered;

      Release_GMBUS;
   end I2C_Read;

end HW.GFX.GMA.I2C;
