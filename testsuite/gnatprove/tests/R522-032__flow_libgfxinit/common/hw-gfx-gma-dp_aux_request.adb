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

with HW.Debug;
with GNAT.Source_Info;

with HW.GFX.GMA.Config;
with HW.GFX.GMA.Registers;
with HW.GFX.GMA.Power_And_Clocks;

use type HW.Word8;
use type HW.GFX.GMA.Registers.Registers_Invalid_Index;

package body HW.GFX.GMA.DP_Aux_Request is

   DP_AUX_CTL_SEND_BUSY             : constant :=    1 * 2 ** 31;
   DP_AUX_CTL_DONE                  : constant :=    1 * 2 ** 30;
   DP_AUX_CTL_INTERRUPT_ON_DONE     : constant :=    1 * 2 ** 29;
   DP_AUX_CTL_TIME_OUT_ERROR        : constant :=    1 * 2 ** 28;
   DP_AUX_CTL_TIME_OUT_TIMER_MASK   : constant :=    3 * 2 ** 26;
   DP_AUX_CTL_TIME_OUT_TIMER_400US  : constant :=    0 * 2 ** 26;
   DP_AUX_CTL_TIME_OUT_TIMER_600US  : constant :=    1 * 2 ** 26;
   DP_AUX_CTL_TIME_OUT_TIMER_800US  : constant :=    2 * 2 ** 26;
   DP_AUX_CTL_TIME_OUT_TIMER_1600US : constant :=    3 * 2 ** 26;
   DP_AUX_CTL_RECEIVE_ERROR         : constant :=    1 * 2 ** 25;
   DP_AUX_CTL_MESSAGE_SIZE_MASK     : constant :=   31 * 2 ** 20;
   DP_AUX_CTL_MESSAGE_SIZE_SHIFT    : constant :=        2 ** 20;
   DP_AUX_CTL_PRECHARGE_TIME_MASK   : constant :=   15 * 2 ** 16;
   DP_AUX_CTL_PRECHARGE_TIME_SHIFT  : constant :=        2 ** 16;
   DP_AUX_CTL_2X_BIT_CLOCK_DIV_MASK : constant := 2047 * 2 **  0;
   -- TODO: HSW/BDW with LPT-H might need a workaround for the 2x bit clock.

   subtype DP_AUX_CTL_MESSAGE_SIZE_T is Natural range 1 .. 20;
   function DP_AUX_CTL_MESSAGE_SIZE
     (Message_Length : DP_AUX_CTL_MESSAGE_SIZE_T)
      return Word32;

   DDI_AUX_MUTEX_MUTEX_ENABLE : constant := 1 * 2 ** 31;
   DDI_AUX_MUTEX_MUTEX_STATUS : constant := 1 * 2 ** 30;

   type AUX_CH_Data_Regs is new Positive range 1 .. 5;

   type AUX_CH_Data_Regs_Array is
      array (AUX_CH_Data_Regs) of Registers.Registers_Index;

   type AUX_CH_Registers is record
      CTL   : Registers.Registers_Index;
      DATA  : AUX_CH_Data_Regs_Array;
      MUTEX : Registers.Registers_Invalid_Index;
   end record;

   type AUX_CH_Registers_Array is array (DP_Port) of AUX_CH_Registers;

   AUX_CH : constant AUX_CH_Registers_Array :=
     (if Config.Has_PCH_Aux_Channels then
         AUX_CH_Registers_Array'
        (DP_A => AUX_CH_Registers'
           (CTL   => Registers.DP_AUX_CTL_A,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.DP_AUX_DATA_A_1,
               2  => Registers.DP_AUX_DATA_A_2,
               3  => Registers.DP_AUX_DATA_A_3,
               4  => Registers.DP_AUX_DATA_A_4,
               5  => Registers.DP_AUX_DATA_A_5),
            MUTEX => Registers.Invalid_Register),
         DP_B => AUX_CH_Registers'
           (CTL   => Registers.PCH_DP_AUX_CTL_B,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.PCH_DP_AUX_DATA_B_1,
               2  => Registers.PCH_DP_AUX_DATA_B_2,
               3  => Registers.PCH_DP_AUX_DATA_B_3,
               4  => Registers.PCH_DP_AUX_DATA_B_4,
               5  => Registers.PCH_DP_AUX_DATA_B_5),
            MUTEX => Registers.Invalid_Register),
         DP_C => AUX_CH_Registers'
           (CTL   => Registers.PCH_DP_AUX_CTL_C,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.PCH_DP_AUX_DATA_C_1,
               2  => Registers.PCH_DP_AUX_DATA_C_2,
               3  => Registers.PCH_DP_AUX_DATA_C_3,
               4  => Registers.PCH_DP_AUX_DATA_C_4,
               5  => Registers.PCH_DP_AUX_DATA_C_5),
            MUTEX => Registers.Invalid_Register),
         DP_D => AUX_CH_Registers'
           (CTL   => Registers.PCH_DP_AUX_CTL_D,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.PCH_DP_AUX_DATA_D_1,
               2  => Registers.PCH_DP_AUX_DATA_D_2,
               3  => Registers.PCH_DP_AUX_DATA_D_3,
               4  => Registers.PCH_DP_AUX_DATA_D_4,
               5  => Registers.PCH_DP_AUX_DATA_D_5),
            MUTEX => Registers.Invalid_Register))
      else
         AUX_CH_Registers_Array'
        (DP_A => AUX_CH_Registers'
           (CTL   => Registers.DDI_AUX_CTL_A,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.DDI_AUX_DATA_A_1,
               2  => Registers.DDI_AUX_DATA_A_2,
               3  => Registers.DDI_AUX_DATA_A_3,
               4  => Registers.DDI_AUX_DATA_A_4,
               5  => Registers.DDI_AUX_DATA_A_5),
            MUTEX => Registers.DDI_AUX_MUTEX_A),
         DP_B => AUX_CH_Registers'
           (CTL   => Registers.DDI_AUX_CTL_B,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.DDI_AUX_DATA_B_1,
               2  => Registers.DDI_AUX_DATA_B_2,
               3  => Registers.DDI_AUX_DATA_B_3,
               4  => Registers.DDI_AUX_DATA_B_4,
               5  => Registers.DDI_AUX_DATA_B_5),
            MUTEX => Registers.DDI_AUX_MUTEX_B),
         DP_C => AUX_CH_Registers'
           (CTL   => Registers.DDI_AUX_CTL_C,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.DDI_AUX_DATA_C_1,
               2  => Registers.DDI_AUX_DATA_C_2,
               3  => Registers.DDI_AUX_DATA_C_3,
               4  => Registers.DDI_AUX_DATA_C_4,
               5  => Registers.DDI_AUX_DATA_C_5),
            MUTEX => Registers.DDI_AUX_MUTEX_C),
         DP_D => AUX_CH_Registers'
           (CTL   => Registers.DDI_AUX_CTL_D,
            DATA  => AUX_CH_Data_Regs_Array'
              (1  => Registers.DDI_AUX_DATA_D_1,
               2  => Registers.DDI_AUX_DATA_D_2,
               3  => Registers.DDI_AUX_DATA_D_3,
               4  => Registers.DDI_AUX_DATA_D_4,
               5  => Registers.DDI_AUX_DATA_D_5),
            MUTEX => Registers.DDI_AUX_MUTEX_D)));

   ----------------------------------------------------------------------------

   function DP_AUX_CTL_MESSAGE_SIZE
     (Message_Length : DP_AUX_CTL_MESSAGE_SIZE_T)
      return Word32
   is
   begin
      return Word32 (Message_Length) * DP_AUX_CTL_MESSAGE_SIZE_SHIFT;
   end DP_AUX_CTL_MESSAGE_SIZE;

   ----------------------------------------------------------------------------

   procedure Aux_Request_Low
     (Port              : in     DP_Port;
      Request           : in     DP_Defs.Aux_Request;
      Request_Length    : in     DP_Defs.Aux_Request_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean)
   with
      Global => (In_Out => Registers.Register_State,
                 Input  => (Time.State, Config.Raw_Clock)),
      Depends =>
        ((Registers.Register_State,
          Response,
          Response_Length,
          Success)
             =>
               (Registers.Register_State,
                Config.Raw_Clock,
                Time.State,
                Port,
                Request,
                Request_Length))
   is
      procedure Write_Data_Reg
        (Register : in     Registers.Registers_Index;
         Buf      : in     DP_Defs.Aux_Request;
         Length   : in     DP_Defs.Aux_Request_Length;
         Offset   : in     DP_Defs.Aux_Request_Index)
      is
         Value : Word32;
         Count : Natural;
      begin
         if Offset < Length then
            if Length - Offset > 4 then
               Count := 4;
            else
               Count := Length - Offset;
            end if;

            Value := 0;
            for Idx in DP_Defs.Aux_Request_Index range 0 .. Count - 1 loop
               Value := Value or
                  Shift_Left (Word32 (Buf (Offset + Idx)), (3 - Idx) * 8);
            end loop;
            Registers.Write (Register => Register, Value => Value);
         end if;
      end Write_Data_Reg;

      procedure Read_Data_Reg
        (Register : in     Registers.Registers_Index;
         Buf      : in out DP_Defs.Aux_Response;
         Length   : in     DP_Defs.Aux_Response_Length;
         Offset   : in     DP_Defs.Aux_Response_Index)
      is
         Value : Word32;
         Count : DP_Defs.Aux_Response_Length;
      begin
         if Offset < Length then
            if Length - Offset > 4 then
               Count := 4;
            else
               Count := Length - Offset;
            end if;

            Registers.Read (Register => Register, Value => Value);
            for Idx in 0 .. Count - 1 loop
               Buf (Offset + Idx) :=
                  Word8 (Shift_Right (Value, (3 - Idx) * 8) and 16#ff#);
            end loop;
         end if;
      end Read_Data_Reg;

      DP_AUX_CTL_2x_Clock_Mask : constant :=
        (if Config.Has_PCH_Aux_Channels then
            DP_AUX_CTL_2X_BIT_CLOCK_DIV_MASK else 0);
      DP_AUX_CTL_2x_Clock : constant Word32 :=
        (if Config.Has_PCH_Aux_Channels then
           (if Port = DP_A then
               Word32 ((Config.Default_CDClk_Freq + 1_000_000) / 2_000_000)
            else
               Word32 ((Config.Raw_Clock + 1_000_000) / 2_000_000))
         elsif Config.Has_GMCH_RawClk then
            Word32 (Div_Round_Closest (Config.Raw_Clock, 2_000_000))
         else 0);

      Busy : Boolean;
      Status : Word32;
   begin
      Response := (others => 0); -- Don't care
      Response_Length := DP_Defs.Aux_Response_Length'First;

      if Config.Need_DP_Aux_Mutex then
         Registers.Set_Mask
           (Register => AUX_CH (Port).MUTEX,
            Mask     => DDI_AUX_MUTEX_MUTEX_ENABLE);
         Registers.Wait_Set_Mask
           (Register => AUX_CH (Port).MUTEX,
            Mask     => DDI_AUX_MUTEX_MUTEX_STATUS);
      end if;

      Registers.Is_Set_Mask
        (Register => AUX_CH (Port).CTL,
         Mask     => DP_AUX_CTL_SEND_BUSY,
         Result   => Busy);
      if Busy then
         Success := False;
      else
         for Idx in AUX_CH_Data_Regs loop
            Write_Data_Reg
              (Register => AUX_CH (Port).DATA (Idx),
               Buf      => Request,
               Length   => Request_Length,
               Offset   => (Natural (Idx) - 1) * 4);
         end loop;

         Registers.Unset_And_Set_Mask
           (Register    => AUX_CH (Port).CTL,
            Mask_Unset  => DP_AUX_CTL_INTERRUPT_ON_DONE or
                           DP_AUX_CTL_TIME_OUT_TIMER_MASK or
                           DP_AUX_CTL_MESSAGE_SIZE_MASK or
                           DP_AUX_CTL_2x_Clock_Mask,
            Mask_Set    => DP_AUX_CTL_SEND_BUSY or          -- starts transfer
                           DP_AUX_CTL_DONE or               -- clears the status
                           DP_AUX_CTL_TIME_OUT_ERROR or     -- clears the status
                           DP_AUX_CTL_RECEIVE_ERROR or      -- clears the status
                           DP_AUX_CTL_TIME_OUT_TIMER_600US or
                           DP_AUX_CTL_MESSAGE_SIZE (Request_Length) or
                           DP_AUX_CTL_2x_Clock);

         Registers.Wait_Unset_Mask
           (Register => AUX_CH (Port).CTL,
            Mask     => DP_AUX_CTL_SEND_BUSY);
         Registers.Read (Register => AUX_CH (Port).CTL, Value => Status);
         Success := (Status and
                     (DP_AUX_CTL_TIME_OUT_ERROR or DP_AUX_CTL_RECEIVE_ERROR))
                    = 0;

         if Success then
            Status := (Status and DP_AUX_CTL_MESSAGE_SIZE_MASK)
                      / DP_AUX_CTL_MESSAGE_SIZE_SHIFT;
            if Natural (Status) < DP_Defs.Aux_Response_Length'First then
               Success := False;
            elsif Natural (Status) > DP_Defs.Aux_Response_Length'Last then
               Response_Length := DP_Defs.Aux_Response_Length'Last;
            else
               Response_Length := Natural (Status);
            end if;
         end if;

         if Success then
            for Idx in AUX_CH_Data_Regs loop
               Read_Data_Reg
                 (Register => AUX_CH (Port).DATA (Idx),
                  Buf      => Response,
                  Length   => Response_Length,
                  Offset   => (Natural (Idx) - 1) * 4);
            end loop;
         end if;
      end if;

      if Config.Need_DP_Aux_Mutex then
         Registers.Unset_And_Set_Mask
           (Register    => AUX_CH (Port).MUTEX,
            Mask_Unset  => DDI_AUX_MUTEX_MUTEX_ENABLE,
            Mask_Set    => DDI_AUX_MUTEX_MUTEX_STATUS);  -- frees the mutex
      end if;
   end Aux_Request_Low;

   ----------------------------------------------------------------------------

   procedure Do_Aux_Request
     (Port              : in     DP_Port;
      Request           : in     DP_Defs.Aux_Request;
      Request_Length    : in     DP_Defs.Aux_Request_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean)
   is
   begin
      for Try in Positive range 1 .. 3 loop
         Aux_Request_Low
           (Port              => Port,
            Request           => Request,
            Request_Length    => Request_Length,
            Response          => Response,
            Response_Length   => Response_Length,
            Success           => Success);
         exit when Success;
      end loop;
   end Do_Aux_Request;

end HW.GFX.GMA.DP_Aux_Request;
