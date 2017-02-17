------------------------------------------------------------------------------
--                                                                          --
--                    Copyright (C) 2015, AdaCore                           --
--                                                                          --
--  Redistribution and use in source and binary forms, with or without      --
--  modification, are permitted provided that the following conditions are  --
--  met:                                                                    --
--     1. Redistributions of source code must retain the above copyright    --
--        notice, this list of conditions and the following disclaimer.     --
--     2. Redistributions in binary form must reproduce the above copyright --
--        notice, this list of conditions and the following disclaimer in   --
--        the documentation and/or other materials provided with the        --
--        distribution.                                                     --
--     3. Neither the name of STMicroelectronics nor the names of its       --
--        contributors may be used to endorse or promote products derived   --
--        from this software without specific prior written permission.     --
--                                                                          --
--   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS    --
--   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT      --
--   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR  --
--   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT   --
--   HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, --
--   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT       --
--   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,  --
--   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY  --
--   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT    --
--   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE  --
--   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.   --
--                                                                          --
--                                                                          --
--  This file is based on:                                                  --
--                                                                          --
--   @file    stm32f4xx_hal_tim.h                                           --
--   @author  MCD Application Team                                          --
--   @version V1.1.0                                                        --
--   @date    19-June-2014                                                  --
--   @brief   Header file of DMA HAL module.                                --
--                                                                          --
--   COPYRIGHT(c) 2014 STMicroelectronics                                   --
------------------------------------------------------------------------------

--  This file provides definitions for the timers on the STM32F4 (ARM Cortex
--  M4F) microcontrollers from ST Microelectronics.

pragma SPARK_Mode (Off);  --  temporary issue with Vol'Address (O916-012)
pragma Restrictions (No_Elaboration_Code);

with System;  use System;

package STM32F4.Timers is

   type Timer is limited private;

   procedure Enable (This : in out Timer)
     with Post => Enabled (This);

   procedure Disable (This : in out Timer)
     with Post => (if No_Outputs_Enabled (This) then not Enabled (This));

   function Enabled (This : Timer) return Boolean;

   --  The Configure routines are overloaded for the sake of
   --  additional timer-class specific parameters.

   procedure Configure
     (This      : in out Timer;
      Prescaler : Half_Word;
      Period    : Half_Word)
     with
       Post => Current_Prescaler (This) = Prescaler and
               Current_Autoreload (This) = Period;

   procedure Set_Counter (This : in out Timer;  Value : Half_Word)
     with Post => Current_Counter (This) = Word (Value);

   procedure Set_Counter (This : in out Timer;  Value : Word)
     with
       Pre  => Has_32bit_Counter (This),
       Post => Current_Counter (This) = Value;

   function Current_Counter (This : Timer) return Word;
   --  For those timers that actually have a 32-bit counter this function will
   --  return the full word value. For the other timers, the upper half-word of
   --  the result will be all zeros so in effect the result will be a half-word
   --  value.

   procedure Set_Autoreload (This : in out Timer;  Value : Half_Word)
     with Post => Current_Autoreload (This) = Value;

   function Current_Autoreload (This : Timer) return Half_Word;
   --  Returns the value of the timer's Auto Reload Register (ARR)

   type Timer_Clock_Divisor is (Div1, Div2, Div4);

   procedure Set_Clock_Division
     (This  : in out Timer;
      Value : Timer_Clock_Divisor)
     with
       Pre  => not Basic_Timer (This),
       Post => Current_Clock_Division (This) = Value;

   function Current_Clock_Division (This : Timer) return Timer_Clock_Divisor;

   type Timer_Counter_Alignment_Mode is
     (Up, Down, Center_Aligned1, Center_Aligned2, Center_Aligned3);
   --  We combine the up-down direction and the center-aligned mode selection
   --  into a single type because the two are interdependent and we don't want
   --  the user to have to remember to set the direction when not using one
   --  of the center-aligned choices. The discontiguous binary values used to
   --  represent the enumerals reflect the combination of the adjacent fields
   --  within the timer representation.

   for Timer_Counter_Alignment_Mode use
     (Up              => 2#000#,
      Down            => 2#001#,
      Center_Aligned1 => 2#010#,
      Center_Aligned2 => 2#100#,
      Center_Aligned3 => 2#110#);

   procedure Set_Counter_Mode
     (This  : in out Timer;
      Value : Timer_Counter_Alignment_Mode)
     with Post => Current_Counter_Mode (This) = Value;

   function Current_Counter_Mode
     (This : Timer)
      return Timer_Counter_Alignment_Mode;
   --  Note that the basic timers only count up.

   procedure Configure
     (This          : in out Timer;
      Prescaler     : Half_Word;
      Period        : Half_Word;
      Clock_Divisor : Timer_Clock_Divisor;
      Counter_Mode  : Timer_Counter_Alignment_Mode)
     with
       Pre  => not Basic_Timer (This),
       Post => Current_Prescaler (This) = Prescaler and
               Current_Clock_Division (This) = Clock_Divisor and
               Current_Counter_Mode (This) = Counter_Mode and
               Current_Autoreload (This) = Period;

   type Timer_Prescaler_Reload_Mode is (Update, Immediate);

   procedure Configure_Prescaler
     (This        : in out Timer;
      Prescaler   : Half_Word;
      Reload_Mode : Timer_Prescaler_Reload_Mode)
     with Post => Current_Prescaler (This) = Prescaler;

   function Current_Prescaler (This : Timer) return Half_Word;

   procedure Set_UpdateDisable
     (This : in out Timer;
      To   : Boolean);

   type Timer_Update_Source is (Global, Regular);

   procedure Set_UpdateRequest
     (This   : in out Timer;
      Source : Timer_Update_Source);

   procedure Set_Autoreload_Preload
     (This : in out Timer;
      To   : Boolean);

   type Timer_One_Pulse_Mode is (Repetitive, Single);

   procedure Select_One_Pulse_Mode
     (This : in out Timer;
      Mode : Timer_One_Pulse_Mode)
     with Post => (if Mode = Single then not Enabled (This));

   ----------------------------------------------------------------------------

   --  Interrupts, DMA, Flags Management --------------------------------------

   ----------------------------------------------------------------------------

   type Timer_Interrupt is
     (Timer_Update_Interrupt,
      Timer_CC1_Interrupt,
      Timer_CC2_Interrupt,
      Timer_CC3_Interrupt,
      Timer_CC4_Interrupt,
      Timer_COM_Interrupt,
      Timer_Trigger_Interrupt,
      Timer_Break_Interrupt);

   for Timer_Interrupt use
     (Timer_Update_Interrupt  => 2#00000001#,
      Timer_CC1_Interrupt     => 2#00000010#,
      Timer_CC2_Interrupt     => 2#00000100#,
      Timer_CC3_Interrupt     => 2#00001000#,
      Timer_CC4_Interrupt     => 2#00010000#,
      Timer_COM_Interrupt     => 2#00100000#,
      Timer_Trigger_Interrupt => 2#01000000#,
      Timer_Break_Interrupt   => 2#10000000#);

   procedure Enable_Interrupt
     (This   : in out Timer;
      Source : Timer_Interrupt)
     with
       Pre =>
         (if Basic_Timer (This) then Source = Timer_Update_Interrupt) and
         (if Source in Timer_COM_Interrupt | Timer_Break_Interrupt
            then Advanced_Timer (This)),
       Post => Interrupt_Enabled (This, Source);

   type Timer_Interrupt_List is array (Positive range <>) of Timer_Interrupt;

   procedure Enable_Interrupt
     (This    : in out Timer;
      Sources : Timer_Interrupt_List)
     with
       Pre =>
         (for all Source of Sources =>
           (if Basic_Timer (This) then Source = Timer_Update_Interrupt) and
           (if Source in Timer_COM_Interrupt | Timer_Break_Interrupt
              then Advanced_Timer (This))),
       Post => (for all Source of Sources => Interrupt_Enabled (This, Source));

   procedure Disable_Interrupt
     (This   : in out Timer;
      Source : Timer_Interrupt)
     with
       Pre =>
         (if Basic_Timer (This) then Source = Timer_Update_Interrupt) and
         (if Source in Timer_COM_Interrupt | Timer_Break_Interrupt
            then Advanced_Timer (This)),
       Post => not Interrupt_Enabled (This, Source);

   procedure Clear_Pending_Interrupt
     (This   : in out Timer;
      Source : Timer_Interrupt)
     with Pre =>
       (if Basic_Timer (This) then Source = Timer_Update_Interrupt) and
       (if Source in Timer_COM_Interrupt | Timer_Break_Interrupt
          then Advanced_Timer (This));

   function Interrupt_Enabled
     (This   : Timer;
      Source : Timer_Interrupt)
      return Boolean
     with Pre =>
       (if Basic_Timer (This) then Source = Timer_Update_Interrupt) and
       (if Source in Timer_COM_Interrupt | Timer_Break_Interrupt
          then Advanced_Timer (This));

   type Timer_Event_Source is
     (Event_Source_Update,
      Event_Source_CC1,
      Event_Source_CC2,
      Event_Source_CC3,
      Event_Source_CC4,
      Event_Source_COM,
      Event_Source_Trigger,
      Event_Source_Break);

   for Timer_Event_Source use
     (Event_Source_Update  => 16#0001#,
      Event_Source_CC1     => 16#0002#,
      Event_Source_CC2     => 16#0004#,
      Event_Source_CC3     => 16#0008#,
      Event_Source_CC4     => 16#0010#,
      Event_Source_COM     => 16#0020#,
      Event_Source_Trigger => 16#0040#,
      Event_Source_Break   => 16#0080#);
   --  TODO: consider alternative to bit-masks

   procedure Generate_Event
     (This   : in out Timer;
      Source : Timer_Event_Source)
     with
       Pre =>
         (if Basic_Timer (This) then Source = Event_Source_Update) and
         (if Source in Event_Source_COM | Event_Source_Break
            then Advanced_Timer (This));

   type Timer_Status_Flag is
     (Timer_Update_Indicated,
      Timer_CC1_Indicated,
      Timer_CC2_Indicated,
      Timer_CC3_Indicated,
      Timer_CC4_Indicated,
      Timer_COM_Indicated,
      Timer_Trigger_Indicated,
      Timer_Break_Indicated,
      Timer_CC1OF_Indicated,
      Timer_CC2OF_Indicated,
      Timer_CC3OF_Indicated,
      Timer_CC4OF_Indicated);

   for Timer_Status_Flag use
     (Timer_Update_Indicated  => 2#000000000001#,
      Timer_CC1_Indicated     => 2#000000000010#,
      Timer_CC2_Indicated     => 2#000000000100#,
      Timer_CC3_Indicated     => 2#000000001000#,
      Timer_CC4_Indicated     => 2#000000010000#,
      Timer_COM_Indicated     => 2#000000100000#,
      Timer_Trigger_Indicated => 2#000001000000#,
      Timer_Break_Indicated   => 2#000010000000#,
      Timer_CC1OF_Indicated   => 2#000100000000#,
      Timer_CC2OF_Indicated   => 2#001000000000#,
      Timer_CC3OF_Indicated   => 2#010000000000#,
      Timer_CC4OF_Indicated   => 2#100000000000#);

   function Status
     (This : Timer;
      Flag : Timer_Status_Flag)
      return Boolean
     with Pre =>
       (if Basic_Timer (This) then Flag = Timer_Update_Indicated) and
       (if Flag in Timer_COM_Indicated | Timer_Break_Indicated
          then Advanced_Timer (This));

   procedure Clear_Status
     (This : in out Timer;
      Flag : Timer_Status_Flag)
     with
       Pre =>
         (if Basic_Timer (This) then Flag = Timer_Update_Indicated) and
         (if Flag in Timer_COM_Indicated | Timer_Break_Indicated
            then Advanced_Timer (This)),
       Post =>
         not Status (This, Flag);

   type Timer_DMA_Source is
     (Timer_DMA_Update,
      Timer_DMA_CC1,
      Timer_DMA_CC2,
      Timer_DMA_CC3,
      Timer_DMA_CC4,
      Timer_DMA_COM,
      Timer_DMA_Trigger);

   for Timer_DMA_Source use
     (Timer_DMA_Update  => 2#00000001_00000000#,
      Timer_DMA_CC1     => 2#00000010_00000000#,
      Timer_DMA_CC2     => 2#00000100_00000000#,
      Timer_DMA_CC3     => 2#00001000_00000000#,
      Timer_DMA_CC4     => 2#00010000_00000000#,
      Timer_DMA_COM     => 2#00100000_00000000#,
      Timer_DMA_Trigger => 2#01000000_00000000#);
   --  TODO: consider using a packed array of booleans in the SR representation
   --  instead of bit-patterns, thereby obviating this rep clause

   procedure Enable_DMA_Source
     (This   : in out Timer;
      Source : Timer_DMA_Source)
     with
       Pre =>
         ((if Basic_Timer (This) then Source = Timer_DMA_Update) and
         (if Source in Timer_DMA_COM | Timer_DMA_Trigger then Advanced_Timer (This)))
         or else DMA_Supported (This),
       Post =>
         DMA_Source_Enabled (This, Source);

   procedure Disable_DMA_Source
     (This   : in out Timer;
      Source : Timer_DMA_Source)
     with
       Pre =>
         ((if Basic_Timer (This) then Source = Timer_DMA_Update) and
         (if Source in Timer_DMA_COM | Timer_DMA_Trigger then Advanced_Timer (This)))
         or else DMA_Supported (This),
       Post =>
         not DMA_Source_Enabled (This, Source);

   function DMA_Source_Enabled
     (This   : Timer;
      Source : Timer_DMA_Source)
     return Boolean
     with
       Pre =>
         ((if Basic_Timer (This) then Source = Timer_DMA_Update) and
         (if Source in Timer_DMA_COM | Timer_DMA_Trigger then Advanced_Timer (This)))
         or else DMA_Supported (This);

   type Timer_DMA_Burst_Length is
     (DMA_Burst_Length_1,
      DMA_Burst_Length_2,
      DMA_Burst_Length_3,
      DMA_Burst_Length_4,
      DMA_Burst_Length_5,
      DMA_Burst_Length_6,
      DMA_Burst_Length_7,
      DMA_Burst_Length_8,
      DMA_Burst_Length_9,
      DMA_Burst_Length_10,
      DMA_Burst_Length_11,
      DMA_Burst_Length_12,
      DMA_Burst_Length_13,
      DMA_Burst_Length_14,
      DMA_Burst_Length_15,
      DMA_Burst_Length_16,
      DMA_Burst_Length_17,
      DMA_Burst_Length_18);

   type Timer_DMA_Base_Address is
     (DMA_Base_CR1,
      DMA_Base_CR2,
      DMA_Base_SMCR,
      DMA_Base_DIER,
      DMA_Base_SR,
      DMA_Base_EGR,
      DMA_Base_CCMR1,
      DMA_Base_CCMR2,
      DMA_Base_CCER,
      DMA_Base_CNT,
      DMA_Base_PSC,
      DMA_Base_ARR,
      DMA_Base_RCR,
      DMA_Base_CCR1,
      DMA_Base_CCR2,
      DMA_Base_CCR3,
      DMA_Base_CCR4,
      DMA_Base_BDTR,
      DMA_Base_DCR,
      DMA_Base_OR);

   procedure Configure_DMA
     (This         : in out Timer;
      Base_Address : Timer_DMA_Base_Address;
      Burst_Length : Timer_DMA_Burst_Length);

   procedure Enable_Capture_Compare_DMA
     (This : in out Timer);

   procedure Disable_Capture_Compare_DMA
     (This : in out Timer);

   ----------------------------------------------------------------------------

   --  Output Compare Management ----------------------------------------------

   ----------------------------------------------------------------------------

   type Timer_Channel is (Channel_1, Channel_2, Channel_3, Channel_4);

   procedure Enable_Channel
     (This    : in out Timer;
      Channel : Timer_Channel)
     with
       Pre  => not Basic_Timer (This),
       Post => Channel_Enabled (This, Channel);

   procedure Disable_Channel
     (This    : in out Timer;
      Channel : Timer_Channel)
     with
       Pre  => not Basic_Timer (This),
       Post => not Channel_Enabled (This, Channel);

   function Channel_Enabled
     (This : Timer;  Channel : Timer_Channel)
      return Boolean;

   procedure Enable_Complementary_Channel
     (This    : in out Timer;
      Channel : Timer_Channel)
     with
       Pre  => Complementary_Outputs_Supported (This, Channel),
       Post => Complementary_Channel_Enabled (This, Channel);

   procedure Disable_Complementary_Channel
     (This    : in out Timer;
      Channel : Timer_Channel)
     with
       Pre  => Complementary_Outputs_Supported (This, Channel),
       Post => not Complementary_Channel_Enabled (This, Channel);

   function Complementary_Channel_Enabled
     (This : Timer;  Channel : Timer_Channel)
      return Boolean
     with Pre => Complementary_Outputs_Supported (This, Channel);

   Timer_Channel_Access_Error : exception;
   --  Raised when accessing a given channel configuration with the wrong view:
   --  as an input when it is set to be an output, and vice versa

   type Timer_Output_Compare_And_PWM_Mode is
     (Timing,
      Active,
      Inactive,
      Toggle,
      Force_Inactive,
      Force_Active,
      PWM1,
      PWM2);

   type Timer_Capture_Compare_State is (Disable, Enable);

   type Timer_Output_Compare_Polarity is (High, Low);

   procedure Configure_Channel_Output
     (This     : in out Timer;
      Channel  : Timer_Channel;
      Mode     : Timer_Output_Compare_And_PWM_Mode;
      State    : Timer_Capture_Compare_State;
      Pulse    : Word;
      Polarity : Timer_Output_Compare_Polarity)
     with
       Pre => (CC_Channel_Exists (This, Channel) and
               Specific_Channel_Output_Supported (This, Channel))  and
               (if not Has_32bit_CC_Values (This) then Pulse <= 16#FFFF#),
       Post => (if State = Enable
                  then Channel_Enabled (This, Channel)
                  else not Channel_Enabled (This, Channel));

   procedure Set_Compare_Value
     (This       : in out Timer;
      Channel    : Timer_Channel;
      Word_Value : Word)
     with
       Pre  => Has_32bit_CC_Values (This),
       Post => Current_Capture_Value (This, Channel) = Word_Value;

   procedure Set_Compare_Value
     (This    : in out Timer;
      Channel : Timer_Channel;
      Value   : Half_Word)
     with
       Pre  => CC_Channel_Exists (This, Channel),
       Post => Current_Capture_Value (This, Channel) = Value;

   type Timer_Capture_Compare_Modes is
     (Output, Direct_TI, Indirect_TI, TRC);

   function Current_Capture_Compare_Mode
     (This    : Timer;
      Channel : Timer_Channel)
      return Timer_Capture_Compare_Modes;

   --  A convenience routine that sets the capture/compare selection to be that
   --  of a single channel output and assigns all the controls of that output,
   --  as an alternative to calling the individual routines. Does not raise the
   --  access error exception because it explicitly sets the mode to Output.
   procedure Set_Single_Output
     (This             : in out Timer;
      Channel          : Timer_Channel;
      Mode             : Timer_Output_Compare_And_PWM_Mode;
      OC_Clear_Enabled : Boolean;
      Preload_Enabled  : Boolean;
      Fast_Enabled     : Boolean)
     with
       Pre => CC_Channel_Exists (This, Channel),
       Post => Current_Capture_Compare_Mode (This, Channel) = Output;

   procedure Set_Output_Compare_Mode
     (This     : in out Timer;
      Channel  : Timer_Channel;
      Mode     : Timer_Output_Compare_And_PWM_Mode)
     with
       Pre => (not Basic_Timer (This)) and
              (if Current_Capture_Compare_Mode (This, Channel) /= Output
                 then raise Timer_Channel_Access_Error);

   procedure Set_Output_Preload_Enable
     (This    : in out Timer;
      Channel : Timer_Channel;
      Enabled : Boolean)
     with
       Pre => CC_Channel_Exists (This, Channel) and
              (if Current_Capture_Compare_Mode (This, Channel) /= Output
                 then raise Timer_Channel_Access_Error);

   procedure Set_Output_Fast_Enable
     (This    : in out Timer;
      Channel : Timer_Channel;
      Enabled : Boolean)
     with
       Pre => CC_Channel_Exists (This, Channel) and
              (if Current_Capture_Compare_Mode (This, Channel) /= Output
                 then raise Timer_Channel_Access_Error);

   procedure Set_Clear_Control
     (This    : in out Timer;
      Channel : Timer_Channel;
      Enabled : Boolean)
     with
       Pre => CC_Channel_Exists (This, Channel) and
              (if Current_Capture_Compare_Mode (This, Channel) /= Output
                 then raise Timer_Channel_Access_Error);

   procedure Set_Output_Forced_Action
     (This    : in out Timer;
      Channel : Timer_Channel;
      Active  : Boolean)
     with
       Pre => CC_Channel_Exists (This, Channel) and
              (if Current_Capture_Compare_Mode (This, Channel) /= Output
                 then raise Timer_Channel_Access_Error);

   procedure Set_Output_Polarity
     (This     : in out Timer;
      Channel  : Timer_Channel;
      Polarity : Timer_Output_Compare_Polarity)
     with
       Pre => not Basic_Timer (This);

   procedure Set_Output_Complementary_Polarity
     (This     : in out Timer;
      Channel  : Timer_Channel;
      Polarity : Timer_Output_Compare_Polarity)
     with
       Pre => Advanced_Timer (This);

   --  Indicates whether all outputs are disabled for all channels of the given
   --  timer.
   function No_Outputs_Enabled (This : Timer) return Boolean;

   ----------------------------------------------------------------------------

   --  Input Capture Management -----------------------------------------------

   ----------------------------------------------------------------------------

   type Timer_Input_Capture_Filter is mod 16;

   type Timer_Input_Capture_Polarity is (Rising, Falling, Both_Edges);

   subtype Timer_Input_Capture_Selection is Timer_Capture_Compare_Modes
     range Direct_TI .. TRC;

   type Timer_Input_Capture_Prescaler is
     (Div1,   -- Capture performed each time an edge is detected on input
      Div2,   -- Capture performed once every 2 events
      Div4,   -- Capture performed once every 4 events
      Div8);  -- Capture performed once every 8 events

   procedure Configure_Channel_Input
     (This      : in out Timer;
      Channel   : Timer_Channel;
      Polarity  : Timer_Input_Capture_Polarity;
      Selection : Timer_Input_Capture_Selection;
      Prescaler : Timer_Input_Capture_Prescaler;
      Filter    : Timer_Input_Capture_Filter)
     with
       Pre  => CC_Channel_Exists (This, Channel) and
               (if Filter > 7 then Advanced_Timer (This)),
       Post => Channel_Enabled (This, Channel) and
               Current_Capture_Compare_Mode (This, Channel) = Selection;

   procedure Configure_Channel_Input_PWM
     (This      : in out Timer;
      Channel   : Timer_Channel;
      Selection : Timer_Input_Capture_Selection;
      Polarity  : Timer_Input_Capture_Polarity;
      Prescaler : Timer_Input_Capture_Prescaler;
      Filter    : Timer_Input_Capture_Filter)
     with
       Pre  => Has_At_Least_2_CC_Channels (This) and
               Channel in Channel_1 | Channel_2,
       Post => Channel_Enabled (This, Channel) and
               Current_Capture_Compare_Mode (This, Channel) = Selection and
               Current_Input_Prescaler (This, Channel) = Prescaler;

   procedure Set_Input_Prescaler
     (This    : in out Timer;
      Channel : Timer_Channel;
      Value   : Timer_Input_Capture_Prescaler)
     with
       Pre  => not Basic_Timer (This) and
               Current_Capture_Compare_Mode (This, Channel) /= Output,
       Post => Current_Input_Prescaler (This, Channel) = Value;

   function Current_Input_Prescaler
     (This    : Timer;
      Channel : Timer_Channel)
      return Timer_Input_Capture_Prescaler;

   function Current_Capture_Value
     (This    : Timer;
      Channel : Timer_Channel)
      return Word;
   --  Reading the upper reserved area of the CCR register does no harm when
   --  the timer does not support 32-bit CC registers so we do not protect
   --  this function with a precondition.

   function Current_Capture_Value
     (This    : Timer;
      Channel : Timer_Channel)
      return Half_Word;

   ----------------------------------------------------------------------------

   --  Advanced control timers ------------------------------------------------

   ----------------------------------------------------------------------------

   procedure Enable_Main_Output (This : in out Timer)
     with
       Pre  => Advanced_Timer (This),
       Post => Main_Output_Enabled (This);

   procedure Disable_Main_Output (This : in out Timer)
     with
       Pre  => Advanced_Timer (This),
       Post => (if No_Outputs_Enabled (This) then not Main_Output_Enabled (This));

   function Main_Output_Enabled (This : Timer) return Boolean;

   procedure Configure
     (This          : in out Timer;
      Prescaler     : Half_Word;
      Period        : Half_Word;
      Clock_Divisor : Timer_Clock_Divisor;
      Counter_Mode  : Timer_Counter_Alignment_Mode;
      Repetitions   : Byte)
     with
       Pre  => Advanced_Timer (This),
       Post => Current_Prescaler (This) = Prescaler and
               Current_Autoreload (This) = Period;

   procedure Configure_Channel_Output
     (This                     : in out Timer;
      Channel                  : Timer_Channel;
      Mode                     : Timer_Output_Compare_And_PWM_Mode;
      State                    : Timer_Capture_Compare_State;
      Pulse                    : Word;
      Polarity                 : Timer_Output_Compare_Polarity;
      Idle_State               : Timer_Capture_Compare_State;
      Complementary_Polarity   : Timer_Output_Compare_Polarity;
      Complementary_Idle_State : Timer_Capture_Compare_State)
     with
       Pre  => Advanced_Timer (This) and
               (if not Has_32bit_CC_Values (This) then Pulse <= 16#FFFF#),
       Post => (if State = Enable
                  then Channel_Enabled (This, Channel)
                  else not Channel_Enabled (This, Channel));

   procedure Enable_CC_Preload_Control (This : in out Timer)
     with Pre => Advanced_Timer (This);

   procedure Disable_CC_Preload_Control (This : in out Timer)
     with Pre => Advanced_Timer (This);

   procedure Select_Commutation (This : in out Timer)
     with Pre => Advanced_Timer (This);

   procedure Deselect_Commutation (This : in out Timer)
     with Pre => Advanced_Timer (This);

   type Timer_Break_Polarity is (Low, High);

   type Timer_Lock_Level is (Off, Level_1, Level_2, Level_3);

   procedure Configure_BDTR
     (This                          : in out Timer;
      Automatic_Output_Enabled      : Boolean;
      Break_Polarity                : Timer_Break_Polarity;
      Break_Enabled                 : Boolean;
      Off_State_Selection_Run_Mode  : Bits_1;
      Off_State_Selection_Idle_Mode : Bits_1;
      Lock_Configuration            : Timer_Lock_Level;
      Deadtime_Generator            : Byte)
     with Pre => Advanced_Timer (This);

   ----------------------------------------------------------------------------

   --  Synchronization Management ---------------------------------------------

   ----------------------------------------------------------------------------

   type Timer_Trigger_Input_Source is
     (Internal_Trigger_0,      -- ITR0
      Internal_Trigger_1,      -- ITR1
      Internal_Trigger_2,      -- ITR2
      Internal_Trigger_3,      -- ITR3
      TI1_Edge_Detector,       -- TI1F_ED
      Filtered_Timer_Input_1,  -- TI1FP1
      Filtered_Timer_Input_2,  -- TI2FP2
      External_Trigger_Input); -- ETRF

   procedure Select_Input_Trigger
     (This   : in out Timer;
      Source : Timer_Trigger_Input_Source)
     with Pre => not Basic_Timer (This);

   type Timer_Trigger_Output_Source is
     (Reset,
      Enable,
      Update,
      OC1,
      OC1Ref,
      OC2Ref,
      OC3Ref,
      OC4Ref);

   procedure Select_Output_Trigger
     (This   : in out Timer;
      Source : Timer_Trigger_Output_Source)
     with Pre => Trigger_Output_Selectable (This);  -- any of Timer 1 .. 8

   type Timer_Slave_Mode is
     (Disabled,
      -- counter counts up/down on TI1 edge
      Encoder_Mode_TI1,
      -- counter counts up/down on TI2 edge
      Encoder_Mode_TI2,
      -- counter counts up/down on both TI1 & TI2 edges
      Encoder_Mode_TI1_TI2,
      Reset,
      Gated,
      Trigger,
      External_1);

   procedure Select_Slave_Mode
     (This : in out Timer;
      Mode : Timer_Slave_Mode)
     with Pre => Slave_Mode_Supported (This);

   procedure Enable_Master_Slave_Mode (This : in out Timer)
     with Pre => Slave_Mode_Supported (This);

   procedure Disable_Master_Slave_Mode (This : in out Timer)
     with Pre => Slave_Mode_Supported (This);

   type Timer_External_Trigger_Polarity is (Inverted, Noninverted);

   type Timer_External_Trigger_Prescaler is
     (Off,
      Div2,
      Div4,
      Div8);

   type Timer_External_Trigger_Filter is mod 16;

   procedure Configure_External_Trigger
     (This      : in out Timer;
      Polarity  : Timer_External_Trigger_Polarity;
      Prescaler : Timer_External_Trigger_Prescaler;
      Filter    : Timer_External_Trigger_Filter)
     with Pre => External_Trigger_Supported (This);

   ----------------------------------------------------------------------------

   --  Clocks Management ------------------------------------------------------

   ----------------------------------------------------------------------------

   procedure Select_Internal_Clock
     (This : in out Timer)
      renames Disable_Master_Slave_Mode;

   subtype Timer_Internal_Trigger_Source is Timer_Trigger_Input_Source
      range Internal_Trigger_0 .. Internal_Trigger_3;

   procedure Configure_As_External_Clock
     (This   : in out Timer;
      Source : Timer_Internal_Trigger_Source)
     with Pre => Clock_Management_Supported (This);

   subtype Timer_External_Clock_Source is Timer_Trigger_Input_Source
      range TI1_Edge_Detector .. Filtered_Timer_Input_2;

   procedure Configure_As_External_Clock
     (This     : in out Timer;
      Source   : Timer_External_Clock_Source;
      Polarity : Timer_Input_Capture_Polarity;
      Filter   : Timer_Input_Capture_Filter)
     with Pre => not Basic_Timer (This);

   procedure Configure_External_Clock_Mode1
     (This      : in out Timer;
      Polarity  : Timer_External_Trigger_Polarity;
      Prescaler : Timer_External_Trigger_Prescaler;
      Filter    : Timer_External_Trigger_Filter)
     with Pre => External_Trigger_Supported (This);

   procedure Configure_External_Clock_Mode2
     (This      : in out Timer;
      Polarity  : Timer_External_Trigger_Polarity;
      Prescaler : Timer_External_Trigger_Prescaler;
      Filter    : Timer_External_Trigger_Filter)
     with Pre => External_Trigger_Supported (This);

   ----------------------------------------------------------------------------

   --  Misc functions ---------------------------------------------------------

   ----------------------------------------------------------------------------

   subtype Timer_Encoder_Mode is
     Timer_Slave_Mode range Encoder_Mode_TI1 .. Encoder_Mode_TI1_TI2;

   procedure Configure_Encoder_Interface
     (This         : in out Timer;
      Mode         : Timer_Encoder_Mode;
      IC1_Polarity : Timer_Input_Capture_Polarity;
      IC2_Polarity : Timer_Input_Capture_Polarity)
     with Pre => Has_At_Least_2_CC_Channels (This);

   procedure Enable_Hall_Sensor
     (This : in out Timer)
     with Pre => Hall_Sensor_Supported (This);

   procedure Disable_Hall_Sensor
     (This : in out Timer)
     with Pre => Hall_Sensor_Supported (This);

   type Timer_2_Remapping_Options is --  see RM pg 632
     (TIM2_TIM8_TRGO,
      TIM2_ETH_PTP,
      TIM2_USBFS_SOF,
      TIM2_USBHS_SOF);

   procedure Configure_Timer_2_Remapping
     (This   : in out Timer;
      Option : Timer_2_Remapping_Options)
     with Pre => This'Address = System'To_Address (TIM2_Base);

   type Timer_5_Remapping_Options is --  see RM pg 633
     (TIM5_GPIO,
      TIM5_LSI,
      TIM5_LSE,
      TIM5_RTC);

   procedure Configure_Timer_5_Remapping
     (This   : in out Timer;
      Option : Timer_5_Remapping_Options)
     with Pre => This'Address = System'To_Address (TIM5_Base);

   type Timer_11_Remapping_Options is
     (TIM11_GPIO,
      TIM11_HSE);

   for Timer_11_Remapping_Options use  -- per RM page 676
     (TIM11_GPIO => 0,
      TIM11_HSE  => 2);

   procedure Configure_Timer_11_Remapping
     (This   : in out Timer;
      Option : Timer_11_Remapping_Options)
     with Pre => This'Address = System'To_Address (TIM11_Base);

   ----------------------------------------------------------------------------

   --  Classifier functions ---------------------------------------------------

   ----------------------------------------------------------------------------

   --  Timers 6 and 7
   function Basic_Timer (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM6_Base) or
      This'Address = System'To_Address (TIM7_Base));

   --  Timers 1 and 8
   function Advanced_Timer (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 2 and 5
   function Has_32bit_Counter (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM2_Base) or
      --  The RM register map for timers 2 through 5, pg 634, indicates that
      --  only timer 2 and timer 5 actually have the upper half of the counter
      --  available, and that the others must keep it reserved. This would
      --  appear to contradict the text in the introduction to those timers,
      --  but section 18.2 indicates the restriction explicitly.
      This'Address = System'To_Address (TIM5_Base));

   --  Timers 2 and 5
   function Has_32bit_CC_Values (This : Timer) return Boolean
      renames Has_32bit_Counter;

   --  Timers 1 .. 8
   function Trigger_Output_Selectable (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM6_Base) or
      This'Address = System'To_Address (TIM7_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 1 .. 5, 8, 9, 12
   function Has_At_Least_2_CC_Channels (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base) or
      This'Address = System'To_Address (TIM9_Base) or
      This'Address = System'To_Address (TIM12_Base));

   --  Timers 1 .. 5, 8
   function Hall_Sensor_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base));

  --  Timers 1 .. 5, 8, 9, 12
   function Clock_Management_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base) or
      This'Address = System'To_Address (TIM9_Base) or
      This'Address = System'To_Address (TIM12_Base));

   --  Timers 1 .. 5, 8
   function Has_At_Least_3_CC_Channels (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 1 .. 5, 8
   function Has_At_Least_4_CC_Channels (This : Timer) return Boolean
     renames Has_At_Least_3_CC_Channels;

   --  Not all timers have four channels available for capture/compare
   function CC_Channel_Exists (This : Timer; Channel : Timer_Channel) return Boolean is
     ((if Channel = Channel_1 then not Basic_Timer (This))            or
      (if Channel = Channel_2 then Has_At_Least_2_CC_Channels (This)) or
      (if Channel = Channel_3 then Has_At_Least_3_CC_Channels (This)) or
      (if Channel = Channel_4 then Has_At_Least_4_CC_Channels (This)));

   --  Timers 1 .. 5, 8
   function Input_XOR_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 1 .. 8
   function DMA_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM6_Base) or
      This'Address = System'To_Address (TIM7_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 1 .. 5, 8, 9, 12
   function Slave_Mode_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base) or
      This'Address = System'To_Address (TIM9_Base) or
      This'Address = System'To_Address (TIM12_Base));

   --  Timers 1 .. 5, 8
   function External_Trigger_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base));

   --  Timers 2, 5, 11
   function Remapping_Capability_Supported (This : Timer) return Boolean is
     (This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM11_Base));

   --  Not all timers support output on all channels
   function Specific_Channel_Output_Supported
     (This : Timer;  Channel : Timer_Channel)
      return Boolean
   is
     (This'Address = System'To_Address (TIM1_Base) or
      This'Address = System'To_Address (TIM2_Base) or
      This'Address = System'To_Address (TIM3_Base) or
      This'Address = System'To_Address (TIM4_Base) or
      This'Address = System'To_Address (TIM5_Base) or
      This'Address = System'To_Address (TIM8_Base)
      --  all the above can be with any of the four channels
      or
      (This'Address = System'To_Address (TIM9_Base) and
       Channel in Channel_1 | Channel_2)
      or
      (This'Address = System'To_Address (TIM10_Base) and
       Channel = Channel_1)
      or
      (This'Address = System'To_Address (TIM11_Base) and
       Channel = Channel_1)
      or
      (This'Address = System'To_Address (TIM12_Base) and
       Channel in Channel_1 | Channel_2)
      or
      (This'Address = System'To_Address (TIM13_Base) and
       Channel = Channel_1)
      or
      (This'Address = System'To_Address (TIM14_Base) and
       Channel = Channel_1));

   --  Timers 1 and 8, channels 1 .. 3
   function Complementary_Outputs_Supported
     (This : Timer;  Channel : Timer_Channel)
      return Boolean
   is
     ((This'Address = System'To_Address (TIM1_Base) or
       This'Address = System'To_Address (TIM8_Base)) and
       Channel in Channel_1 | Channel_2 | Channel_3);

private

   type TIMx_CR1 is record
      Reserved              : Bits_6;
      Clock_Division        : Timer_Clock_Divisor;
      ARPE                  : Boolean;  -- Auto-reload preload enable
      Mode_And_Dir          : Timer_Counter_Alignment_Mode;
      One_Pulse_Mode        : Timer_One_Pulse_Mode;
      Update_Request_Source : Boolean;
      Update_Disable        : Boolean;
      Timer_Enabled         : Boolean;
   end record with Volatile_Full_Access, Size => 32;

   for TIMx_CR1 use record
      Reserved              at 0 range 10 .. 15;
      Clock_Division        at 0 range  8 .. 9;
      ARPE                  at 0 range  7 .. 7;
      Mode_And_Dir          at 0 range  4 .. 6;
      One_Pulse_Mode        at 0 range  3 .. 3;
      Update_Request_Source at 0 range  2 .. 2;
      Update_Disable        at 0 range  1 .. 1;
      Timer_Enabled         at 0 range  0 .. 0;
   end record;

   ------------------------  representation for CR2  --------------------------

   type TIMx_CR2 is record
      Reserved0                                 : Half_Word;
      Reserved1                                 : Bits_1;
      Channel_4_Output_Idle_State               : Timer_Capture_Compare_State;
      Channel_3_Complementary_Output_Idle_State : Timer_Capture_Compare_State;
      Channel_3_Output_Idle_State               : Timer_Capture_Compare_State;
      Channel_2_Complementary_Output_Idle_State : Timer_Capture_Compare_State;
      Channel_2_Output_Idle_State               : Timer_Capture_Compare_State;
      Channel_1_Complementary_Output_Idle_State : Timer_Capture_Compare_State;
      Channel_1_Output_Idle_State               : Timer_Capture_Compare_State;
      TI1_Selection                             : Boolean;
      Master_Mode_Selection                     : Timer_Trigger_Output_Source;
      Capture_Compare_DMA_Selection             : Boolean;
      Capture_Compare_Control_Update_Selection  : Boolean;
      Reserved2                                 : Bits_1;
      Capture_Compare_Preloaded_Control         : Boolean;
   end record with Volatile_Full_Access, Size => 32;

   for TIMx_CR2 use record
      Reserved0                                 at 0 range 16 .. 31;
      Reserved1                                 at 0 range 15 .. 15;
      Channel_4_Output_Idle_State               at 0 range 14 .. 14;
      Channel_3_Complementary_Output_Idle_State at 0 range 13 .. 13;
      Channel_3_Output_Idle_State               at 0 range 12 .. 12;
      Channel_2_Complementary_Output_Idle_State at 0 range 11 .. 11;
      Channel_2_Output_Idle_State               at 0 range 10 .. 10;
      Channel_1_Complementary_Output_Idle_State at 0 range  9 .. 9;
      Channel_1_Output_Idle_State               at 0 range  8 .. 8;
      TI1_Selection                             at 0 range  7 .. 7;
      Master_Mode_Selection                     at 0 range  4 .. 6;
      Capture_Compare_DMA_Selection             at 0 range  3 .. 3;
      Capture_Compare_Control_Update_Selection  at 0 range  2 .. 2;
      Reserved2                                 at 0 range  1 .. 1;
      Capture_Compare_Preloaded_Control         at 0 range  0 .. 0;
   end record;

   ------------  representation for slave mode control register  --------------

   type TIMx_SMCR is record
      Reserved0                  : Half_Word;
      External_Trigger_Polarity  : Timer_External_Trigger_Polarity;
      External_Clock_Enable      : Boolean;
      External_Trigger_Prescaler : Timer_External_Trigger_Prescaler;
      External_Trigger_Filter    : Timer_External_Trigger_Filter;
      Master_Slave_Mode          : Boolean;
      Trigger_Selection          : Timer_Trigger_Input_Source;
      Reserved1                  : Bits_1;
      Slave_Mode_Selection       : Timer_Slave_Mode;
   end record with Volatile_Full_Access, Size => 32;

   for TIMx_SMCR use record
      Reserved0                  at 0 range 16 .. 31;
      External_Trigger_Polarity  at 0 range 15 .. 15;
      External_Clock_Enable      at 0 range 14 .. 14;
      External_Trigger_Prescaler at 0 range 12 .. 13;
      External_Trigger_Filter    at 0 range  8 .. 11;
      Master_Slave_Mode          at 0 range  7 .. 7;
      Trigger_Selection          at 0 range  4 .. 6;
      Reserved1                  at 0 range  3 .. 3;
      Slave_Mode_Selection       at 0 range  0 .. 2;
   end record;

   ------------  representation for CCMR1 and CCMR2  --------------------------

   --  Per the ST Reference Manual, there are two words (registers)
   --  allocated within a timer to describe the capture-compare input/output
   --  configurations for the four channels. These are CCMR1 and CCMR2. Both
   --  currently only use the lower half of the word, with the upper half
   --  reserved.

   --  Each description is either that of a single input or a single output
   --  for the given channel. Both kinds of description require eight
   --  bits, therefore there are two channel descriptions in each word.

   --  Although both the input and output descriptions are the same size in
   --  terms of bits (six bits each), they do not have the same logical fields.
   --  We use two distinct types to represent individual input and output
   --  descriptions.

   type Channel_Output_Descriptor is record
      OCxFast_Enable    : Boolean;
      OCxPreload_Enable : Boolean;
      OCxMode           : Timer_Output_Compare_And_PWM_Mode;
      OCxClear_Enable   : Boolean;
   end record with Size => 6;

   for Channel_Output_Descriptor use record
      OCxFast_Enable    at 0 range 0 .. 0;
      OCxPreload_Enable at 0 range 1 .. 1;
      OCxMode           at 0 range 2 .. 4;
      OCxClear_Enable   at 0 range 5 .. 5;
   end record;

   type Channel_Input_Descriptor is record
      ICxFilter    : Timer_Input_Capture_Filter;
      ICxPrescaler : Timer_Input_Capture_Prescaler;
   end record with Size => 6;

   for Channel_Input_Descriptor use record
      ICxFilter    at 0 range 2 .. 5;
      ICxPrescaler at 0 range 0 .. 1;
   end record;

   --  So any given eight-bit description uses six bits for the specific fields
   --  describing the input or output configuration. The other two bits are
   --  taken by a field selecting the kind of description, i.e., either an
   --  input or an output description. In the RM register definitions this
   --  is "CCxS" (where 'x' is a place-holder for a channel number). Although
   --  there is one kind of output, there are in fact three kinds of inputs.

   --  Thus any given channel description is an eight-bit quantity that
   --  both indicates the kind and contains another set of dependent fields
   --  representing that kind. The dependent fields are logically mutually
   --  exclusive, i.e., if the CCxS selection field indicates an input then
   --  the output fields are not present, and vice versa. This logical layout
   --  is naturally represented in Ada as a discriminated type, where the
   --  discriminant is the CCxS "Selection" indicator.

   --  Note that the discriminant default value "Output" matches the default
   --  value of the hardware register bits when the device is powered up.
   --  Therefore we don't strictly speaking need pragma Import on the
   --  declarations of Timer objects, but it won't hurt.

   type IO_Descriptor (CCxSelection : Timer_Capture_Compare_Modes := Output) is
      record
         case CCxSelection is
            when Direct_TI .. TRC =>
               Capture : Channel_Input_Descriptor;
            when Output =>
               Compare : Channel_Output_Descriptor;
         end case;
      end record with Size => 8;

   --  Per the RM, the input fields and the output fields are in the same
   --  locations in memory, that is, they overlay, coming after the common
   --  CCxS field.

   for IO_Descriptor use record
      CCxSelection at 0 range 0 .. 1;
      Capture      at 0 range 2 .. 7;
      Compare      at 0 range 2 .. 7;
   end record;

   --  Thus we have a means of describing any single channel's configuration
   --  as either an input or an output. But how to get to them? As mentioned
   --  above, there are four channels so there are four I/O descriptions,
   --  spread across the two words of CCMR1 and CCMR2 in the timer
   --  representation. Specifically, the descriptions for channels 1 and 2 are
   --  in CCMR1, and the descriptions for channels 3 and 4 are in CCMR2. Rather
   --  than determine which register to use by having a dedicated routine
   --  for each channel, we use an array of descriptions allocated across the
   --  memory for the two registers and compute the description to use within
   --  the array for that channel.
   --
   --  The remaining difficulty is the reserved upper halves of each of the
   --  two registers in memory. We cannot simply allocate four components in
   --  our array because we must skip the reserved areas, but we don't have
   --  non-contiguous arrays in Ada (nor should we). As a result we must
   --  either declare two arrays, each with two descriptions, thus requiring
   --  additional types to specify the reserved areas, or we declare one
   --  array of eight descriptions and only access the four "real" ones. If we
   --  take the latter approach the other four descriptions would occupy the
   --  reserved areas and would never be accessed. As long as the reserved
   --  areas remain at their reset values (all zeroes) all should be well...
   --  except that we also have the requirement to access the memory for the
   --  two registers as either half-words or words, so any simplicity gained
   --  from declaring an array larger than required would be lost when
   --  processing it. Hence the following takes the first approach, not
   --  mapping anything to the reserved upper halves of the two words.

   subtype Lower_Half_Index is Integer range 1 .. 2;

   type TIMx_CCMRx_Lower_Half is
     array (Lower_Half_Index) of IO_Descriptor
     with Volatile_Components, Component_Size => 8, Size => 16;

   type TIMx_CCMRx is record
      Descriptors : TIMx_CCMRx_Lower_Half;
      Reserved    : Bits_16;
   end record with Volatile, Size => 32;

   for TIMx_CCMRx use record
      Descriptors at 0 range  0 .. 15;
      Reserved    at 0 range 16 .. 31;
   end record;

   --  Then we can define the array of this final record type TIMx_CCMRx,
   --  taking the space of the two CCMR1 and CCMR2 register words in memory.

   subtype CCMRx_Index is Integer range 1 .. 2;

   type TIMx_CCMR_Pair is array (CCMRx_Index) of TIMx_CCMRx
     with Component_Size => 32, Size => 64;

   --  Is this better than using bit masks? There's certainly a good bit more
   --  required for the declarations of the data structure! But the access code
   --  is pretty small and we would argue that the compile-time checking, and
   --  the readability, imply greater robustness and maintainability. (That
   --  said, the existing C libraries are very stable and mature.) This part
   --  of the hardware is definitely complicated in itself, and overlaying the
   --  input and output descriptions in memory didn't help. Performance should
   --  be reasonable, although not as good as bit-masking would be. Nowadays
   --  that's not necessarily where the money is, so we go with this approach
   --  for now...

   procedure Write_Channel_Input_Description
     (This        : in out Timer;
      Channel     : Timer_Channel;
      Kind        : Timer_Input_Capture_Selection;
      Description : Channel_Input_Descriptor)
     with Pre => not Channel_Enabled (This, Channel);

   ------------  representation for the CCER  ---------------------------------

   --  The CCER register is composed of a logical grouping of four sets of
   --  bits, one per channel. The type Single_CCE describe these four bits.
   --  Channels 1 through 3 have all four bits, but channel 4 does not have
   --  the complementary state and polarity bits. We pretend that it does for
   --  the type declaration and then treat it accordingly in the accessing
   --  subprograms.

   type Single_CCE is record
      CCxE  : Timer_Capture_Compare_State;
      CCxP  : Bits_1;
      CCxNE : Timer_Capture_Compare_State;
      CCxNP : Bits_1;
   end record with Size => 4;

   for Single_CCE use record
      CCxE  at 0 range 0 .. 0;
      CCxP  at 0 range 1 .. 1;
      CCxNE at 0 range 2 .. 2;
      CCxNP at 0 range 3 .. 3;
   end record;

   type TIMx_CCER is array (Timer_Channel) of Single_CCE
     with Volatile_Full_Access, Component_Size => 4, Size => 16;

   --------  representation for CCR1 through CCR4  ----------------------------

   --  Instead of declaring four individual record components, one per channel,
   --  each one a word in size, we just declare an array component representing
   --  all four values, indexed by the channel. Timers 2 and 5 actually use all
   --  32 bits of each, the other timers only use the lower half.

   type Capture_Compare_Registers is array (Timer_Channel) of Word
     with Volatile_Components, Component_Size => 32, Size => 128;

   ----------  representation for the Break and Dead Time Register - ----------

   type TIMx_BDTR is record
      Reserved                      : Half_Word;
      Main_Output_Enabled           : Boolean;
      Automatic_Output_Enabled      : Boolean;
      Break_Polarity                : Timer_Break_Polarity;
      Break_Enable                  : Boolean;
      Off_State_Selection_Run_Mode  : Bits_1;
      Off_State_Selection_Idle_Mode : Bits_1;
      Lock                          : Timer_Lock_Level;
      Deadtime_Generator            : Byte;
   end record with Volatile_Full_Access, Size => 32;

   for TIMx_BDTR use record
      Reserved                      at 0 range 16 .. 31;
      Main_Output_Enabled           at 0 range 15 .. 15;
      Automatic_Output_Enabled      at 0 range 14 .. 14;
      Break_Polarity                at 0 range 13 .. 13;
      Break_Enable                  at 0 range 12 .. 12;
      Off_State_Selection_Run_Mode  at 0 range 11 .. 11;
      Off_State_Selection_Idle_Mode at 0 range 10 .. 10;
      Lock                          at 0 range  8 .. 9;
      Deadtime_Generator            at 0 range  0 .. 7;
   end record;

   -----------  representation for the DMA Control Register type  -------------

   type TIMx_DCR is record
      Reserved0    : Half_Word;
      Reserved1    : Bits_3;
      Burst_Length : Timer_DMA_Burst_Length;
      Reserved2    : Bits_3;
      Base_Address : Timer_DMA_Base_Address;
   end record with Volatile_Full_Access, Size => 32;

   for TIMx_DCR use record
      Reserved0    at 0 range 16 .. 31;
      Reserved1    at 0 range 13 .. 15;
      Burst_Length at 0 range  8 .. 12;
      Reserved2    at 0 range  5 .. 7;
      Base_Address at 0 range  0 .. 4;
   end record;

   -------  representation for Timer 2, 5, and 11 remapping options  ----------

   type TIMx_OR is record
      Reserved0 : Half_Word;
      Reserved1 : Bits_4;
      ITR1_RMP  : Timer_2_Remapping_Options;
      Reserved2 : Bits_2;
      TI4_RMP   : Timer_5_Remapping_Options;   -- timer 5,  pg 633
      Reserved3 : Bits_4;
      TI1_RMP   : Timer_11_Remapping_Options;  -- timer 11, pg 676
   end record with Volatile_Full_Access, Size => 32;

   --  TODO: ensure the gaps are kept at reserved value in the routines'
   --  generated code

   for TIMx_OR use record
      Reserved0 at 0 range 16 .. 31;
      Reserved1 at 0 range 12 .. 15;
      ITR1_RMP  at 0 range 10 .. 11;
      Reserved2 at 0 range  8 .. 9;
      TI4_RMP   at 0 range  6 .. 7;
      Reserved3 at 0 range  2 .. 5;
      TI1_RMP   at 0 range  0 .. 1;
   end record;

   ----------------  representation for the whole Timer type  -----------------

   type Timer is limited record
      CR1                : TIMx_CR1;
      CR2                : TIMx_CR2;
      SMCR               : TIMx_SMCR;
      DIER               : Word;
      SR                 : Word;
      EGR                : Word;
      CCMR1_2            : TIMx_CCMR_Pair;
      CCER               : TIMx_CCER;
      Reserved_CCER      : Half_Word;
      Counter            : Word;  -- a full word for timers 2 and 5 only
      Prescaler          : Half_Word;
      Reserved_Prescaler : Half_Word;
      ARR                : Half_Word;
      Reserved_ARR       : Half_Word;
      RCR                : Word;
      CCR1_4             : Capture_Compare_Registers;
      BDTR               : TIMx_BDTR;
      DCR                : TIMx_DCR;
      DMAR               : Word;
      Options            : TIMx_OR;
   end record with Volatile, Size => 21 * 32;

   for Timer use record
      CR1                at 16#00# range  0 .. 31;
      CR2                at 16#04# range  0 .. 31;
      SMCR               at 16#08# range  0 .. 31;
      DIER               at 16#0C# range  0 .. 31;
      SR                 at 16#10# range  0 .. 31;
      EGR                at 16#14# range  0 .. 31;
      CCMR1_2            at 16#18# range  0 .. 63;
      CCER               at 16#20# range  0 .. 15;
      Reserved_CCER      at 16#20# range 16 .. 31;
      Counter            at 16#24# range  0 .. 31;
      Prescaler          at 16#28# range  0 .. 15;
      Reserved_Prescaler at 16#28# range 16 .. 31;
      ARR                at 16#2C# range  0 .. 15;
      Reserved_ARR       at 16#2C# range 16 .. 31;
      RCR                at 16#30# range  0 .. 31;
      CCR1_4             at 16#34# range  0 .. 127;  -- ie, 4 words
      BDTR               at 16#44# range  0 .. 31;
      DCR                at 16#48# range  0 .. 31;
      DMAR               at 16#4C# range  0 .. 31;
      Options            at 16#50# range  0 .. 31;
   end record;

end STM32F4.Timers;
