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
--   @file    stm32f4xx_hal_usart.h                                         --
--   @author  MCD Application Team                                          --
--   @version V1.1.0                                                        --
--   @date    19-June-2014                                                  --
--   @brief   Header file of DMA HAL module.                                --
--                                                                          --
--   COPYRIGHT(c) 2014 STMicroelectronics                                   --
------------------------------------------------------------------------------

--  This file provides register definitions for the STM32F4 (ARM Cortex M4F)
--  USART from ST Microelectronics.

--  Note that there are board implementation assumptions represented by the
--  private function APB_Clock.

-- pragma SPARK_Mode (On);

pragma Restrictions (No_Elaboration_Code);

with System;

package STM32F4.USARTs is

   type USART is limited private;

   procedure Enable (This : in out USART)
     with
       Post => Enabled (This),
       Inline;

   procedure Disable (This : in out USART)
     with
       Post => not Enabled (This),
       Inline;

   function Enabled (This : USART) return Boolean with Inline;

   procedure Receive (This : USART;  Data : out Half_Word) with Inline;
   --  reads Device.DR into Data

   function Current_Input (This : USART) return Half_Word with Inline;
   --  returns Device.DR

   procedure Transmit (This : in out USART;  Data : Half_Word) with Inline;

   function Tx_Ready (This : USART) return Boolean with Inline, Volatile_Function;

   function Rx_Ready (This : USART) return Boolean with Inline, Volatile_Function;

   type Stop_Bits is (Stopbits_1, Stopbits_2);

   for Stop_Bits use (Stopbits_1 => 0, Stopbits_2 => 16#2000#);
   for Stop_Bits'Size use Half_Word'Size;

   procedure Set_Stop_Bits (This : in out USART;  To : Stop_Bits);

   type Word_Lengths is (Word_Length_8, Word_Length_9);
   for Word_Lengths use (Word_Length_8 => 0, Word_Length_9 => 16#1000#);
   for Word_Lengths'Size use Half_Word'Size;

   procedure Set_Word_Length (This : in out USART;  To : Word_Lengths);

   type Parities is (No_Parity, Even_Parity, Odd_Parity);

   for Parities use
     (No_Parity => 0, Even_Parity => 16#0400#, Odd_Parity => 16#0600#);
   for Parities'Size use Half_Word'Size;

   procedure Set_Parity (This : in out USART;  To : Parities);

   subtype Baud_Rates is Word range 110 .. 115_200 with Static_Predicate =>
      Baud_Rates in
        110    | 300    | 600    | 1200   | 2400   | 4800   | 9600 |
        14_400 | 19_200 | 28_800 | 38_400 | 56_000 | 57_600 | 115_200;

   procedure Set_Baud_Rate (This : in out USART;  To : Baud_Rates);

   type UART_Modes is (Rx_Mode, Tx_Mode, Tx_Rx_Mode);

   for UART_Modes use
     (Rx_Mode => 16#0004#, Tx_Mode => 16#0008#, Tx_Rx_Mode => 16#000C#);
   for UART_Modes'Size use Half_Word'Size;

   procedure Set_Mode (This : in out USART;  To : UART_Modes);

   type Flow_Control is
     (No_Flow_Control,
      RTS_Flow_Control,
      CTS_Flow_Control,
      RTS_CTS_Flow_Control);

   for Flow_Control use
     (No_Flow_Control      => 0,
      RTS_Flow_Control     => 16#0100#,
      CTS_Flow_Control     => 16#0200#,
      RTS_CTS_Flow_Control => 16#0300#);
   for Flow_Control'Size use Half_Word'Size;

   procedure Set_Flow_Control (This : in out USART;  To : Flow_Control);

   type USART_Interrupt is
     (Parity_Error,
      Transmit_Data_Register_Empty,
      Transmission_Complete,
      Received_Data_Not_Empty,
      Idle_Line_Detection,
      Line_Break_Detection,
      Clear_To_Send,
      Error);

   procedure Enable_Interrupts
     (This   : in out USART;
      Source : USART_Interrupt)
     with
       Post => Interrupt_Enabled (This, Source),
       Inline;

   procedure Disable_Interrupts
     (This   : in out USART;
      Source : USART_Interrupt)
     with
       Post => not Interrupt_Enabled (This, Source),
        Inline;

   function Interrupt_Enabled
     (This   : USART;
      Source : USART_Interrupt)
      return Boolean
     with Inline, Volatile_Function;

   type USART_Status_Flag is
     (Parity_Error_Indicated,
      Framing_Error_Indicated,
      USART_Noise_Error_Indicated,
      Overrun_Error_Indicated,
      Idle_Line_Detection_Indicated,
      Read_Data_Register_Not_Empty,
      Transmission_Complete_Indicated,
      Transmit_Data_Register_Empty,
      Line_Break_Detection_Indicated,
      Clear_To_Send_Indicated);

   function Status (This : USART; Flag : USART_Status_Flag) return Boolean
     with Inline, Volatile_Function;

   procedure Clear_Status (This : in out USART; Flag : USART_Status_Flag)
     with Inline;

   procedure Enable_DMA_Transmit_Requests (This : in out USART)
     with
       Inline,
       Post => DMA_Transmit_Requests_Enabled (This);

   procedure Disable_DMA_Transmit_Requests (This : in out USART)
     with
       Inline,
       Post => not DMA_Transmit_Requests_Enabled (This);

   function DMA_Transmit_Requests_Enabled  (This : USART) return Boolean
     with Inline;


   procedure Enable_DMA_Receive_Requests (This : in out USART)
     with
       Inline,
       Post => DMA_Receive_Requests_Enabled (This);

   procedure Disable_DMA_Receive_Requests (This : in out USART)
     with
       Inline,
       Post => not DMA_Receive_Requests_Enabled (This);

   function DMA_Receive_Requests_Enabled  (This : USART) return Boolean
     with Inline;

   procedure Pause_DMA_Transmission (This : in out USART)
     renames Disable_DMA_Transmit_Requests;

   procedure Resume_DMA_Transmission (This : in out USART)
     with
       Inline,
       Post => DMA_Transmit_Requests_Enabled (This) and
               Enabled (This);

   procedure Pause_DMA_Reception (This : in out USART)
     renames Disable_DMA_Receive_Requests;

   procedure Resume_DMA_Reception (This : in out USART)
     with
       Inline,
       Post => DMA_Receive_Requests_Enabled (This) and
               Enabled (This);

   ----------------------------- WARNING --------------------------------------
   function Data_Register_Address (This : USART) return System.Address
     with Inline;
   --  Returns the address of the USART Data Register. This is exported
   --  STRICTLY for the sake of clients driving a USART via DMA. All other
   --  clients of this package should use the procedural interfaces Transmit
   --  and Receive instead of directly accessing the Data Register!
   --  Seriously, don't use this function otherwise.
   ----------------------------- WARNING --------------------------------------

private

   type Status_Register is record
      Reserved0                         : Half_Word;
      Reserved1                         : Bits_6;
      Clear_To_Send_Flag                : Boolean;
      LIN_Break_Detected_Flag           : Boolean;
      Transmit_Data_Register_Empty_Flag : Boolean;
      Transmission_Complete_Flag        : Boolean;
      Read_Data_Register_Not_Empty_Flag : Boolean;
      IDLE_Line_Detected_Flag           : Boolean;
      OverRun_Error_Flag                : Boolean;
      Noise_Error_Flag                  : Boolean;
      Framing_Error_Flag                : Boolean;
      Parity_Error_Flag                 : Boolean;
   end record
     with Atomic, Size => 32;

   for Status_Register use record
      Reserved0                         at 0 range 16 .. 31;
      Reserved1                         at 0 range 10 .. 15;
      Clear_To_Send_Flag                at 0 range  9 .. 9;
      LIN_Break_Detected_Flag           at 0 range  8 .. 8;
      Transmit_Data_Register_Empty_Flag at 0 range  7 .. 7;
      Transmission_Complete_Flag        at 0 range  6 .. 6;
      Read_Data_Register_Not_Empty_Flag at 0 range  5 .. 5;
      IDLE_Line_Detected_Flag           at 0 range  4 .. 4;
      OverRun_Error_Flag                at 0 range  3 .. 3;
      Noise_Error_Flag                  at 0 range  2 .. 2;
      Framing_Error_Flag                at 0 range  1 .. 1;
      Parity_Error_Flag                 at 0 range  0 .. 0;
   end record;

   for Status_Register'Bit_Order use System.Low_Order_First;

   type USART is limited record
      SR         : Status_Register;
      DR         : Half_Word; -- Data register
      Reserved_1 : Half_Word;
      BRR        : Half_Word; -- Baud rate register
      Reserved_2 : Half_Word;
      CR1        : Half_Word; -- Control register 1
      Reserved_3 : Half_Word;
      CR2        : Half_Word; -- Control register 2
      Reserved_4 : Half_Word;
      CR3        : Half_Word; -- Control register 3
      Reserved_5 : Half_Word;
      GTPR       : Half_Word; -- Guard time and prescaler register
      Reserved_6 : Half_Word;
   end record with
     Volatile;

   for USART use record
      SR         at  0 range 0 .. 31;
      DR         at  4 range 0 .. 15;
      Reserved_1 at  6 range 0 .. 15;
      BRR        at  8 range 0 .. 15;
      Reserved_2 at 10 range 0 .. 15;
      CR1        at 12 range 0 .. 15;
      Reserved_3 at 14 range 0 .. 15;
      CR2        at 16 range 0 .. 15;
      Reserved_4 at 18 range 0 .. 15;
      CR3        at 20 range 0 .. 15;
      Reserved_5 at 22 range 0 .. 15;
      GTPR       at 24 range 0 .. 15;
      Reserved_6 at 26 range 0 .. 15;
   end record;


   function APB_Clock (This : USART) return Word with Inline, Volatile_Function;
   --  Returns either APB1 or APB2 clock rate, in Hertz, depending on the USART.
   --  For the sake of not making this package board-specific, we assume that
   --  we are given a valid USART object at a valid address, AND that the
   --  USART devices really are configured such that only 1 and 6 are on APB2.
   --  Therefore, if a board has additional USARTs beyond USART6, eg USART8 on
   --  the F429I Discovery board, they better conform to that assumption.


   USART_DR_MASK : constant Half_Word := 16#1FF#;

   --  TODO: consider replacing CRx with record types

   --  Bit definitions for USART CR1 register
   CR1_SBK    : constant := 16#0001#;   -- Send Break
   CR1_RWU    : constant := 16#0002#;   -- Receiver Wakeup
   CR1_RE     : constant := 16#0004#;   -- Receiver Enable
   CR1_TE     : constant := 16#0008#;   -- Transmitter Enable
   CR1_IDLEIE : constant := 16#0010#;   -- IDLE Interrupt Enable
   CR1_RXNEIE : constant := 16#0020#;   -- RXNE Interrupt Enable
   CR1_TCIE   : constant := 16#0040#;   -- Transmit Complete Interrupt Enable
   CR1_TXEIE  : constant := 16#0080#;   -- Transmit Data Register Empty Interrupt Enable
   CR1_PEIE   : constant := 16#0100#;   -- PE Interrupt Enable
   CR1_PS     : constant := 16#0200#;   -- Parity Selection
   CR1_PCE    : constant := 16#0400#;   -- Parity Control Enable
   CR1_WAKE   : constant := 16#0800#;   -- Wakeup Method
   CR1_M      : constant := 16#1000#;   -- Word Length
   CR1_UE     : constant := 16#2000#;   -- USART Enable
   CR1_OVER8  : constant := 16#8000#;   -- Oversampling by 8 Enable

   --  Bit definitions for USART CR2 register
   CR2_ADD   : constant := 16#000F#;   -- Address of USART Node
   CR2_LBDL  : constant := 16#0020#;   -- LIN Brk Detection Length
   CR2_LBDIE : constant := 16#0040#;   -- LIN Brk Detection Interrupt Enable
   CR2_LBCL  : constant := 16#0100#;   -- Last Bit Clock pulse
   CR2_CPHA  : constant := 16#0200#;   -- Clock Phase
   CR2_CPOL  : constant := 16#0400#;   -- Clock Polarity
   CR2_CLKEN : constant := 16#0800#;   -- Clock Enable

   CR2_STOP   : constant := 16#3000#;   -- STOP bits
   CR2_STOP_0 : constant := 16#1000#;   -- Bit 0
   CR2_STOP_1 : constant := 16#2000#;   -- Bit 1

   CR2_LINEN : constant := 16#4000#;   -- LIN mode enable

   --  Bit definitions for USART CR3 register
   CR3_EIE    : constant := 16#0001#;   -- Error Interrupt Enable
   CR3_IREN   : constant := 16#0002#;   -- IrDA mode Enable
   CR3_IRLP   : constant := 16#0004#;   -- IrDA Low-Power
   CR3_HDSEL  : constant := 16#0008#;   -- Half-Duplex Selection
   CR3_NACK   : constant := 16#0010#;   -- Smartcard NACK enable
   CR3_SCEN   : constant := 16#0020#;   -- Smartcard mode enable
   CR3_DMAR   : constant := 16#0040#;   -- DMA Enable Receiver
   CR3_DMAT   : constant := 16#0080#;   -- DMA Enable Transmitter
   CR3_RTSE   : constant := 16#0100#;   -- RTS Enable
   CR3_CTSE   : constant := 16#0200#;   -- CTS Enable
   CR3_CTSIE  : constant := 16#0400#;   -- CTS Interrupt Enable
   CR3_ONEBIT : constant := 16#0800#;   -- One bit method enable

end STM32F4.USARTs;
