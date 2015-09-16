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
--   @file    stm32f4xx_hal_spi.h                                           --
--   @author  MCD Application Team                                          --
--   @version V1.1.0                                                        --
--   @date    19-June-2014                                                  --
--   @brief   Header file of DMA HAL module.                                --
--                                                                          --
--   COPYRIGHT(c) 2014 STMicroelectronics                                   --
------------------------------------------------------------------------------

--  This file provides definitions for the STM32F4 (ARM Cortex M4F
--  from ST Microelectronics) Serial Peripheral Interface (SPI) facility.

package STM32F4.SPI is

   type SPI_Port is limited private;

   type SPI_Data_Direction is
     (D2Lines_FullDuplex,
      D2Lines_RxOnly,
      D1Line_Rx,
      D1Line_Tx);

   type SPI_Data_Size is (Data_16, Data_8);

   type SPI_Mode is (Master, Slave);

   type SPI_CLock_Polarity is (High, Low);

   type SPI_CLock_Phase is (P1Edge, P2Edge);

   type SPI_Slave_Management is (Software_Managed, Hardware_Managed);

   type SPI_Baud_Rate_Prescaler is
     (BRP_2, BRP_4, BRP_8, BRP_16, BRP_32, BRP_64, BRP_128, BRP_256);

   type SPI_First_Bit is (MSB, LSB);

   type SPI_Configuration is record
      Direction           : SPI_Data_Direction;
      Mode                : SPI_Mode;
      Data_Size           : SPI_Data_Size;
      Clock_Polarity      : SPI_Clock_Polarity;
      Clock_Phase         : SPI_Clock_Phase;
      Slave_Management    : SPI_Slave_Management;
      Baud_Rate_Prescaler : SPI_Baud_Rate_Prescaler;
      First_Bit           : SPI_First_Bit;
      CRC_Poly            : Half_Word;
   end record;

   procedure Configure (Port : in out SPI_Port; Conf : SPI_Configuration);

   procedure Enable (Port : in out SPI_Port);

   procedure Disable (Port : in out SPI_Port);

   function Enabled (Port : SPI_Port) return Boolean with Volatile_Function;

   procedure Send (Port : in out SPI_Port; Data : Half_Word);

   function Data (Port : SPI_Port) return Half_Word
     with Inline, Volatile_Function;

   procedure Send (Port : in out SPI_Port; Data : Byte);

   function Data (Port : SPI_Port) return Byte
     with Inline, Volatile_Function;

   function Rx_Is_Empty (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Tx_Is_Empty (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Busy (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Channel_Side_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Underrun_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function CRC_Error_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Mode_Fault_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Overrun_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   function Frame_Fmt_Error_Indicated (Port : SPI_Port) return Boolean
     with Inline, Volatile_Function;

   procedure Clear_Overrun (Port : SPI_Port);

   procedure Reset_CRC (Port : in out SPI_Port);

   function CRC_Enabled (Port : SPI_Port) return Boolean;

   function Is_Data_Frame_16bit (Port : SPI_Port) return Boolean with Volatile_Function;

   function Current_Mode (Port : SPI_Port) return SPI_Mode with Volatile_Function;

   function Current_Data_Direction (Port : SPI_Port) return SPI_Data_Direction with Volatile_Function;

   --  The following I/O routines implement the higher level functionality for CRC and data direction, among others.

   type Byte_Buffer is array (Natural range <>) of Byte
     with Alignment => 2;
   -- The alignment is set to 2 because we treat component pairs as half_word
   -- values when sending/receiving in 16-bit mode.

   --  Blocking

   procedure Transmit
     (Port     : in out SPI_Port;
      Outgoing : Byte_Buffer;
      Size     : Positive);

   procedure Transmit
     (Port     : in out SPI_Port;
      Outgoing : Byte);

   procedure Receive
     (Port     : in out SPI_Port;
      Incoming : out Byte_Buffer;
      Size     : Positive);

   procedure Receive
     (Port     : in out SPI_Port;
      Incoming : out Byte);

   procedure Transmit_Receive
     (Port      : in out SPI_Port;
      Outgoing  : Byte_Buffer;
      Incoming  : out Byte_Buffer;
      Size      : Positive);

   procedure Transmit_Receive
     (Port      : in out SPI_Port;
      Outgoing  : Byte;
      Incoming  : out Byte);

   --  TODO: add the other higher-level HAL routines for interrupts and DMA

private

   type SPI_Control_Register is record
      Clock_Phase    : Bits_1;
      Clock_Polarity : Bits_1;
      Master_Select  : Bits_1;
      Baud_Rate_Ctrl : Bits_3;
      SPI_Enable     : Bits_1;
      LSB_First      : Bits_1; --  Frame Format
      Slave_Select   : Bits_1;
      Soft_Slave_Mgt : Bits_1; --  Software Slave Management
      RXOnly         : Bits_1;
      Data_Frame_Fmt : Bits_1; --  1=16-bit 0=8-bit
      CRC_Next       : Bits_1; --  1=CRC Phase 0=No CRC Phase
      CRC_Enable     : Bits_1;
      Output_BiDir   : Bits_1; --  Output enable in bidirectional mode
      BiDir_Mode     : Bits_1; --  Bidirectional data mode enable
   end record with Pack, Volatile_Full_Access, Size => 16;

   type SPI_Control_Register2 is record
      RX_DMA_Enable           : Bits_1;
      TX_DMA_Enable           : Bits_1;
      SS_Out_Enable           : Bits_1;
      Reserved_1              : Bits_1;
      Frame_Fmt               : Bits_1; --  0=Motorola Mode 1=TI Mode
      Err_Int_Enable          : Bits_1;
      RX_Not_Empty_Int_Enable : Bits_1;
      TX_Empty_Int_Enable     : Bits_1;
      Reserved_2              : Bits_8;
   end record with Pack, Volatile_Full_Access, Size => 16;

   type SPI_I2S_Config_Register is record
      Channel_Length : Bits_1;
      Data_Length    : Bits_2;
      Clock_Polarity : Bits_1;
      I2S_Standard   : Bits_2; --  00==Philips 01=MSB (L) 10=LSB (R) 11=PCM
      Reserved_1     : Bits_1;
      PCM_Frame_Sync : Bits_1; --  0=Short 1=Long
      Config_Mode    : Bits_2; --  00=SlaveTX 01=SlaveRX 10=MasterTX11=MasterRX
      Enable         : Bits_1;
      Mode_Select    : Bits_1; --  0=SPI Mode 1=I2S Mode
      Reserved_2     : Bits_4;
   end record with Pack, Volatile_Full_Access, Size => 16;

   type SPI_I2S_Prescale_Register is record
      Linear_Prescaler      : Bits_8;
      Odd_Factor            : Bits_1;
      Master_CLK_Out_Enable : Bits_1;
      Reserved              : Bits_6;
   end record with Pack, Volatile_Full_Access, Size => 16;

   type SPI_Status_Register is record
      RX_Buffer_Not_Empty : Boolean;
      TX_Buffer_Empty     : Boolean;
      Channel_Side        : Boolean;
      Underrun_Flag       : Boolean;
      CRC_Error_Flag      : Boolean;
      Mode_Fault          : Boolean;
      Overrun_Flag        : Boolean;
      Busy_Flag           : Boolean;
      Frame_Fmt_Error     : Boolean;
      Reserved            : Bits_7;
   end record with Pack, Volatile_Full_Access, Size => 16;

   type SPI_Port is record
      CTRL1       : SPI_Control_Register;
      Reserved_1  : Half_Word;
      CTRL2       : SPI_Control_Register2;
      Reserved_2  : Half_Word;
      Status      : SPI_Status_Register;
      Reserved_3  : Half_Word;
      Data        : Half_Word;
      Reserved_4  : Half_Word;
      CRC_Poly    : Half_Word; --  Default = 16#0007#
      Reserved_5  : Half_Word;
      RX_CRC      : Half_Word;
      Reserved_6  : Half_Word;
      TX_CRC      : Half_Word;
      Reserved_7  : Half_Word;
      I2S_Conf    : SPI_I2S_Config_Register;
      Reserved_8  : Half_Word;
      I2S_PreScal : SPI_I2S_Prescale_Register;
      Reserved_9  : Half_Word;
   end record with Pack, Volatile, Size => 9 * 32;


   procedure Send_Receive_16bit_Mode
     (Port     : in out SPI_Port;
      Outgoing : Byte_Buffer;
      Incoming : out Byte_Buffer;
      Size     : Positive);

   procedure Send_Receive_8bit_Mode
     (Port     : in out SPI_Port;
      Outgoing : Byte_Buffer;
      Incoming : out Byte_Buffer;
      Size     : Positive);

   procedure Send_16bit_Mode
     (Port     : in out SPI_Port;
      Outgoing : Byte_Buffer;
      Size     : Positive);

   procedure Send_8bit_Mode
     (Port     : in out SPI_Port;
      Outgoing : Byte_Buffer;
      Size     : Positive);

   procedure Receive_16bit_Mode
     (Port     : in out SPI_Port;
      Incoming : out Byte_Buffer;
      Count    : Positive);

   procedure Receive_8bit_Mode
     (Port     : in out SPI_Port;
      Incoming : out Byte_Buffer;
      Count    : Positive);

end STM32F4.SPI;
