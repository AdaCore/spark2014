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
--   @file    stm32f429i_discovery.h                                        --
--   @author  MCD Application Team                                          --
--   @version V1.1.0                                                        --
--   @date    19-June-2014                                                  --
--   @brief   Header file of DMA HAL module.                                --
--                                                                          --
--   COPYRIGHT(c) 2014 STMicroelectronics                                   --
------------------------------------------------------------------------------

--  This file provides declarations for STM32F429xx boards manufactured by
--  from ST Microelectronics.  For example: the STM32F429I Discovery kit.

with System;          use System;
with STM32F4.GPIO;    use STM32F4.GPIO;
with STM32F4.DMA;     use STM32F4.DMA;
with STM32F4.USARTs;  use STM32F4.USARTs;
with STM32F4.I2C;     use STM32F4.I2C;
with STM32F4.SPI;     use STM32F4.SPI;
with STM32F4.Timers;  use STM32F4.Timers;

use STM32F4;  -- for base addresses

package STM32F429_Discovery is
--   pragma Elaborate_Body;  temporarily commented (see O916-???)

   subtype User_LED is GPIO_Pin;

   Green : User_LED renames Pin_13;
   Red   : User_LED renames Pin_14;

   LED3  : User_LED renames Green;
   LED4  : User_LED renames Red;

   All_LEDs  : constant GPIO_Pins := LED3 & LED4;

   procedure Initialize_LEDs;
   --  MUST be called prior to any use of the LEDs

   procedure Turn_On (This : User_LED) with Inline;
   procedure Turn_Off (This : User_LED) with Inline;
   procedure Toggle (This : User_LED) with Inline;

   procedure Toggle_LEDs (These : GPIO_Pins) with Inline;
   procedure All_LEDs_Off with Inline;
   procedure All_LEDs_On  with Inline;


   GPIO_A : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOA_Base);
   GPIO_B : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOB_Base);
   GPIO_C : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOC_Base);
   GPIO_D : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOD_Base);
   GPIO_E : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOE_Base);
   GPIO_F : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOF_Base);
   GPIO_G : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOG_Base);
   GPIO_H : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOH_Base);
   GPIO_I : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOI_Base);
   GPIO_J : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOJ_Base);
   GPIO_K : aliased GPIO_Port with Volatile, Address => System'To_Address (GPIOK_Base);

   procedure Enable_Clock (This : aliased in out GPIO_Port);

   USART_1 : aliased USART with Volatile, Address => System'To_Address (USART1_Base);
   USART_2 : aliased USART with Volatile, Address => System'To_Address (USART2_Base);
   USART_3 : aliased USART with Volatile, Address => System'To_Address (USART3_Base);
   -- UART_4  : aliased UART with Volatile, Address => System'To_Address (UART4_Base);
   -- UART_5  : aliased UART with Volatile, Address => System'To_Address (UART5_Base);
   USART_6 : aliased USART with Volatile, Address => System'To_Address (USART6_Base);
   -- UART_7  : aliased UART with Volatile, Address => System'To_Address (UART7_Base);
   -- UART_8  : aliased UART with Volatile, Address => System'To_Address (UART8_Base);

   procedure Enable_Clock (This : aliased in out USART);

   DMA_1 : aliased DMA_Controller with Volatile, Address => System'To_Address (DMA1_BASE);
   DMA_2 : aliased DMA_Controller with Volatile, Address => System'To_Address (DMA2_BASE);

   procedure Enable_Clock (This : aliased in out DMA_Controller);

   I2C_1 : aliased I2C_Port with Volatile, Address => System'To_Address (I2C1_Base);
   I2C_2 : aliased I2C_Port with Volatile, Address => System'To_Address (I2C2_Base);
   I2C_3 : aliased I2C_Port with Volatile, Address => System'To_Address (I2C3_Base);

   procedure Enable_Clock (This : aliased in out I2C_Port);

   procedure Reset (This : in out I2C_Port);

   SPI_1 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI1_Base);
   SPI_2 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI2_Base);
   SPI_3 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI3_Base);
   SPI_4 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI4_Base);
   SPI_5 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI5_Base);
   SPI_6 : aliased SPI_Port with Volatile, Address => System'To_Address (SPI6_Base);

   procedure Enable_Clock (This : aliased in out SPI_Port);

   procedure Reset (This : in out SPI_Port);

   Timer_1 : aliased Timer with Volatile, Address => System'To_Address (TIM1_Base);
   pragma Import (Ada, Timer_1);
   Timer_2 : aliased Timer with Volatile, Address => System'To_Address (TIM2_Base);
   pragma Import (Ada, Timer_2);
   Timer_3 : aliased Timer with Volatile, Address => System'To_Address (TIM3_Base);
   pragma Import (Ada, Timer_3);
   Timer_4 : aliased Timer with Volatile, Address => System'To_Address (TIM4_Base);
   pragma Import (Ada, Timer_4);
   Timer_5 : aliased Timer with Volatile, Address => System'To_Address (TIM5_Base);
   pragma Import (Ada, Timer_5);
   Timer_6 : aliased Timer with Volatile, Address => System'To_Address (TIM6_Base);
   pragma Import (Ada, Timer_6);
   Timer_7 : aliased Timer with Volatile, Address => System'To_Address (TIM7_Base);
   pragma Import (Ada, Timer_7);
   Timer_8 : aliased Timer with Volatile, Address => System'To_Address (TIM8_Base);
   pragma Import (Ada, Timer_8);
   Timer_9 : aliased Timer with Volatile, Address => System'To_Address (TIM9_Base);
   pragma Import (Ada, Timer_9);
   Timer_10 : aliased Timer with Volatile, Address => System'To_Address (TIM10_Base);
   pragma Import (Ada, Timer_10);
   Timer_11 : aliased Timer with Volatile, Address => System'To_Address (TIM11_Base);
   pragma Import (Ada, Timer_11);
   Timer_12 : aliased Timer with Volatile, Address => System'To_Address (TIM12_Base);
   pragma Import (Ada, Timer_12);
   Timer_13 : aliased Timer with Volatile, Address => System'To_Address (TIM13_Base);
   pragma Import (Ada, Timer_13);
   Timer_14 : aliased Timer with Volatile, Address => System'To_Address (TIM14_Base);
   pragma Import (Ada, Timer_14);

   procedure Enable_Clock (This : in out Timer);

   procedure Reset (This : in out Timer);

end STM32F429_Discovery;
