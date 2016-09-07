--
--  Copyright (C) 2016, AdaCore
--

--  This spec has been automatically generated from STM32F429x.svd

pragma Ada_2012;

with System;

--  STM32F429x
package Interfaces.STM32 is
   pragma Preelaborate;
   pragma No_Elaboration_Code_All;

   --------------------
   -- Base addresses --
   --------------------

   RNG_Base : constant System.Address :=
     System'To_Address (16#50060800#);
   DCMI_Base : constant System.Address :=
     System'To_Address (16#50050000#);
   FMC_Base : constant System.Address :=
     System'To_Address (16#A0000000#);
   DBG_Base : constant System.Address :=
     System'To_Address (16#E0042000#);
   DMA2_Base : constant System.Address :=
     System'To_Address (16#40026400#);
   DMA1_Base : constant System.Address :=
     System'To_Address (16#40026000#);
   RCC_Base : constant System.Address :=
     System'To_Address (16#40023800#);
   GPIOK_Base : constant System.Address :=
     System'To_Address (16#40022800#);
   GPIOJ_Base : constant System.Address :=
     System'To_Address (16#40022400#);
   GPIOI_Base : constant System.Address :=
     System'To_Address (16#40022000#);
   GPIOH_Base : constant System.Address :=
     System'To_Address (16#40021C00#);
   GPIOG_Base : constant System.Address :=
     System'To_Address (16#40021800#);
   GPIOF_Base : constant System.Address :=
     System'To_Address (16#40021400#);
   GPIOE_Base : constant System.Address :=
     System'To_Address (16#40021000#);
   GPIOD_Base : constant System.Address :=
     System'To_Address (16#40020C00#);
   GPIOC_Base : constant System.Address :=
     System'To_Address (16#40020800#);
   GPIOB_Base : constant System.Address :=
     System'To_Address (16#40020400#);
   GPIOA_Base : constant System.Address :=
     System'To_Address (16#40020000#);
   SYSCFG_Base : constant System.Address :=
     System'To_Address (16#40013800#);
   SPI1_Base : constant System.Address :=
     System'To_Address (16#40013000#);
   SPI2_Base : constant System.Address :=
     System'To_Address (16#40003800#);
   SPI3_Base : constant System.Address :=
     System'To_Address (16#40003C00#);
   I2S2ext_Base : constant System.Address :=
     System'To_Address (16#40003400#);
   I2S3ext_Base : constant System.Address :=
     System'To_Address (16#40004000#);
   SPI4_Base : constant System.Address :=
     System'To_Address (16#40013400#);
   SPI5_Base : constant System.Address :=
     System'To_Address (16#40015000#);
   SPI6_Base : constant System.Address :=
     System'To_Address (16#40015400#);
   SDIO_Base : constant System.Address :=
     System'To_Address (16#40012C00#);
   ADC1_Base : constant System.Address :=
     System'To_Address (16#40012000#);
   ADC2_Base : constant System.Address :=
     System'To_Address (16#40012100#);
   ADC3_Base : constant System.Address :=
     System'To_Address (16#40012200#);
   USART6_Base : constant System.Address :=
     System'To_Address (16#40011400#);
   USART1_Base : constant System.Address :=
     System'To_Address (16#40011000#);
   USART2_Base : constant System.Address :=
     System'To_Address (16#40004400#);
   USART3_Base : constant System.Address :=
     System'To_Address (16#40004800#);
   UART7_Base : constant System.Address :=
     System'To_Address (16#40007800#);
   UART8_Base : constant System.Address :=
     System'To_Address (16#40007C00#);
   DAC_Base : constant System.Address :=
     System'To_Address (16#40007400#);
   PWR_Base : constant System.Address :=
     System'To_Address (16#40007000#);
   I2C3_Base : constant System.Address :=
     System'To_Address (16#40005C00#);
   I2C2_Base : constant System.Address :=
     System'To_Address (16#40005800#);
   I2C1_Base : constant System.Address :=
     System'To_Address (16#40005400#);
   IWDG_Base : constant System.Address :=
     System'To_Address (16#40003000#);
   WWDG_Base : constant System.Address :=
     System'To_Address (16#40002C00#);
   RTC_Base : constant System.Address :=
     System'To_Address (16#40002800#);
   UART4_Base : constant System.Address :=
     System'To_Address (16#40004C00#);
   UART5_Base : constant System.Address :=
     System'To_Address (16#40005000#);
   C_ADC_Base : constant System.Address :=
     System'To_Address (16#40012300#);
   TIM1_Base : constant System.Address :=
     System'To_Address (16#40010000#);
   TIM8_Base : constant System.Address :=
     System'To_Address (16#40010400#);
   TIM2_Base : constant System.Address :=
     System'To_Address (16#40000000#);
   TIM3_Base : constant System.Address :=
     System'To_Address (16#40000400#);
   TIM4_Base : constant System.Address :=
     System'To_Address (16#40000800#);
   TIM5_Base : constant System.Address :=
     System'To_Address (16#40000C00#);
   TIM9_Base : constant System.Address :=
     System'To_Address (16#40014000#);
   TIM12_Base : constant System.Address :=
     System'To_Address (16#40001800#);
   TIM10_Base : constant System.Address :=
     System'To_Address (16#40014400#);
   TIM13_Base : constant System.Address :=
     System'To_Address (16#40001C00#);
   TIM14_Base : constant System.Address :=
     System'To_Address (16#40002000#);
   TIM11_Base : constant System.Address :=
     System'To_Address (16#40014800#);
   TIM6_Base : constant System.Address :=
     System'To_Address (16#40001000#);
   TIM7_Base : constant System.Address :=
     System'To_Address (16#40001400#);
   Ethernet_MAC_Base : constant System.Address :=
     System'To_Address (16#40028000#);
   Ethernet_MMC_Base : constant System.Address :=
     System'To_Address (16#40028100#);
   Ethernet_PTP_Base : constant System.Address :=
     System'To_Address (16#40028700#);
   Ethernet_DMA_Base : constant System.Address :=
     System'To_Address (16#40029000#);
   CRC_Base : constant System.Address :=
     System'To_Address (16#40023000#);
   OTG_FS_GLOBAL_Base : constant System.Address :=
     System'To_Address (16#50000000#);
   OTG_FS_HOST_Base : constant System.Address :=
     System'To_Address (16#50000400#);
   OTG_FS_DEVICE_Base : constant System.Address :=
     System'To_Address (16#50000800#);
   OTG_FS_PWRCLK_Base : constant System.Address :=
     System'To_Address (16#50000E00#);
   CAN1_Base : constant System.Address :=
     System'To_Address (16#40006400#);
   CAN2_Base : constant System.Address :=
     System'To_Address (16#40006800#);
   NVIC_Base : constant System.Address :=
     System'To_Address (16#E000E000#);
   FLASH_Base : constant System.Address :=
     System'To_Address (16#40023C00#);
   EXTI_Base : constant System.Address :=
     System'To_Address (16#40013C00#);
   OTG_HS_GLOBAL_Base : constant System.Address :=
     System'To_Address (16#40040000#);
   OTG_HS_HOST_Base : constant System.Address :=
     System'To_Address (16#40040400#);
   OTG_HS_DEVICE_Base : constant System.Address :=
     System'To_Address (16#40040800#);
   OTG_HS_PWRCLK_Base : constant System.Address :=
     System'To_Address (16#40040E00#);
   LTDC_Base : constant System.Address :=
     System'To_Address (16#40016800#);
   SAI_Base : constant System.Address :=
     System'To_Address (16#40015800#);
   DMA2D_Base : constant System.Address :=
     System'To_Address (16#4002B000#);

end Interfaces.STM32;
