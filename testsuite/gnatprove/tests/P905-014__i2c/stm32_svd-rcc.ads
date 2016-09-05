--  This spec has been automatically generated from STM32F429x.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

package STM32_SVD.RCC is
   pragma Preelaborate;

   ---------------
   -- Registers --
   ---------------

   subtype CR_HSION_Field is STM32_SVD.Bit;
   subtype CR_HSIRDY_Field is STM32_SVD.Bit;
   subtype CR_HSITRIM_Field is STM32_SVD.UInt5;
   subtype CR_HSICAL_Field is STM32_SVD.Byte;
   subtype CR_HSEON_Field is STM32_SVD.Bit;
   subtype CR_HSERDY_Field is STM32_SVD.Bit;
   subtype CR_HSEBYP_Field is STM32_SVD.Bit;
   subtype CR_CSSON_Field is STM32_SVD.Bit;
   subtype CR_PLLON_Field is STM32_SVD.Bit;
   subtype CR_PLLRDY_Field is STM32_SVD.Bit;
   subtype CR_PLLI2SON_Field is STM32_SVD.Bit;
   subtype CR_PLLI2SRDY_Field is STM32_SVD.Bit;

   --  clock control register
   type CR_Register is record
      --  Internal high-speed clock enable
      HSION          : CR_HSION_Field := 16#1#;
      --  Read-only. Internal high-speed clock ready flag
      HSIRDY         : CR_HSIRDY_Field := 16#1#;
      --  unspecified
      Reserved_2_2   : STM32_SVD.Bit := 16#0#;
      --  Internal high-speed clock trimming
      HSITRIM        : CR_HSITRIM_Field := 16#10#;
      --  Read-only. Internal high-speed clock calibration
      HSICAL         : CR_HSICAL_Field := 16#0#;
      --  HSE clock enable
      HSEON          : CR_HSEON_Field := 16#0#;
      --  Read-only. HSE clock ready flag
      HSERDY         : CR_HSERDY_Field := 16#0#;
      --  HSE clock bypass
      HSEBYP         : CR_HSEBYP_Field := 16#0#;
      --  Clock security system enable
      CSSON          : CR_CSSON_Field := 16#0#;
      --  unspecified
      Reserved_20_23 : STM32_SVD.UInt4 := 16#0#;
      --  Main PLL (PLL) enable
      PLLON          : CR_PLLON_Field := 16#0#;
      --  Read-only. Main PLL (PLL) clock ready flag
      PLLRDY         : CR_PLLRDY_Field := 16#0#;
      --  PLLI2S enable
      PLLI2SON       : CR_PLLI2SON_Field := 16#0#;
      --  Read-only. PLLI2S clock ready flag
      PLLI2SRDY      : CR_PLLI2SRDY_Field := 16#0#;
      --  unspecified
      Reserved_28_31 : STM32_SVD.UInt4 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CR_Register use record
      HSION          at 0 range 0 .. 0;
      HSIRDY         at 0 range 1 .. 1;
      Reserved_2_2   at 0 range 2 .. 2;
      HSITRIM        at 0 range 3 .. 7;
      HSICAL         at 0 range 8 .. 15;
      HSEON          at 0 range 16 .. 16;
      HSERDY         at 0 range 17 .. 17;
      HSEBYP         at 0 range 18 .. 18;
      CSSON          at 0 range 19 .. 19;
      Reserved_20_23 at 0 range 20 .. 23;
      PLLON          at 0 range 24 .. 24;
      PLLRDY         at 0 range 25 .. 25;
      PLLI2SON       at 0 range 26 .. 26;
      PLLI2SRDY      at 0 range 27 .. 27;
      Reserved_28_31 at 0 range 28 .. 31;
   end record;

   subtype PLLCFGR_PLLM_Field is STM32_SVD.UInt6;
   subtype PLLCFGR_PLLN_Field is STM32_SVD.UInt9;
   subtype PLLCFGR_PLLP_Field is STM32_SVD.UInt2;
   subtype PLLCFGR_PLLSRC_Field is STM32_SVD.Bit;
   subtype PLLCFGR_PLLQ_Field is STM32_SVD.UInt4;

   --  PLL configuration register
   type PLLCFGR_Register is record
      --  Division factor for the main PLL (PLL) and audio PLL (PLLI2S) input
      --  clock
      PLLM           : PLLCFGR_PLLM_Field := 16#10#;
      --  Main PLL (PLL) multiplication factor for VCO
      PLLN           : PLLCFGR_PLLN_Field := 16#C0#;
      --  unspecified
      Reserved_15_15 : STM32_SVD.Bit := 16#0#;
      --  Main PLL (PLL) division factor for main system clock
      PLLP           : PLLCFGR_PLLP_Field := 16#0#;
      --  unspecified
      Reserved_18_21 : STM32_SVD.UInt4 := 16#0#;
      --  Main PLL(PLL) and audio PLL (PLLI2S) entry clock source
      PLLSRC         : PLLCFGR_PLLSRC_Field := 16#0#;
      --  unspecified
      Reserved_23_23 : STM32_SVD.Bit := 16#0#;
      --  Main PLL (PLL) division factor for USB OTG FS, SDIO and random number
      --  generator clocks
      PLLQ           : PLLCFGR_PLLQ_Field := 16#4#;
      --  unspecified
      Reserved_28_31 : STM32_SVD.UInt4 := 16#2#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for PLLCFGR_Register use record
      PLLM           at 0 range 0 .. 5;
      PLLN           at 0 range 6 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      PLLP           at 0 range 16 .. 17;
      Reserved_18_21 at 0 range 18 .. 21;
      PLLSRC         at 0 range 22 .. 22;
      Reserved_23_23 at 0 range 23 .. 23;
      PLLQ           at 0 range 24 .. 27;
      Reserved_28_31 at 0 range 28 .. 31;
   end record;

   subtype CFGR_SW_Field is STM32_SVD.UInt2;
   subtype CFGR_SWS_Field is STM32_SVD.UInt2;
   subtype CFGR_HPRE_Field is STM32_SVD.UInt4;
   --  CFGR_PPRE array element
   subtype CFGR_PPRE_Element is STM32_SVD.UInt3;

   --  CFGR_PPRE array
   type CFGR_PPRE_Field_Array is array (1 .. 2) of CFGR_PPRE_Element
     with Component_Size => 3, Size => 6;

   --  Type definition for CFGR_PPRE
   type CFGR_PPRE_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  PPRE as a value
            Val : STM32_SVD.UInt6;
         when True =>
            --  PPRE as an array
            Arr : CFGR_PPRE_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 6;

   for CFGR_PPRE_Field use record
      Val at 0 range 0 .. 5;
      Arr at 0 range 0 .. 5;
   end record;

   subtype CFGR_RTCPRE_Field is STM32_SVD.UInt5;
   subtype CFGR_MCO1_Field is STM32_SVD.UInt2;
   subtype CFGR_I2SSRC_Field is STM32_SVD.Bit;
   subtype CFGR_MCO1PRE_Field is STM32_SVD.UInt3;
   subtype CFGR_MCO2PRE_Field is STM32_SVD.UInt3;
   subtype CFGR_MCO2_Field is STM32_SVD.UInt2;

   --  clock configuration register
   type CFGR_Register is record
      --  System clock switch
      SW           : CFGR_SW_Field := 16#0#;
      --  Read-only. System clock switch status
      SWS          : CFGR_SWS_Field := 16#0#;
      --  AHB prescaler
      HPRE         : CFGR_HPRE_Field := 16#0#;
      --  unspecified
      Reserved_8_9 : STM32_SVD.UInt2 := 16#0#;
      --  APB Low speed prescaler (APB1)
      PPRE         : CFGR_PPRE_Field := (As_Array => False, Val => 16#0#);
      --  HSE division factor for RTC clock
      RTCPRE       : CFGR_RTCPRE_Field := 16#0#;
      --  Microcontroller clock output 1
      MCO1         : CFGR_MCO1_Field := 16#0#;
      --  I2S clock selection
      I2SSRC       : CFGR_I2SSRC_Field := 16#0#;
      --  MCO1 prescaler
      MCO1PRE      : CFGR_MCO1PRE_Field := 16#0#;
      --  MCO2 prescaler
      MCO2PRE      : CFGR_MCO2PRE_Field := 16#0#;
      --  Microcontroller clock output 2
      MCO2         : CFGR_MCO2_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CFGR_Register use record
      SW           at 0 range 0 .. 1;
      SWS          at 0 range 2 .. 3;
      HPRE         at 0 range 4 .. 7;
      Reserved_8_9 at 0 range 8 .. 9;
      PPRE         at 0 range 10 .. 15;
      RTCPRE       at 0 range 16 .. 20;
      MCO1         at 0 range 21 .. 22;
      I2SSRC       at 0 range 23 .. 23;
      MCO1PRE      at 0 range 24 .. 26;
      MCO2PRE      at 0 range 27 .. 29;
      MCO2         at 0 range 30 .. 31;
   end record;

   subtype CIR_LSIRDYF_Field is STM32_SVD.Bit;
   subtype CIR_LSERDYF_Field is STM32_SVD.Bit;
   subtype CIR_HSIRDYF_Field is STM32_SVD.Bit;
   subtype CIR_HSERDYF_Field is STM32_SVD.Bit;
   subtype CIR_PLLRDYF_Field is STM32_SVD.Bit;
   subtype CIR_PLLI2SRDYF_Field is STM32_SVD.Bit;
   subtype CIR_PLLSAIRDYF_Field is STM32_SVD.Bit;
   subtype CIR_CSSF_Field is STM32_SVD.Bit;
   subtype CIR_LSIRDYIE_Field is STM32_SVD.Bit;
   subtype CIR_LSERDYIE_Field is STM32_SVD.Bit;
   subtype CIR_HSIRDYIE_Field is STM32_SVD.Bit;
   subtype CIR_HSERDYIE_Field is STM32_SVD.Bit;
   subtype CIR_PLLRDYIE_Field is STM32_SVD.Bit;
   subtype CIR_PLLI2SRDYIE_Field is STM32_SVD.Bit;
   subtype CIR_PLLSAIRDYIE_Field is STM32_SVD.Bit;
   subtype CIR_LSIRDYC_Field is STM32_SVD.Bit;
   subtype CIR_LSERDYC_Field is STM32_SVD.Bit;
   subtype CIR_HSIRDYC_Field is STM32_SVD.Bit;
   subtype CIR_HSERDYC_Field is STM32_SVD.Bit;
   subtype CIR_PLLRDYC_Field is STM32_SVD.Bit;
   subtype CIR_PLLI2SRDYC_Field is STM32_SVD.Bit;
   subtype CIR_PLLSAIRDYC_Field is STM32_SVD.Bit;
   subtype CIR_CSSC_Field is STM32_SVD.Bit;

   --  clock interrupt register
   type CIR_Register is record
      --  Read-only. LSI ready interrupt flag
      LSIRDYF        : CIR_LSIRDYF_Field := 16#0#;
      --  Read-only. LSE ready interrupt flag
      LSERDYF        : CIR_LSERDYF_Field := 16#0#;
      --  Read-only. HSI ready interrupt flag
      HSIRDYF        : CIR_HSIRDYF_Field := 16#0#;
      --  Read-only. HSE ready interrupt flag
      HSERDYF        : CIR_HSERDYF_Field := 16#0#;
      --  Read-only. Main PLL (PLL) ready interrupt flag
      PLLRDYF        : CIR_PLLRDYF_Field := 16#0#;
      --  Read-only. PLLI2S ready interrupt flag
      PLLI2SRDYF     : CIR_PLLI2SRDYF_Field := 16#0#;
      --  Read-only. PLLSAI ready interrupt flag
      PLLSAIRDYF     : CIR_PLLSAIRDYF_Field := 16#0#;
      --  Read-only. Clock security system interrupt flag
      CSSF           : CIR_CSSF_Field := 16#0#;
      --  LSI ready interrupt enable
      LSIRDYIE       : CIR_LSIRDYIE_Field := 16#0#;
      --  LSE ready interrupt enable
      LSERDYIE       : CIR_LSERDYIE_Field := 16#0#;
      --  HSI ready interrupt enable
      HSIRDYIE       : CIR_HSIRDYIE_Field := 16#0#;
      --  HSE ready interrupt enable
      HSERDYIE       : CIR_HSERDYIE_Field := 16#0#;
      --  Main PLL (PLL) ready interrupt enable
      PLLRDYIE       : CIR_PLLRDYIE_Field := 16#0#;
      --  PLLI2S ready interrupt enable
      PLLI2SRDYIE    : CIR_PLLI2SRDYIE_Field := 16#0#;
      --  PLLSAI Ready Interrupt Enable
      PLLSAIRDYIE    : CIR_PLLSAIRDYIE_Field := 16#0#;
      --  unspecified
      Reserved_15_15 : STM32_SVD.Bit := 16#0#;
      --  Write-only. LSI ready interrupt clear
      LSIRDYC        : CIR_LSIRDYC_Field := 16#0#;
      --  Write-only. LSE ready interrupt clear
      LSERDYC        : CIR_LSERDYC_Field := 16#0#;
      --  Write-only. HSI ready interrupt clear
      HSIRDYC        : CIR_HSIRDYC_Field := 16#0#;
      --  Write-only. HSE ready interrupt clear
      HSERDYC        : CIR_HSERDYC_Field := 16#0#;
      --  Write-only. Main PLL(PLL) ready interrupt clear
      PLLRDYC        : CIR_PLLRDYC_Field := 16#0#;
      --  Write-only. PLLI2S ready interrupt clear
      PLLI2SRDYC     : CIR_PLLI2SRDYC_Field := 16#0#;
      --  Write-only. PLLSAI Ready Interrupt Clear
      PLLSAIRDYC     : CIR_PLLSAIRDYC_Field := 16#0#;
      --  Write-only. Clock security system interrupt clear
      CSSC           : CIR_CSSC_Field := 16#0#;
      --  unspecified
      Reserved_24_31 : STM32_SVD.Byte := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CIR_Register use record
      LSIRDYF        at 0 range 0 .. 0;
      LSERDYF        at 0 range 1 .. 1;
      HSIRDYF        at 0 range 2 .. 2;
      HSERDYF        at 0 range 3 .. 3;
      PLLRDYF        at 0 range 4 .. 4;
      PLLI2SRDYF     at 0 range 5 .. 5;
      PLLSAIRDYF     at 0 range 6 .. 6;
      CSSF           at 0 range 7 .. 7;
      LSIRDYIE       at 0 range 8 .. 8;
      LSERDYIE       at 0 range 9 .. 9;
      HSIRDYIE       at 0 range 10 .. 10;
      HSERDYIE       at 0 range 11 .. 11;
      PLLRDYIE       at 0 range 12 .. 12;
      PLLI2SRDYIE    at 0 range 13 .. 13;
      PLLSAIRDYIE    at 0 range 14 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      LSIRDYC        at 0 range 16 .. 16;
      LSERDYC        at 0 range 17 .. 17;
      HSIRDYC        at 0 range 18 .. 18;
      HSERDYC        at 0 range 19 .. 19;
      PLLRDYC        at 0 range 20 .. 20;
      PLLI2SRDYC     at 0 range 21 .. 21;
      PLLSAIRDYC     at 0 range 22 .. 22;
      CSSC           at 0 range 23 .. 23;
      Reserved_24_31 at 0 range 24 .. 31;
   end record;

   subtype AHB1RSTR_GPIOARST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOBRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOCRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIODRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOERST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOFRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOGRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOHRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOIRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOJRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_GPIOKRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_CRCRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_DMA1RST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_DMA2RST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_DMA2DRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_ETHMACRST_Field is STM32_SVD.Bit;
   subtype AHB1RSTR_OTGHSRST_Field is STM32_SVD.Bit;

   --  AHB1 peripheral reset register
   type AHB1RSTR_Register is record
      --  IO port A reset
      GPIOARST       : AHB1RSTR_GPIOARST_Field := 16#0#;
      --  IO port B reset
      GPIOBRST       : AHB1RSTR_GPIOBRST_Field := 16#0#;
      --  IO port C reset
      GPIOCRST       : AHB1RSTR_GPIOCRST_Field := 16#0#;
      --  IO port D reset
      GPIODRST       : AHB1RSTR_GPIODRST_Field := 16#0#;
      --  IO port E reset
      GPIOERST       : AHB1RSTR_GPIOERST_Field := 16#0#;
      --  IO port F reset
      GPIOFRST       : AHB1RSTR_GPIOFRST_Field := 16#0#;
      --  IO port G reset
      GPIOGRST       : AHB1RSTR_GPIOGRST_Field := 16#0#;
      --  IO port H reset
      GPIOHRST       : AHB1RSTR_GPIOHRST_Field := 16#0#;
      --  IO port I reset
      GPIOIRST       : AHB1RSTR_GPIOIRST_Field := 16#0#;
      --  IO port J reset
      GPIOJRST       : AHB1RSTR_GPIOJRST_Field := 16#0#;
      --  IO port K reset
      GPIOKRST       : AHB1RSTR_GPIOKRST_Field := 16#0#;
      --  unspecified
      Reserved_11_11 : STM32_SVD.Bit := 16#0#;
      --  CRC reset
      CRCRST         : AHB1RSTR_CRCRST_Field := 16#0#;
      --  unspecified
      Reserved_13_20 : STM32_SVD.Byte := 16#0#;
      --  DMA2 reset
      DMA1RST        : AHB1RSTR_DMA1RST_Field := 16#0#;
      --  DMA2 reset
      DMA2RST        : AHB1RSTR_DMA2RST_Field := 16#0#;
      --  DMA2D reset
      DMA2DRST       : AHB1RSTR_DMA2DRST_Field := 16#0#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  Ethernet MAC reset
      ETHMACRST      : AHB1RSTR_ETHMACRST_Field := 16#0#;
      --  unspecified
      Reserved_26_28 : STM32_SVD.UInt3 := 16#0#;
      --  USB OTG HS module reset
      OTGHSRST       : AHB1RSTR_OTGHSRST_Field := 16#0#;
      --  unspecified
      Reserved_30_31 : STM32_SVD.UInt2 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB1RSTR_Register use record
      GPIOARST       at 0 range 0 .. 0;
      GPIOBRST       at 0 range 1 .. 1;
      GPIOCRST       at 0 range 2 .. 2;
      GPIODRST       at 0 range 3 .. 3;
      GPIOERST       at 0 range 4 .. 4;
      GPIOFRST       at 0 range 5 .. 5;
      GPIOGRST       at 0 range 6 .. 6;
      GPIOHRST       at 0 range 7 .. 7;
      GPIOIRST       at 0 range 8 .. 8;
      GPIOJRST       at 0 range 9 .. 9;
      GPIOKRST       at 0 range 10 .. 10;
      Reserved_11_11 at 0 range 11 .. 11;
      CRCRST         at 0 range 12 .. 12;
      Reserved_13_20 at 0 range 13 .. 20;
      DMA1RST        at 0 range 21 .. 21;
      DMA2RST        at 0 range 22 .. 22;
      DMA2DRST       at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      ETHMACRST      at 0 range 25 .. 25;
      Reserved_26_28 at 0 range 26 .. 28;
      OTGHSRST       at 0 range 29 .. 29;
      Reserved_30_31 at 0 range 30 .. 31;
   end record;

   subtype AHB2RSTR_DCMIRST_Field is STM32_SVD.Bit;
   subtype AHB2RSTR_RNGRST_Field is STM32_SVD.Bit;
   subtype AHB2RSTR_OTGFSRST_Field is STM32_SVD.Bit;

   --  AHB2 peripheral reset register
   type AHB2RSTR_Register is record
      --  Camera interface reset
      DCMIRST       : AHB2RSTR_DCMIRST_Field := 16#0#;
      --  unspecified
      Reserved_1_5  : STM32_SVD.UInt5 := 16#0#;
      --  Random number generator module reset
      RNGRST        : AHB2RSTR_RNGRST_Field := 16#0#;
      --  USB OTG FS module reset
      OTGFSRST      : AHB2RSTR_OTGFSRST_Field := 16#0#;
      --  unspecified
      Reserved_8_31 : STM32_SVD.UInt24 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB2RSTR_Register use record
      DCMIRST       at 0 range 0 .. 0;
      Reserved_1_5  at 0 range 1 .. 5;
      RNGRST        at 0 range 6 .. 6;
      OTGFSRST      at 0 range 7 .. 7;
      Reserved_8_31 at 0 range 8 .. 31;
   end record;

   subtype AHB3RSTR_FMCRST_Field is STM32_SVD.Bit;

   --  AHB3 peripheral reset register
   type AHB3RSTR_Register is record
      --  Flexible memory controller module reset
      FMCRST        : AHB3RSTR_FMCRST_Field := 16#0#;
      --  unspecified
      Reserved_1_31 : STM32_SVD.UInt31 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB3RSTR_Register use record
      FMCRST        at 0 range 0 .. 0;
      Reserved_1_31 at 0 range 1 .. 31;
   end record;

   subtype APB1RSTR_TIM2RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM3RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM4RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM5RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM6RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM7RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM12RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM13RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_TIM14RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_WWDGRST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_SPI2RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_SPI3RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART2RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART3RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART4RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART5RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_I2C1RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_I2C2RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_I2C3RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_CAN1RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_CAN2RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_PWRRST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_DACRST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART7RST_Field is STM32_SVD.Bit;
   subtype APB1RSTR_UART8RST_Field is STM32_SVD.Bit;

   --  APB1 peripheral reset register
   type APB1RSTR_Register is record
      --  TIM2 reset
      TIM2RST        : APB1RSTR_TIM2RST_Field := 16#0#;
      --  TIM3 reset
      TIM3RST        : APB1RSTR_TIM3RST_Field := 16#0#;
      --  TIM4 reset
      TIM4RST        : APB1RSTR_TIM4RST_Field := 16#0#;
      --  TIM5 reset
      TIM5RST        : APB1RSTR_TIM5RST_Field := 16#0#;
      --  TIM6 reset
      TIM6RST        : APB1RSTR_TIM6RST_Field := 16#0#;
      --  TIM7 reset
      TIM7RST        : APB1RSTR_TIM7RST_Field := 16#0#;
      --  TIM12 reset
      TIM12RST       : APB1RSTR_TIM12RST_Field := 16#0#;
      --  TIM13 reset
      TIM13RST       : APB1RSTR_TIM13RST_Field := 16#0#;
      --  TIM14 reset
      TIM14RST       : APB1RSTR_TIM14RST_Field := 16#0#;
      --  unspecified
      Reserved_9_10  : STM32_SVD.UInt2 := 16#0#;
      --  Window watchdog reset
      WWDGRST        : APB1RSTR_WWDGRST_Field := 16#0#;
      --  unspecified
      Reserved_12_13 : STM32_SVD.UInt2 := 16#0#;
      --  SPI 2 reset
      SPI2RST        : APB1RSTR_SPI2RST_Field := 16#0#;
      --  SPI 3 reset
      SPI3RST        : APB1RSTR_SPI3RST_Field := 16#0#;
      --  unspecified
      Reserved_16_16 : STM32_SVD.Bit := 16#0#;
      --  USART 2 reset
      UART2RST       : APB1RSTR_UART2RST_Field := 16#0#;
      --  USART 3 reset
      UART3RST       : APB1RSTR_UART3RST_Field := 16#0#;
      --  USART 4 reset
      UART4RST       : APB1RSTR_UART4RST_Field := 16#0#;
      --  USART 5 reset
      UART5RST       : APB1RSTR_UART5RST_Field := 16#0#;
      --  I2C 1 reset
      I2C1RST        : APB1RSTR_I2C1RST_Field := 16#0#;
      --  I2C 2 reset
      I2C2RST        : APB1RSTR_I2C2RST_Field := 16#0#;
      --  I2C3 reset
      I2C3RST        : APB1RSTR_I2C3RST_Field := 16#0#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  CAN1 reset
      CAN1RST        : APB1RSTR_CAN1RST_Field := 16#0#;
      --  CAN2 reset
      CAN2RST        : APB1RSTR_CAN2RST_Field := 16#0#;
      --  unspecified
      Reserved_27_27 : STM32_SVD.Bit := 16#0#;
      --  Power interface reset
      PWRRST         : APB1RSTR_PWRRST_Field := 16#0#;
      --  DAC reset
      DACRST         : APB1RSTR_DACRST_Field := 16#0#;
      --  UART7 reset
      UART7RST       : APB1RSTR_UART7RST_Field := 16#0#;
      --  UART8 reset
      UART8RST       : APB1RSTR_UART8RST_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB1RSTR_Register use record
      TIM2RST        at 0 range 0 .. 0;
      TIM3RST        at 0 range 1 .. 1;
      TIM4RST        at 0 range 2 .. 2;
      TIM5RST        at 0 range 3 .. 3;
      TIM6RST        at 0 range 4 .. 4;
      TIM7RST        at 0 range 5 .. 5;
      TIM12RST       at 0 range 6 .. 6;
      TIM13RST       at 0 range 7 .. 7;
      TIM14RST       at 0 range 8 .. 8;
      Reserved_9_10  at 0 range 9 .. 10;
      WWDGRST        at 0 range 11 .. 11;
      Reserved_12_13 at 0 range 12 .. 13;
      SPI2RST        at 0 range 14 .. 14;
      SPI3RST        at 0 range 15 .. 15;
      Reserved_16_16 at 0 range 16 .. 16;
      UART2RST       at 0 range 17 .. 17;
      UART3RST       at 0 range 18 .. 18;
      UART4RST       at 0 range 19 .. 19;
      UART5RST       at 0 range 20 .. 20;
      I2C1RST        at 0 range 21 .. 21;
      I2C2RST        at 0 range 22 .. 22;
      I2C3RST        at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      CAN1RST        at 0 range 25 .. 25;
      CAN2RST        at 0 range 26 .. 26;
      Reserved_27_27 at 0 range 27 .. 27;
      PWRRST         at 0 range 28 .. 28;
      DACRST         at 0 range 29 .. 29;
      UART7RST       at 0 range 30 .. 30;
      UART8RST       at 0 range 31 .. 31;
   end record;

   subtype APB2RSTR_TIM1RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_TIM8RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_USART1RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_USART6RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_ADCRST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SDIORST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SPI1RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SPI4RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SYSCFGRST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_TIM9RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_TIM10RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_TIM11RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SPI5RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SPI6RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_SAI1RST_Field is STM32_SVD.Bit;
   subtype APB2RSTR_LTDCRST_Field is STM32_SVD.Bit;

   --  APB2 peripheral reset register
   type APB2RSTR_Register is record
      --  TIM1 reset
      TIM1RST        : APB2RSTR_TIM1RST_Field := 16#0#;
      --  TIM8 reset
      TIM8RST        : APB2RSTR_TIM8RST_Field := 16#0#;
      --  unspecified
      Reserved_2_3   : STM32_SVD.UInt2 := 16#0#;
      --  USART1 reset
      USART1RST      : APB2RSTR_USART1RST_Field := 16#0#;
      --  USART6 reset
      USART6RST      : APB2RSTR_USART6RST_Field := 16#0#;
      --  unspecified
      Reserved_6_7   : STM32_SVD.UInt2 := 16#0#;
      --  ADC interface reset (common to all ADCs)
      ADCRST         : APB2RSTR_ADCRST_Field := 16#0#;
      --  unspecified
      Reserved_9_10  : STM32_SVD.UInt2 := 16#0#;
      --  SDIO reset
      SDIORST        : APB2RSTR_SDIORST_Field := 16#0#;
      --  SPI 1 reset
      SPI1RST        : APB2RSTR_SPI1RST_Field := 16#0#;
      --  SPI4 reset
      SPI4RST        : APB2RSTR_SPI4RST_Field := 16#0#;
      --  System configuration controller reset
      SYSCFGRST      : APB2RSTR_SYSCFGRST_Field := 16#0#;
      --  unspecified
      Reserved_15_15 : STM32_SVD.Bit := 16#0#;
      --  TIM9 reset
      TIM9RST        : APB2RSTR_TIM9RST_Field := 16#0#;
      --  TIM10 reset
      TIM10RST       : APB2RSTR_TIM10RST_Field := 16#0#;
      --  TIM11 reset
      TIM11RST       : APB2RSTR_TIM11RST_Field := 16#0#;
      --  unspecified
      Reserved_19_19 : STM32_SVD.Bit := 16#0#;
      --  SPI5 reset
      SPI5RST        : APB2RSTR_SPI5RST_Field := 16#0#;
      --  SPI6 reset
      SPI6RST        : APB2RSTR_SPI6RST_Field := 16#0#;
      --  SAI1 reset
      SAI1RST        : APB2RSTR_SAI1RST_Field := 16#0#;
      --  unspecified
      Reserved_23_25 : STM32_SVD.UInt3 := 16#0#;
      --  LTDC reset
      LTDCRST        : APB2RSTR_LTDCRST_Field := 16#0#;
      --  unspecified
      Reserved_27_31 : STM32_SVD.UInt5 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB2RSTR_Register use record
      TIM1RST        at 0 range 0 .. 0;
      TIM8RST        at 0 range 1 .. 1;
      Reserved_2_3   at 0 range 2 .. 3;
      USART1RST      at 0 range 4 .. 4;
      USART6RST      at 0 range 5 .. 5;
      Reserved_6_7   at 0 range 6 .. 7;
      ADCRST         at 0 range 8 .. 8;
      Reserved_9_10  at 0 range 9 .. 10;
      SDIORST        at 0 range 11 .. 11;
      SPI1RST        at 0 range 12 .. 12;
      SPI4RST        at 0 range 13 .. 13;
      SYSCFGRST      at 0 range 14 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      TIM9RST        at 0 range 16 .. 16;
      TIM10RST       at 0 range 17 .. 17;
      TIM11RST       at 0 range 18 .. 18;
      Reserved_19_19 at 0 range 19 .. 19;
      SPI5RST        at 0 range 20 .. 20;
      SPI6RST        at 0 range 21 .. 21;
      SAI1RST        at 0 range 22 .. 22;
      Reserved_23_25 at 0 range 23 .. 25;
      LTDCRST        at 0 range 26 .. 26;
      Reserved_27_31 at 0 range 27 .. 31;
   end record;

   subtype AHB1ENR_GPIOAEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOBEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOCEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIODEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOEEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOFEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOGEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOHEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOIEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOJEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_GPIOKEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_CRCEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_BKPSRAMEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_CCMDATARAMEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_DMA1EN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_DMA2EN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_DMA2DEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_ETHMACEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_ETHMACTXEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_ETHMACRXEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_ETHMACPTPEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_OTGHSEN_Field is STM32_SVD.Bit;
   subtype AHB1ENR_OTGHSULPIEN_Field is STM32_SVD.Bit;

   --  AHB1 peripheral clock register
   type AHB1ENR_Register is record
      --  IO port A clock enable
      GPIOAEN        : AHB1ENR_GPIOAEN_Field := 16#0#;
      --  IO port B clock enable
      GPIOBEN        : AHB1ENR_GPIOBEN_Field := 16#0#;
      --  IO port C clock enable
      GPIOCEN        : AHB1ENR_GPIOCEN_Field := 16#0#;
      --  IO port D clock enable
      GPIODEN        : AHB1ENR_GPIODEN_Field := 16#0#;
      --  IO port E clock enable
      GPIOEEN        : AHB1ENR_GPIOEEN_Field := 16#0#;
      --  IO port F clock enable
      GPIOFEN        : AHB1ENR_GPIOFEN_Field := 16#0#;
      --  IO port G clock enable
      GPIOGEN        : AHB1ENR_GPIOGEN_Field := 16#0#;
      --  IO port H clock enable
      GPIOHEN        : AHB1ENR_GPIOHEN_Field := 16#0#;
      --  IO port I clock enable
      GPIOIEN        : AHB1ENR_GPIOIEN_Field := 16#0#;
      --  IO port J clock enable
      GPIOJEN        : AHB1ENR_GPIOJEN_Field := 16#0#;
      --  IO port K clock enable
      GPIOKEN        : AHB1ENR_GPIOKEN_Field := 16#0#;
      --  unspecified
      Reserved_11_11 : STM32_SVD.Bit := 16#0#;
      --  CRC clock enable
      CRCEN          : AHB1ENR_CRCEN_Field := 16#0#;
      --  unspecified
      Reserved_13_17 : STM32_SVD.UInt5 := 16#0#;
      --  Backup SRAM interface clock enable
      BKPSRAMEN      : AHB1ENR_BKPSRAMEN_Field := 16#0#;
      --  unspecified
      Reserved_19_19 : STM32_SVD.Bit := 16#0#;
      --  CCM data RAM clock enable
      CCMDATARAMEN   : AHB1ENR_CCMDATARAMEN_Field := 16#1#;
      --  DMA1 clock enable
      DMA1EN         : AHB1ENR_DMA1EN_Field := 16#0#;
      --  DMA2 clock enable
      DMA2EN         : AHB1ENR_DMA2EN_Field := 16#0#;
      --  DMA2D clock enable
      DMA2DEN        : AHB1ENR_DMA2DEN_Field := 16#0#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  Ethernet MAC clock enable
      ETHMACEN       : AHB1ENR_ETHMACEN_Field := 16#0#;
      --  Ethernet Transmission clock enable
      ETHMACTXEN     : AHB1ENR_ETHMACTXEN_Field := 16#0#;
      --  Ethernet Reception clock enable
      ETHMACRXEN     : AHB1ENR_ETHMACRXEN_Field := 16#0#;
      --  Ethernet PTP clock enable
      ETHMACPTPEN    : AHB1ENR_ETHMACPTPEN_Field := 16#0#;
      --  USB OTG HS clock enable
      OTGHSEN        : AHB1ENR_OTGHSEN_Field := 16#0#;
      --  USB OTG HSULPI clock enable
      OTGHSULPIEN    : AHB1ENR_OTGHSULPIEN_Field := 16#0#;
      --  unspecified
      Reserved_31_31 : STM32_SVD.Bit := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB1ENR_Register use record
      GPIOAEN        at 0 range 0 .. 0;
      GPIOBEN        at 0 range 1 .. 1;
      GPIOCEN        at 0 range 2 .. 2;
      GPIODEN        at 0 range 3 .. 3;
      GPIOEEN        at 0 range 4 .. 4;
      GPIOFEN        at 0 range 5 .. 5;
      GPIOGEN        at 0 range 6 .. 6;
      GPIOHEN        at 0 range 7 .. 7;
      GPIOIEN        at 0 range 8 .. 8;
      GPIOJEN        at 0 range 9 .. 9;
      GPIOKEN        at 0 range 10 .. 10;
      Reserved_11_11 at 0 range 11 .. 11;
      CRCEN          at 0 range 12 .. 12;
      Reserved_13_17 at 0 range 13 .. 17;
      BKPSRAMEN      at 0 range 18 .. 18;
      Reserved_19_19 at 0 range 19 .. 19;
      CCMDATARAMEN   at 0 range 20 .. 20;
      DMA1EN         at 0 range 21 .. 21;
      DMA2EN         at 0 range 22 .. 22;
      DMA2DEN        at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      ETHMACEN       at 0 range 25 .. 25;
      ETHMACTXEN     at 0 range 26 .. 26;
      ETHMACRXEN     at 0 range 27 .. 27;
      ETHMACPTPEN    at 0 range 28 .. 28;
      OTGHSEN        at 0 range 29 .. 29;
      OTGHSULPIEN    at 0 range 30 .. 30;
      Reserved_31_31 at 0 range 31 .. 31;
   end record;

   subtype AHB2ENR_DCMIEN_Field is STM32_SVD.Bit;
   subtype AHB2ENR_RNGEN_Field is STM32_SVD.Bit;
   subtype AHB2ENR_OTGFSEN_Field is STM32_SVD.Bit;

   --  AHB2 peripheral clock enable register
   type AHB2ENR_Register is record
      --  Camera interface enable
      DCMIEN        : AHB2ENR_DCMIEN_Field := 16#0#;
      --  unspecified
      Reserved_1_5  : STM32_SVD.UInt5 := 16#0#;
      --  Random number generator clock enable
      RNGEN         : AHB2ENR_RNGEN_Field := 16#0#;
      --  USB OTG FS clock enable
      OTGFSEN       : AHB2ENR_OTGFSEN_Field := 16#0#;
      --  unspecified
      Reserved_8_31 : STM32_SVD.UInt24 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB2ENR_Register use record
      DCMIEN        at 0 range 0 .. 0;
      Reserved_1_5  at 0 range 1 .. 5;
      RNGEN         at 0 range 6 .. 6;
      OTGFSEN       at 0 range 7 .. 7;
      Reserved_8_31 at 0 range 8 .. 31;
   end record;

   subtype AHB3ENR_FMCEN_Field is STM32_SVD.Bit;

   --  AHB3 peripheral clock enable register
   type AHB3ENR_Register is record
      --  Flexible memory controller module clock enable
      FMCEN         : AHB3ENR_FMCEN_Field := 16#0#;
      --  unspecified
      Reserved_1_31 : STM32_SVD.UInt31 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB3ENR_Register use record
      FMCEN         at 0 range 0 .. 0;
      Reserved_1_31 at 0 range 1 .. 31;
   end record;

   subtype APB1ENR_TIM2EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM3EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM4EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM5EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM6EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM7EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM12EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM13EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_TIM14EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_WWDGEN_Field is STM32_SVD.Bit;
   subtype APB1ENR_SPI2EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_SPI3EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_USART2EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_USART3EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_UART4EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_UART5EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_I2C1EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_I2C2EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_I2C3EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_CAN1EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_CAN2EN_Field is STM32_SVD.Bit;
   subtype APB1ENR_PWREN_Field is STM32_SVD.Bit;
   subtype APB1ENR_DACEN_Field is STM32_SVD.Bit;
   subtype APB1ENR_UART7ENR_Field is STM32_SVD.Bit;
   subtype APB1ENR_UART8ENR_Field is STM32_SVD.Bit;

   --  APB1 peripheral clock enable register
   type APB1ENR_Register is record
      --  TIM2 clock enable
      TIM2EN         : APB1ENR_TIM2EN_Field := 16#0#;
      --  TIM3 clock enable
      TIM3EN         : APB1ENR_TIM3EN_Field := 16#0#;
      --  TIM4 clock enable
      TIM4EN         : APB1ENR_TIM4EN_Field := 16#0#;
      --  TIM5 clock enable
      TIM5EN         : APB1ENR_TIM5EN_Field := 16#0#;
      --  TIM6 clock enable
      TIM6EN         : APB1ENR_TIM6EN_Field := 16#0#;
      --  TIM7 clock enable
      TIM7EN         : APB1ENR_TIM7EN_Field := 16#0#;
      --  TIM12 clock enable
      TIM12EN        : APB1ENR_TIM12EN_Field := 16#0#;
      --  TIM13 clock enable
      TIM13EN        : APB1ENR_TIM13EN_Field := 16#0#;
      --  TIM14 clock enable
      TIM14EN        : APB1ENR_TIM14EN_Field := 16#0#;
      --  unspecified
      Reserved_9_10  : STM32_SVD.UInt2 := 16#0#;
      --  Window watchdog clock enable
      WWDGEN         : APB1ENR_WWDGEN_Field := 16#0#;
      --  unspecified
      Reserved_12_13 : STM32_SVD.UInt2 := 16#0#;
      --  SPI2 clock enable
      SPI2EN         : APB1ENR_SPI2EN_Field := 16#0#;
      --  SPI3 clock enable
      SPI3EN         : APB1ENR_SPI3EN_Field := 16#0#;
      --  unspecified
      Reserved_16_16 : STM32_SVD.Bit := 16#0#;
      --  USART 2 clock enable
      USART2EN       : APB1ENR_USART2EN_Field := 16#0#;
      --  USART3 clock enable
      USART3EN       : APB1ENR_USART3EN_Field := 16#0#;
      --  UART4 clock enable
      UART4EN        : APB1ENR_UART4EN_Field := 16#0#;
      --  UART5 clock enable
      UART5EN        : APB1ENR_UART5EN_Field := 16#0#;
      --  I2C1 clock enable
      I2C1EN         : APB1ENR_I2C1EN_Field := 16#0#;
      --  I2C2 clock enable
      I2C2EN         : APB1ENR_I2C2EN_Field := 16#0#;
      --  I2C3 clock enable
      I2C3EN         : APB1ENR_I2C3EN_Field := 16#0#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  CAN 1 clock enable
      CAN1EN         : APB1ENR_CAN1EN_Field := 16#0#;
      --  CAN 2 clock enable
      CAN2EN         : APB1ENR_CAN2EN_Field := 16#0#;
      --  unspecified
      Reserved_27_27 : STM32_SVD.Bit := 16#0#;
      --  Power interface clock enable
      PWREN          : APB1ENR_PWREN_Field := 16#0#;
      --  DAC interface clock enable
      DACEN          : APB1ENR_DACEN_Field := 16#0#;
      --  UART7 clock enable
      UART7ENR       : APB1ENR_UART7ENR_Field := 16#0#;
      --  UART8 clock enable
      UART8ENR       : APB1ENR_UART8ENR_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB1ENR_Register use record
      TIM2EN         at 0 range 0 .. 0;
      TIM3EN         at 0 range 1 .. 1;
      TIM4EN         at 0 range 2 .. 2;
      TIM5EN         at 0 range 3 .. 3;
      TIM6EN         at 0 range 4 .. 4;
      TIM7EN         at 0 range 5 .. 5;
      TIM12EN        at 0 range 6 .. 6;
      TIM13EN        at 0 range 7 .. 7;
      TIM14EN        at 0 range 8 .. 8;
      Reserved_9_10  at 0 range 9 .. 10;
      WWDGEN         at 0 range 11 .. 11;
      Reserved_12_13 at 0 range 12 .. 13;
      SPI2EN         at 0 range 14 .. 14;
      SPI3EN         at 0 range 15 .. 15;
      Reserved_16_16 at 0 range 16 .. 16;
      USART2EN       at 0 range 17 .. 17;
      USART3EN       at 0 range 18 .. 18;
      UART4EN        at 0 range 19 .. 19;
      UART5EN        at 0 range 20 .. 20;
      I2C1EN         at 0 range 21 .. 21;
      I2C2EN         at 0 range 22 .. 22;
      I2C3EN         at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      CAN1EN         at 0 range 25 .. 25;
      CAN2EN         at 0 range 26 .. 26;
      Reserved_27_27 at 0 range 27 .. 27;
      PWREN          at 0 range 28 .. 28;
      DACEN          at 0 range 29 .. 29;
      UART7ENR       at 0 range 30 .. 30;
      UART8ENR       at 0 range 31 .. 31;
   end record;

   subtype APB2ENR_TIM1EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_TIM8EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_USART1EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_USART6EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_ADC1EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_ADC2EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_ADC3EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_SDIOEN_Field is STM32_SVD.Bit;
   subtype APB2ENR_SPI1EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_SPI4ENR_Field is STM32_SVD.Bit;
   subtype APB2ENR_SYSCFGEN_Field is STM32_SVD.Bit;
   subtype APB2ENR_TIM9EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_TIM10EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_TIM11EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_SPI5ENR_Field is STM32_SVD.Bit;
   subtype APB2ENR_SPI6ENR_Field is STM32_SVD.Bit;
   subtype APB2ENR_SAI1EN_Field is STM32_SVD.Bit;
   subtype APB2ENR_LTDCEN_Field is STM32_SVD.Bit;

   --  APB2 peripheral clock enable register
   type APB2ENR_Register is record
      --  TIM1 clock enable
      TIM1EN         : APB2ENR_TIM1EN_Field := 16#0#;
      --  TIM8 clock enable
      TIM8EN         : APB2ENR_TIM8EN_Field := 16#0#;
      --  unspecified
      Reserved_2_3   : STM32_SVD.UInt2 := 16#0#;
      --  USART1 clock enable
      USART1EN       : APB2ENR_USART1EN_Field := 16#0#;
      --  USART6 clock enable
      USART6EN       : APB2ENR_USART6EN_Field := 16#0#;
      --  unspecified
      Reserved_6_7   : STM32_SVD.UInt2 := 16#0#;
      --  ADC1 clock enable
      ADC1EN         : APB2ENR_ADC1EN_Field := 16#0#;
      --  ADC2 clock enable
      ADC2EN         : APB2ENR_ADC2EN_Field := 16#0#;
      --  ADC3 clock enable
      ADC3EN         : APB2ENR_ADC3EN_Field := 16#0#;
      --  SDIO clock enable
      SDIOEN         : APB2ENR_SDIOEN_Field := 16#0#;
      --  SPI1 clock enable
      SPI1EN         : APB2ENR_SPI1EN_Field := 16#0#;
      --  SPI4 clock enable
      SPI4ENR        : APB2ENR_SPI4ENR_Field := 16#0#;
      --  System configuration controller clock enable
      SYSCFGEN       : APB2ENR_SYSCFGEN_Field := 16#0#;
      --  unspecified
      Reserved_15_15 : STM32_SVD.Bit := 16#0#;
      --  TIM9 clock enable
      TIM9EN         : APB2ENR_TIM9EN_Field := 16#0#;
      --  TIM10 clock enable
      TIM10EN        : APB2ENR_TIM10EN_Field := 16#0#;
      --  TIM11 clock enable
      TIM11EN        : APB2ENR_TIM11EN_Field := 16#0#;
      --  unspecified
      Reserved_19_19 : STM32_SVD.Bit := 16#0#;
      --  SPI5 clock enable
      SPI5ENR        : APB2ENR_SPI5ENR_Field := 16#0#;
      --  SPI6 clock enable
      SPI6ENR        : APB2ENR_SPI6ENR_Field := 16#0#;
      --  SAI1 clock enable
      SAI1EN         : APB2ENR_SAI1EN_Field := 16#0#;
      --  unspecified
      Reserved_23_25 : STM32_SVD.UInt3 := 16#0#;
      --  LTDC clock enable
      LTDCEN         : APB2ENR_LTDCEN_Field := 16#0#;
      --  unspecified
      Reserved_27_31 : STM32_SVD.UInt5 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB2ENR_Register use record
      TIM1EN         at 0 range 0 .. 0;
      TIM8EN         at 0 range 1 .. 1;
      Reserved_2_3   at 0 range 2 .. 3;
      USART1EN       at 0 range 4 .. 4;
      USART6EN       at 0 range 5 .. 5;
      Reserved_6_7   at 0 range 6 .. 7;
      ADC1EN         at 0 range 8 .. 8;
      ADC2EN         at 0 range 9 .. 9;
      ADC3EN         at 0 range 10 .. 10;
      SDIOEN         at 0 range 11 .. 11;
      SPI1EN         at 0 range 12 .. 12;
      SPI4ENR        at 0 range 13 .. 13;
      SYSCFGEN       at 0 range 14 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      TIM9EN         at 0 range 16 .. 16;
      TIM10EN        at 0 range 17 .. 17;
      TIM11EN        at 0 range 18 .. 18;
      Reserved_19_19 at 0 range 19 .. 19;
      SPI5ENR        at 0 range 20 .. 20;
      SPI6ENR        at 0 range 21 .. 21;
      SAI1EN         at 0 range 22 .. 22;
      Reserved_23_25 at 0 range 23 .. 25;
      LTDCEN         at 0 range 26 .. 26;
      Reserved_27_31 at 0 range 27 .. 31;
   end record;

   subtype AHB1LPENR_GPIOALPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOBLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOCLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIODLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOELPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOFLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOGLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOHLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOILPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOJLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_GPIOKLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_CRCLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_FLITFLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_SRAM1LPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_SRAM2LPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_BKPSRAMLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_SRAM3LPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_DMA1LPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_DMA2LPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_DMA2DLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_ETHMACLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_ETHMACTXLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_ETHMACRXLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_ETHMACPTPLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_OTGHSLPEN_Field is STM32_SVD.Bit;
   subtype AHB1LPENR_OTGHSULPILPEN_Field is STM32_SVD.Bit;

   --  AHB1 peripheral clock enable in low power mode register
   type AHB1LPENR_Register is record
      --  IO port A clock enable during sleep mode
      GPIOALPEN      : AHB1LPENR_GPIOALPEN_Field := 16#1#;
      --  IO port B clock enable during Sleep mode
      GPIOBLPEN      : AHB1LPENR_GPIOBLPEN_Field := 16#1#;
      --  IO port C clock enable during Sleep mode
      GPIOCLPEN      : AHB1LPENR_GPIOCLPEN_Field := 16#1#;
      --  IO port D clock enable during Sleep mode
      GPIODLPEN      : AHB1LPENR_GPIODLPEN_Field := 16#1#;
      --  IO port E clock enable during Sleep mode
      GPIOELPEN      : AHB1LPENR_GPIOELPEN_Field := 16#1#;
      --  IO port F clock enable during Sleep mode
      GPIOFLPEN      : AHB1LPENR_GPIOFLPEN_Field := 16#1#;
      --  IO port G clock enable during Sleep mode
      GPIOGLPEN      : AHB1LPENR_GPIOGLPEN_Field := 16#1#;
      --  IO port H clock enable during Sleep mode
      GPIOHLPEN      : AHB1LPENR_GPIOHLPEN_Field := 16#1#;
      --  IO port I clock enable during Sleep mode
      GPIOILPEN      : AHB1LPENR_GPIOILPEN_Field := 16#1#;
      --  IO port J clock enable during Sleep mode
      GPIOJLPEN      : AHB1LPENR_GPIOJLPEN_Field := 16#0#;
      --  IO port K clock enable during Sleep mode
      GPIOKLPEN      : AHB1LPENR_GPIOKLPEN_Field := 16#0#;
      --  unspecified
      Reserved_11_11 : STM32_SVD.Bit := 16#0#;
      --  CRC clock enable during Sleep mode
      CRCLPEN        : AHB1LPENR_CRCLPEN_Field := 16#1#;
      --  unspecified
      Reserved_13_14 : STM32_SVD.UInt2 := 16#0#;
      --  Flash interface clock enable during Sleep mode
      FLITFLPEN      : AHB1LPENR_FLITFLPEN_Field := 16#1#;
      --  SRAM 1interface clock enable during Sleep mode
      SRAM1LPEN      : AHB1LPENR_SRAM1LPEN_Field := 16#1#;
      --  SRAM 2 interface clock enable during Sleep mode
      SRAM2LPEN      : AHB1LPENR_SRAM2LPEN_Field := 16#1#;
      --  Backup SRAM interface clock enable during Sleep mode
      BKPSRAMLPEN    : AHB1LPENR_BKPSRAMLPEN_Field := 16#1#;
      --  SRAM 3 interface clock enable during Sleep mode
      SRAM3LPEN      : AHB1LPENR_SRAM3LPEN_Field := 16#0#;
      --  unspecified
      Reserved_20_20 : STM32_SVD.Bit := 16#0#;
      --  DMA1 clock enable during Sleep mode
      DMA1LPEN       : AHB1LPENR_DMA1LPEN_Field := 16#1#;
      --  DMA2 clock enable during Sleep mode
      DMA2LPEN       : AHB1LPENR_DMA2LPEN_Field := 16#1#;
      --  DMA2D clock enable during Sleep mode
      DMA2DLPEN      : AHB1LPENR_DMA2DLPEN_Field := 16#0#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  Ethernet MAC clock enable during Sleep mode
      ETHMACLPEN     : AHB1LPENR_ETHMACLPEN_Field := 16#1#;
      --  Ethernet transmission clock enable during Sleep mode
      ETHMACTXLPEN   : AHB1LPENR_ETHMACTXLPEN_Field := 16#1#;
      --  Ethernet reception clock enable during Sleep mode
      ETHMACRXLPEN   : AHB1LPENR_ETHMACRXLPEN_Field := 16#1#;
      --  Ethernet PTP clock enable during Sleep mode
      ETHMACPTPLPEN  : AHB1LPENR_ETHMACPTPLPEN_Field := 16#1#;
      --  USB OTG HS clock enable during Sleep mode
      OTGHSLPEN      : AHB1LPENR_OTGHSLPEN_Field := 16#1#;
      --  USB OTG HS ULPI clock enable during Sleep mode
      OTGHSULPILPEN  : AHB1LPENR_OTGHSULPILPEN_Field := 16#1#;
      --  unspecified
      Reserved_31_31 : STM32_SVD.Bit := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB1LPENR_Register use record
      GPIOALPEN      at 0 range 0 .. 0;
      GPIOBLPEN      at 0 range 1 .. 1;
      GPIOCLPEN      at 0 range 2 .. 2;
      GPIODLPEN      at 0 range 3 .. 3;
      GPIOELPEN      at 0 range 4 .. 4;
      GPIOFLPEN      at 0 range 5 .. 5;
      GPIOGLPEN      at 0 range 6 .. 6;
      GPIOHLPEN      at 0 range 7 .. 7;
      GPIOILPEN      at 0 range 8 .. 8;
      GPIOJLPEN      at 0 range 9 .. 9;
      GPIOKLPEN      at 0 range 10 .. 10;
      Reserved_11_11 at 0 range 11 .. 11;
      CRCLPEN        at 0 range 12 .. 12;
      Reserved_13_14 at 0 range 13 .. 14;
      FLITFLPEN      at 0 range 15 .. 15;
      SRAM1LPEN      at 0 range 16 .. 16;
      SRAM2LPEN      at 0 range 17 .. 17;
      BKPSRAMLPEN    at 0 range 18 .. 18;
      SRAM3LPEN      at 0 range 19 .. 19;
      Reserved_20_20 at 0 range 20 .. 20;
      DMA1LPEN       at 0 range 21 .. 21;
      DMA2LPEN       at 0 range 22 .. 22;
      DMA2DLPEN      at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      ETHMACLPEN     at 0 range 25 .. 25;
      ETHMACTXLPEN   at 0 range 26 .. 26;
      ETHMACRXLPEN   at 0 range 27 .. 27;
      ETHMACPTPLPEN  at 0 range 28 .. 28;
      OTGHSLPEN      at 0 range 29 .. 29;
      OTGHSULPILPEN  at 0 range 30 .. 30;
      Reserved_31_31 at 0 range 31 .. 31;
   end record;

   subtype AHB2LPENR_DCMILPEN_Field is STM32_SVD.Bit;
   subtype AHB2LPENR_RNGLPEN_Field is STM32_SVD.Bit;
   subtype AHB2LPENR_OTGFSLPEN_Field is STM32_SVD.Bit;

   --  AHB2 peripheral clock enable in low power mode register
   type AHB2LPENR_Register is record
      --  Camera interface enable during Sleep mode
      DCMILPEN      : AHB2LPENR_DCMILPEN_Field := 16#1#;
      --  unspecified
      Reserved_1_5  : STM32_SVD.UInt5 := 16#18#;
      --  Random number generator clock enable during Sleep mode
      RNGLPEN       : AHB2LPENR_RNGLPEN_Field := 16#1#;
      --  USB OTG FS clock enable during Sleep mode
      OTGFSLPEN     : AHB2LPENR_OTGFSLPEN_Field := 16#1#;
      --  unspecified
      Reserved_8_31 : STM32_SVD.UInt24 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB2LPENR_Register use record
      DCMILPEN      at 0 range 0 .. 0;
      Reserved_1_5  at 0 range 1 .. 5;
      RNGLPEN       at 0 range 6 .. 6;
      OTGFSLPEN     at 0 range 7 .. 7;
      Reserved_8_31 at 0 range 8 .. 31;
   end record;

   subtype AHB3LPENR_FMCLPEN_Field is STM32_SVD.Bit;

   --  AHB3 peripheral clock enable in low power mode register
   type AHB3LPENR_Register is record
      --  Flexible memory controller module clock enable during Sleep mode
      FMCLPEN       : AHB3LPENR_FMCLPEN_Field := 16#1#;
      --  unspecified
      Reserved_1_31 : STM32_SVD.UInt31 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHB3LPENR_Register use record
      FMCLPEN       at 0 range 0 .. 0;
      Reserved_1_31 at 0 range 1 .. 31;
   end record;

   subtype APB1LPENR_TIM2LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM3LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM4LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM5LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM6LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM7LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM12LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM13LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_TIM14LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_WWDGLPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_SPI2LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_SPI3LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_USART2LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_USART3LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_UART4LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_UART5LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_I2C1LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_I2C2LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_I2C3LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_CAN1LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_CAN2LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_PWRLPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_DACLPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_UART7LPEN_Field is STM32_SVD.Bit;
   subtype APB1LPENR_UART8LPEN_Field is STM32_SVD.Bit;

   --  APB1 peripheral clock enable in low power mode register
   type APB1LPENR_Register is record
      --  TIM2 clock enable during Sleep mode
      TIM2LPEN       : APB1LPENR_TIM2LPEN_Field := 16#1#;
      --  TIM3 clock enable during Sleep mode
      TIM3LPEN       : APB1LPENR_TIM3LPEN_Field := 16#1#;
      --  TIM4 clock enable during Sleep mode
      TIM4LPEN       : APB1LPENR_TIM4LPEN_Field := 16#1#;
      --  TIM5 clock enable during Sleep mode
      TIM5LPEN       : APB1LPENR_TIM5LPEN_Field := 16#1#;
      --  TIM6 clock enable during Sleep mode
      TIM6LPEN       : APB1LPENR_TIM6LPEN_Field := 16#1#;
      --  TIM7 clock enable during Sleep mode
      TIM7LPEN       : APB1LPENR_TIM7LPEN_Field := 16#1#;
      --  TIM12 clock enable during Sleep mode
      TIM12LPEN      : APB1LPENR_TIM12LPEN_Field := 16#1#;
      --  TIM13 clock enable during Sleep mode
      TIM13LPEN      : APB1LPENR_TIM13LPEN_Field := 16#1#;
      --  TIM14 clock enable during Sleep mode
      TIM14LPEN      : APB1LPENR_TIM14LPEN_Field := 16#1#;
      --  unspecified
      Reserved_9_10  : STM32_SVD.UInt2 := 16#0#;
      --  Window watchdog clock enable during Sleep mode
      WWDGLPEN       : APB1LPENR_WWDGLPEN_Field := 16#1#;
      --  unspecified
      Reserved_12_13 : STM32_SVD.UInt2 := 16#0#;
      --  SPI2 clock enable during Sleep mode
      SPI2LPEN       : APB1LPENR_SPI2LPEN_Field := 16#1#;
      --  SPI3 clock enable during Sleep mode
      SPI3LPEN       : APB1LPENR_SPI3LPEN_Field := 16#1#;
      --  unspecified
      Reserved_16_16 : STM32_SVD.Bit := 16#0#;
      --  USART2 clock enable during Sleep mode
      USART2LPEN     : APB1LPENR_USART2LPEN_Field := 16#1#;
      --  USART3 clock enable during Sleep mode
      USART3LPEN     : APB1LPENR_USART3LPEN_Field := 16#1#;
      --  UART4 clock enable during Sleep mode
      UART4LPEN      : APB1LPENR_UART4LPEN_Field := 16#1#;
      --  UART5 clock enable during Sleep mode
      UART5LPEN      : APB1LPENR_UART5LPEN_Field := 16#1#;
      --  I2C1 clock enable during Sleep mode
      I2C1LPEN       : APB1LPENR_I2C1LPEN_Field := 16#1#;
      --  I2C2 clock enable during Sleep mode
      I2C2LPEN       : APB1LPENR_I2C2LPEN_Field := 16#1#;
      --  I2C3 clock enable during Sleep mode
      I2C3LPEN       : APB1LPENR_I2C3LPEN_Field := 16#1#;
      --  unspecified
      Reserved_24_24 : STM32_SVD.Bit := 16#0#;
      --  CAN 1 clock enable during Sleep mode
      CAN1LPEN       : APB1LPENR_CAN1LPEN_Field := 16#1#;
      --  CAN 2 clock enable during Sleep mode
      CAN2LPEN       : APB1LPENR_CAN2LPEN_Field := 16#1#;
      --  unspecified
      Reserved_27_27 : STM32_SVD.Bit := 16#0#;
      --  Power interface clock enable during Sleep mode
      PWRLPEN        : APB1LPENR_PWRLPEN_Field := 16#1#;
      --  DAC interface clock enable during Sleep mode
      DACLPEN        : APB1LPENR_DACLPEN_Field := 16#1#;
      --  UART7 clock enable during Sleep mode
      UART7LPEN      : APB1LPENR_UART7LPEN_Field := 16#0#;
      --  UART8 clock enable during Sleep mode
      UART8LPEN      : APB1LPENR_UART8LPEN_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB1LPENR_Register use record
      TIM2LPEN       at 0 range 0 .. 0;
      TIM3LPEN       at 0 range 1 .. 1;
      TIM4LPEN       at 0 range 2 .. 2;
      TIM5LPEN       at 0 range 3 .. 3;
      TIM6LPEN       at 0 range 4 .. 4;
      TIM7LPEN       at 0 range 5 .. 5;
      TIM12LPEN      at 0 range 6 .. 6;
      TIM13LPEN      at 0 range 7 .. 7;
      TIM14LPEN      at 0 range 8 .. 8;
      Reserved_9_10  at 0 range 9 .. 10;
      WWDGLPEN       at 0 range 11 .. 11;
      Reserved_12_13 at 0 range 12 .. 13;
      SPI2LPEN       at 0 range 14 .. 14;
      SPI3LPEN       at 0 range 15 .. 15;
      Reserved_16_16 at 0 range 16 .. 16;
      USART2LPEN     at 0 range 17 .. 17;
      USART3LPEN     at 0 range 18 .. 18;
      UART4LPEN      at 0 range 19 .. 19;
      UART5LPEN      at 0 range 20 .. 20;
      I2C1LPEN       at 0 range 21 .. 21;
      I2C2LPEN       at 0 range 22 .. 22;
      I2C3LPEN       at 0 range 23 .. 23;
      Reserved_24_24 at 0 range 24 .. 24;
      CAN1LPEN       at 0 range 25 .. 25;
      CAN2LPEN       at 0 range 26 .. 26;
      Reserved_27_27 at 0 range 27 .. 27;
      PWRLPEN        at 0 range 28 .. 28;
      DACLPEN        at 0 range 29 .. 29;
      UART7LPEN      at 0 range 30 .. 30;
      UART8LPEN      at 0 range 31 .. 31;
   end record;

   subtype APB2LPENR_TIM1LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_TIM8LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_USART1LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_USART6LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_ADC1LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_ADC2LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_ADC3LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SDIOLPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SPI1LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SPI4LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SYSCFGLPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_TIM9LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_TIM10LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_TIM11LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SPI5LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SPI6LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_SAI1LPEN_Field is STM32_SVD.Bit;
   subtype APB2LPENR_LTDCLPEN_Field is STM32_SVD.Bit;

   --  APB2 peripheral clock enabled in low power mode register
   type APB2LPENR_Register is record
      --  TIM1 clock enable during Sleep mode
      TIM1LPEN       : APB2LPENR_TIM1LPEN_Field := 16#1#;
      --  TIM8 clock enable during Sleep mode
      TIM8LPEN       : APB2LPENR_TIM8LPEN_Field := 16#1#;
      --  unspecified
      Reserved_2_3   : STM32_SVD.UInt2 := 16#0#;
      --  USART1 clock enable during Sleep mode
      USART1LPEN     : APB2LPENR_USART1LPEN_Field := 16#1#;
      --  USART6 clock enable during Sleep mode
      USART6LPEN     : APB2LPENR_USART6LPEN_Field := 16#1#;
      --  unspecified
      Reserved_6_7   : STM32_SVD.UInt2 := 16#0#;
      --  ADC1 clock enable during Sleep mode
      ADC1LPEN       : APB2LPENR_ADC1LPEN_Field := 16#1#;
      --  ADC2 clock enable during Sleep mode
      ADC2LPEN       : APB2LPENR_ADC2LPEN_Field := 16#1#;
      --  ADC 3 clock enable during Sleep mode
      ADC3LPEN       : APB2LPENR_ADC3LPEN_Field := 16#1#;
      --  SDIO clock enable during Sleep mode
      SDIOLPEN       : APB2LPENR_SDIOLPEN_Field := 16#1#;
      --  SPI 1 clock enable during Sleep mode
      SPI1LPEN       : APB2LPENR_SPI1LPEN_Field := 16#1#;
      --  SPI 4 clock enable during Sleep mode
      SPI4LPEN       : APB2LPENR_SPI4LPEN_Field := 16#0#;
      --  System configuration controller clock enable during Sleep mode
      SYSCFGLPEN     : APB2LPENR_SYSCFGLPEN_Field := 16#1#;
      --  unspecified
      Reserved_15_15 : STM32_SVD.Bit := 16#0#;
      --  TIM9 clock enable during sleep mode
      TIM9LPEN       : APB2LPENR_TIM9LPEN_Field := 16#1#;
      --  TIM10 clock enable during Sleep mode
      TIM10LPEN      : APB2LPENR_TIM10LPEN_Field := 16#1#;
      --  TIM11 clock enable during Sleep mode
      TIM11LPEN      : APB2LPENR_TIM11LPEN_Field := 16#1#;
      --  unspecified
      Reserved_19_19 : STM32_SVD.Bit := 16#0#;
      --  SPI 5 clock enable during Sleep mode
      SPI5LPEN       : APB2LPENR_SPI5LPEN_Field := 16#0#;
      --  SPI 6 clock enable during Sleep mode
      SPI6LPEN       : APB2LPENR_SPI6LPEN_Field := 16#0#;
      --  SAI1 clock enable
      SAI1LPEN       : APB2LPENR_SAI1LPEN_Field := 16#0#;
      --  unspecified
      Reserved_23_25 : STM32_SVD.UInt3 := 16#0#;
      --  LTDC clock enable
      LTDCLPEN       : APB2LPENR_LTDCLPEN_Field := 16#0#;
      --  unspecified
      Reserved_27_31 : STM32_SVD.UInt5 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB2LPENR_Register use record
      TIM1LPEN       at 0 range 0 .. 0;
      TIM8LPEN       at 0 range 1 .. 1;
      Reserved_2_3   at 0 range 2 .. 3;
      USART1LPEN     at 0 range 4 .. 4;
      USART6LPEN     at 0 range 5 .. 5;
      Reserved_6_7   at 0 range 6 .. 7;
      ADC1LPEN       at 0 range 8 .. 8;
      ADC2LPEN       at 0 range 9 .. 9;
      ADC3LPEN       at 0 range 10 .. 10;
      SDIOLPEN       at 0 range 11 .. 11;
      SPI1LPEN       at 0 range 12 .. 12;
      SPI4LPEN       at 0 range 13 .. 13;
      SYSCFGLPEN     at 0 range 14 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      TIM9LPEN       at 0 range 16 .. 16;
      TIM10LPEN      at 0 range 17 .. 17;
      TIM11LPEN      at 0 range 18 .. 18;
      Reserved_19_19 at 0 range 19 .. 19;
      SPI5LPEN       at 0 range 20 .. 20;
      SPI6LPEN       at 0 range 21 .. 21;
      SAI1LPEN       at 0 range 22 .. 22;
      Reserved_23_25 at 0 range 23 .. 25;
      LTDCLPEN       at 0 range 26 .. 26;
      Reserved_27_31 at 0 range 27 .. 31;
   end record;

   subtype BDCR_LSEON_Field is STM32_SVD.Bit;
   subtype BDCR_LSERDY_Field is STM32_SVD.Bit;
   subtype BDCR_LSEBYP_Field is STM32_SVD.Bit;
   --  BDCR_RTCSEL array element
   subtype BDCR_RTCSEL_Element is STM32_SVD.Bit;

   --  BDCR_RTCSEL array
   type BDCR_RTCSEL_Field_Array is array (0 .. 1) of BDCR_RTCSEL_Element
     with Component_Size => 1, Size => 2;

   --  Type definition for BDCR_RTCSEL
   type BDCR_RTCSEL_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  RTCSEL as a value
            Val : STM32_SVD.UInt2;
         when True =>
            --  RTCSEL as an array
            Arr : BDCR_RTCSEL_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 2;

   for BDCR_RTCSEL_Field use record
      Val at 0 range 0 .. 1;
      Arr at 0 range 0 .. 1;
   end record;

   subtype BDCR_RTCEN_Field is STM32_SVD.Bit;
   subtype BDCR_BDRST_Field is STM32_SVD.Bit;

   --  Backup domain control register
   type BDCR_Register is record
      --  External low-speed oscillator enable
      LSEON          : BDCR_LSEON_Field := 16#0#;
      --  Read-only. External low-speed oscillator ready
      LSERDY         : BDCR_LSERDY_Field := 16#0#;
      --  External low-speed oscillator bypass
      LSEBYP         : BDCR_LSEBYP_Field := 16#0#;
      --  unspecified
      Reserved_3_7   : STM32_SVD.UInt5 := 16#0#;
      --  RTC clock source selection
      RTCSEL         : BDCR_RTCSEL_Field := (As_Array => False, Val => 16#0#);
      --  unspecified
      Reserved_10_14 : STM32_SVD.UInt5 := 16#0#;
      --  RTC clock enable
      RTCEN          : BDCR_RTCEN_Field := 16#0#;
      --  Backup domain software reset
      BDRST          : BDCR_BDRST_Field := 16#0#;
      --  unspecified
      Reserved_17_31 : STM32_SVD.UInt15 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for BDCR_Register use record
      LSEON          at 0 range 0 .. 0;
      LSERDY         at 0 range 1 .. 1;
      LSEBYP         at 0 range 2 .. 2;
      Reserved_3_7   at 0 range 3 .. 7;
      RTCSEL         at 0 range 8 .. 9;
      Reserved_10_14 at 0 range 10 .. 14;
      RTCEN          at 0 range 15 .. 15;
      BDRST          at 0 range 16 .. 16;
      Reserved_17_31 at 0 range 17 .. 31;
   end record;

   subtype CSR_LSION_Field is STM32_SVD.Bit;
   subtype CSR_LSIRDY_Field is STM32_SVD.Bit;
   subtype CSR_RMVF_Field is STM32_SVD.Bit;
   subtype CSR_BORRSTF_Field is STM32_SVD.Bit;
   subtype CSR_PADRSTF_Field is STM32_SVD.Bit;
   subtype CSR_PORRSTF_Field is STM32_SVD.Bit;
   subtype CSR_SFTRSTF_Field is STM32_SVD.Bit;
   subtype CSR_WDGRSTF_Field is STM32_SVD.Bit;
   subtype CSR_WWDGRSTF_Field is STM32_SVD.Bit;
   subtype CSR_LPWRRSTF_Field is STM32_SVD.Bit;

   --  clock control & status register
   type CSR_Register is record
      --  Internal low-speed oscillator enable
      LSION         : CSR_LSION_Field := 16#0#;
      --  Read-only. Internal low-speed oscillator ready
      LSIRDY        : CSR_LSIRDY_Field := 16#0#;
      --  unspecified
      Reserved_2_23 : STM32_SVD.UInt22 := 16#0#;
      --  Remove reset flag
      RMVF          : CSR_RMVF_Field := 16#0#;
      --  BOR reset flag
      BORRSTF       : CSR_BORRSTF_Field := 16#1#;
      --  PIN reset flag
      PADRSTF       : CSR_PADRSTF_Field := 16#1#;
      --  POR/PDR reset flag
      PORRSTF       : CSR_PORRSTF_Field := 16#1#;
      --  Software reset flag
      SFTRSTF       : CSR_SFTRSTF_Field := 16#0#;
      --  Independent watchdog reset flag
      WDGRSTF       : CSR_WDGRSTF_Field := 16#0#;
      --  Window watchdog reset flag
      WWDGRSTF      : CSR_WWDGRSTF_Field := 16#0#;
      --  Low-power reset flag
      LPWRRSTF      : CSR_LPWRRSTF_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CSR_Register use record
      LSION         at 0 range 0 .. 0;
      LSIRDY        at 0 range 1 .. 1;
      Reserved_2_23 at 0 range 2 .. 23;
      RMVF          at 0 range 24 .. 24;
      BORRSTF       at 0 range 25 .. 25;
      PADRSTF       at 0 range 26 .. 26;
      PORRSTF       at 0 range 27 .. 27;
      SFTRSTF       at 0 range 28 .. 28;
      WDGRSTF       at 0 range 29 .. 29;
      WWDGRSTF      at 0 range 30 .. 30;
      LPWRRSTF      at 0 range 31 .. 31;
   end record;

   subtype SSCGR_MODPER_Field is STM32_SVD.UInt13;
   subtype SSCGR_INCSTEP_Field is STM32_SVD.UInt15;
   subtype SSCGR_SPREADSEL_Field is STM32_SVD.Bit;
   subtype SSCGR_SSCGEN_Field is STM32_SVD.Bit;

   --  spread spectrum clock generation register
   type SSCGR_Register is record
      --  Modulation period
      MODPER         : SSCGR_MODPER_Field := 16#0#;
      --  Incrementation step
      INCSTEP        : SSCGR_INCSTEP_Field := 16#0#;
      --  unspecified
      Reserved_28_29 : STM32_SVD.UInt2 := 16#0#;
      --  Spread Select
      SPREADSEL      : SSCGR_SPREADSEL_Field := 16#0#;
      --  Spread spectrum modulation enable
      SSCGEN         : SSCGR_SSCGEN_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for SSCGR_Register use record
      MODPER         at 0 range 0 .. 12;
      INCSTEP        at 0 range 13 .. 27;
      Reserved_28_29 at 0 range 28 .. 29;
      SPREADSEL      at 0 range 30 .. 30;
      SSCGEN         at 0 range 31 .. 31;
   end record;

   subtype PLLI2SCFGR_PLLI2SN_Field is STM32_SVD.UInt9;
   subtype PLLI2SCFGR_PLLI2SQ_Field is STM32_SVD.UInt4;
   subtype PLLI2SCFGR_PLLI2SR_Field is STM32_SVD.UInt3;

   --  PLLI2S configuration register
   type PLLI2SCFGR_Register is record
      --  unspecified
      Reserved_0_5   : STM32_SVD.UInt6 := 16#0#;
      --  PLLI2S multiplication factor for VCO
      PLLI2SN        : PLLI2SCFGR_PLLI2SN_Field := 16#C0#;
      --  unspecified
      Reserved_15_23 : STM32_SVD.UInt9 := 16#0#;
      --  PLLI2S division factor for SAI1 clock
      PLLI2SQ        : PLLI2SCFGR_PLLI2SQ_Field := 16#0#;
      --  PLLI2S division factor for I2S clocks
      PLLI2SR        : PLLI2SCFGR_PLLI2SR_Field := 16#2#;
      --  unspecified
      Reserved_31_31 : STM32_SVD.Bit := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for PLLI2SCFGR_Register use record
      Reserved_0_5   at 0 range 0 .. 5;
      PLLI2SN        at 0 range 6 .. 14;
      Reserved_15_23 at 0 range 15 .. 23;
      PLLI2SQ        at 0 range 24 .. 27;
      PLLI2SR        at 0 range 28 .. 30;
      Reserved_31_31 at 0 range 31 .. 31;
   end record;

   subtype PLLSAICFGR_PLLSAIN_Field is STM32_SVD.UInt9;
   subtype PLLSAICFGR_PLLSAIQ_Field is STM32_SVD.UInt4;
   subtype PLLSAICFGR_PLLSAIR_Field is STM32_SVD.UInt3;

   --  PLLSAICFGR
   type PLLSAICFGR_Register is record
      --  unspecified
      Reserved_0_5   : STM32_SVD.UInt6 := 16#0#;
      --  PLLSAIN
      PLLSAIN        : PLLSAICFGR_PLLSAIN_Field := 16#C0#;
      --  unspecified
      Reserved_15_23 : STM32_SVD.UInt9 := 16#0#;
      --  PLLSAIN
      PLLSAIQ        : PLLSAICFGR_PLLSAIQ_Field := 16#4#;
      --  PLLSAIN
      PLLSAIR        : PLLSAICFGR_PLLSAIR_Field := 16#2#;
      --  unspecified
      Reserved_31_31 : STM32_SVD.Bit := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for PLLSAICFGR_Register use record
      Reserved_0_5   at 0 range 0 .. 5;
      PLLSAIN        at 0 range 6 .. 14;
      Reserved_15_23 at 0 range 15 .. 23;
      PLLSAIQ        at 0 range 24 .. 27;
      PLLSAIR        at 0 range 28 .. 30;
      Reserved_31_31 at 0 range 31 .. 31;
   end record;

   subtype DCKCFGR_PLLI2SDIVQ_Field is STM32_SVD.UInt5;
   subtype DCKCFGR_PLLSAIDIVQ_Field is STM32_SVD.UInt5;
   subtype DCKCFGR_PLLSAIDIVR_Field is STM32_SVD.UInt2;
   subtype DCKCFGR_SAI1ASRC_Field is STM32_SVD.UInt2;
   subtype DCKCFGR_SAI1BSRC_Field is STM32_SVD.UInt2;
   subtype DCKCFGR_TIMPRE_Field is STM32_SVD.Bit;

   --  DCKCFGR
   type DCKCFGR_Register is record
      --  PLLI2SDIVQ
      PLLI2SDIVQ     : DCKCFGR_PLLI2SDIVQ_Field := 16#0#;
      --  unspecified
      Reserved_5_7   : STM32_SVD.UInt3 := 16#0#;
      --  PLLSAIDIVQ
      PLLSAIDIVQ     : DCKCFGR_PLLSAIDIVQ_Field := 16#0#;
      --  unspecified
      Reserved_13_15 : STM32_SVD.UInt3 := 16#0#;
      --  PLLSAIDIVR
      PLLSAIDIVR     : DCKCFGR_PLLSAIDIVR_Field := 16#0#;
      --  unspecified
      Reserved_18_19 : STM32_SVD.UInt2 := 16#0#;
      --  SAI1ASRC
      SAI1ASRC       : DCKCFGR_SAI1ASRC_Field := 16#0#;
      --  SAI1BSRC
      SAI1BSRC       : DCKCFGR_SAI1BSRC_Field := 16#0#;
      --  TIMPRE
      TIMPRE         : DCKCFGR_TIMPRE_Field := 16#0#;
      --  unspecified
      Reserved_25_31 : STM32_SVD.UInt7 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for DCKCFGR_Register use record
      PLLI2SDIVQ     at 0 range 0 .. 4;
      Reserved_5_7   at 0 range 5 .. 7;
      PLLSAIDIVQ     at 0 range 8 .. 12;
      Reserved_13_15 at 0 range 13 .. 15;
      PLLSAIDIVR     at 0 range 16 .. 17;
      Reserved_18_19 at 0 range 18 .. 19;
      SAI1ASRC       at 0 range 20 .. 21;
      SAI1BSRC       at 0 range 22 .. 23;
      TIMPRE         at 0 range 24 .. 24;
      Reserved_25_31 at 0 range 25 .. 31;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  Reset and clock control
   type RCC_Peripheral is record
      --  clock control register
      CR         : CR_Register;
      --  PLL configuration register
      PLLCFGR    : PLLCFGR_Register;
      --  clock configuration register
      CFGR       : CFGR_Register;
      --  clock interrupt register
      CIR        : CIR_Register;
      --  AHB1 peripheral reset register
      AHB1RSTR   : AHB1RSTR_Register;
      --  AHB2 peripheral reset register
      AHB2RSTR   : AHB2RSTR_Register;
      --  AHB3 peripheral reset register
      AHB3RSTR   : AHB3RSTR_Register;
      --  APB1 peripheral reset register
      APB1RSTR   : APB1RSTR_Register;
      --  APB2 peripheral reset register
      APB2RSTR   : APB2RSTR_Register;
      --  AHB1 peripheral clock register
      AHB1ENR    : AHB1ENR_Register;
      --  AHB2 peripheral clock enable register
      AHB2ENR    : AHB2ENR_Register;
      --  AHB3 peripheral clock enable register
      AHB3ENR    : AHB3ENR_Register;
      --  APB1 peripheral clock enable register
      APB1ENR    : APB1ENR_Register;
      --  APB2 peripheral clock enable register
      APB2ENR    : APB2ENR_Register;
      --  AHB1 peripheral clock enable in low power mode register
      AHB1LPENR  : AHB1LPENR_Register;
      --  AHB2 peripheral clock enable in low power mode register
      AHB2LPENR  : AHB2LPENR_Register;
      --  AHB3 peripheral clock enable in low power mode register
      AHB3LPENR  : AHB3LPENR_Register;
      --  APB1 peripheral clock enable in low power mode register
      APB1LPENR  : APB1LPENR_Register;
      --  APB2 peripheral clock enabled in low power mode register
      APB2LPENR  : APB2LPENR_Register;
      --  Backup domain control register
      BDCR       : BDCR_Register;
      --  clock control & status register
      CSR        : CSR_Register;
      --  spread spectrum clock generation register
      SSCGR      : SSCGR_Register;
      --  PLLI2S configuration register
      PLLI2SCFGR : PLLI2SCFGR_Register;
      --  PLLSAICFGR
      PLLSAICFGR : PLLSAICFGR_Register;
      --  DCKCFGR
      DCKCFGR    : DCKCFGR_Register;
   end record
     with Volatile;

   for RCC_Peripheral use record
      CR         at 0 range 0 .. 31;
      PLLCFGR    at 4 range 0 .. 31;
      CFGR       at 8 range 0 .. 31;
      CIR        at 12 range 0 .. 31;
      AHB1RSTR   at 16 range 0 .. 31;
      AHB2RSTR   at 20 range 0 .. 31;
      AHB3RSTR   at 24 range 0 .. 31;
      APB1RSTR   at 32 range 0 .. 31;
      APB2RSTR   at 36 range 0 .. 31;
      AHB1ENR    at 48 range 0 .. 31;
      AHB2ENR    at 52 range 0 .. 31;
      AHB3ENR    at 56 range 0 .. 31;
      APB1ENR    at 64 range 0 .. 31;
      APB2ENR    at 68 range 0 .. 31;
      AHB1LPENR  at 80 range 0 .. 31;
      AHB2LPENR  at 84 range 0 .. 31;
      AHB3LPENR  at 88 range 0 .. 31;
      APB1LPENR  at 96 range 0 .. 31;
      APB2LPENR  at 100 range 0 .. 31;
      BDCR       at 112 range 0 .. 31;
      CSR        at 116 range 0 .. 31;
      SSCGR      at 128 range 0 .. 31;
      PLLI2SCFGR at 132 range 0 .. 31;
      PLLSAICFGR at 136 range 0 .. 31;
      DCKCFGR    at 140 range 0 .. 31;
   end record;

   --  Reset and clock control
   RCC_Periph : aliased RCC_Peripheral
     with Import, Address => RCC_Base;

end STM32_SVD.RCC;
