--  This spec has been automatically generated from STM32F105xx.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

package STM32.RCC is
   pragma Preelaborate;

   ---------------
   -- Registers --
   ---------------

   -----------------
   -- CR_Register --
   -----------------

   subtype CR_HSION_Field is STM32.Bit;
   subtype CR_HSIRDY_Field is STM32.Bit;
   subtype CR_HSITRIM_Field is STM32.UInt5;
   subtype CR_HSICAL_Field is STM32.Byte;
   subtype CR_HSEON_Field is STM32.Bit;
   subtype CR_HSERDY_Field is STM32.Bit;
   subtype CR_HSEBYP_Field is STM32.Bit;
   subtype CR_CSSON_Field is STM32.Bit;
   subtype CR_PLLON_Field is STM32.Bit;
   subtype CR_PLLRDY_Field is STM32.Bit;
   subtype CR_PLL2ON_Field is STM32.Bit;
   subtype CR_PLL2RDY_Field is STM32.Bit;
   subtype CR_PLL3ON_Field is STM32.Bit;
   subtype CR_PLL3RDY_Field is STM32.Bit;

   --  Clock control register
   type CR_Register is record
      --  Internal High Speed clock enable
      HSION          : CR_HSION_Field := 16#1#;
      --  Read-only. Internal High Speed clock ready flag
      HSIRDY         : CR_HSIRDY_Field := 16#1#;
      --  unspecified
      Reserved_2_2   : STM32.Bit := 16#0#;
      --  Internal High Speed clock trimming
      HSITRIM        : CR_HSITRIM_Field := 16#10#;
      --  Read-only. Internal High Speed clock Calibration
      HSICAL         : CR_HSICAL_Field := 16#0#;
      --  External High Speed clock enable
      HSEON          : CR_HSEON_Field := 16#0#;
      --  Read-only. External High Speed clock ready flag
      HSERDY         : CR_HSERDY_Field := 16#0#;
      --  External High Speed clock Bypass
      HSEBYP         : CR_HSEBYP_Field := 16#0#;
      --  Clock Security System enable
      CSSON          : CR_CSSON_Field := 16#0#;
      --  unspecified
      Reserved_20_23 : STM32.UInt4 := 16#0#;
      --  PLL enable
      PLLON          : CR_PLLON_Field := 16#0#;
      --  Read-only. PLL clock ready flag
      PLLRDY         : CR_PLLRDY_Field := 16#0#;
      --  PLL2 enable
      PLL2ON         : CR_PLL2ON_Field := 16#0#;
      --  Read-only. PLL2 clock ready flag
      PLL2RDY        : CR_PLL2RDY_Field := 16#0#;
      --  PLL3 enable
      PLL3ON         : CR_PLL3ON_Field := 16#0#;
      --  Read-only. PLL3 clock ready flag
      PLL3RDY        : CR_PLL3RDY_Field := 16#0#;
      --  unspecified
      Reserved_30_31 : STM32.UInt2 := 16#0#;
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
      PLL2ON         at 0 range 26 .. 26;
      PLL2RDY        at 0 range 27 .. 27;
      PLL3ON         at 0 range 28 .. 28;
      PLL3RDY        at 0 range 29 .. 29;
      Reserved_30_31 at 0 range 30 .. 31;
   end record;

   -------------------
   -- CFGR_Register --
   -------------------

   subtype CFGR_SW_Field is STM32.UInt2;
   subtype CFGR_SWS_Field is STM32.UInt2;
   subtype CFGR_HPRE_Field is STM32.UInt4;

   ---------------
   -- CFGR.PPRE --
   ---------------

   --  CFGR_PPRE array element
   subtype CFGR_PPRE_Element is STM32.UInt3;

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
            Val : STM32.UInt6;
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

   subtype CFGR_ADCPRE_Field is STM32.UInt2;
   subtype CFGR_PLLSRC_Field is STM32.Bit;
   subtype CFGR_PLLXTPRE_Field is STM32.Bit;
   subtype CFGR_PLLMUL_Field is STM32.UInt4;
   subtype CFGR_OTGFSPRE_Field is STM32.Bit;
   subtype CFGR_MCO_Field is STM32.UInt4;

   --  Clock configuration register (RCC_CFGR)
   type CFGR_Register is record
      --  System clock Switch
      SW             : CFGR_SW_Field := 16#0#;
      --  Read-only. System Clock Switch Status
      SWS            : CFGR_SWS_Field := 16#0#;
      --  AHB prescaler
      HPRE           : CFGR_HPRE_Field := 16#0#;
      --  APB Low speed prescaler (APB1)
      PPRE           : CFGR_PPRE_Field := (As_Array => False, Val => 16#0#);
      --  ADC prescaler
      ADCPRE         : CFGR_ADCPRE_Field := 16#0#;
      --  PLL entry clock source
      PLLSRC         : CFGR_PLLSRC_Field := 16#0#;
      --  HSE divider for PLL entry
      PLLXTPRE       : CFGR_PLLXTPRE_Field := 16#0#;
      --  PLL Multiplication Factor
      PLLMUL         : CFGR_PLLMUL_Field := 16#0#;
      --  USB OTG FS prescaler
      OTGFSPRE       : CFGR_OTGFSPRE_Field := 16#0#;
      --  unspecified
      Reserved_23_23 : STM32.Bit := 16#0#;
      --  Microcontroller clock output
      MCO            : CFGR_MCO_Field := 16#0#;
      --  unspecified
      Reserved_28_31 : STM32.UInt4 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CFGR_Register use record
      SW             at 0 range 0 .. 1;
      SWS            at 0 range 2 .. 3;
      HPRE           at 0 range 4 .. 7;
      PPRE           at 0 range 8 .. 13;
      ADCPRE         at 0 range 14 .. 15;
      PLLSRC         at 0 range 16 .. 16;
      PLLXTPRE       at 0 range 17 .. 17;
      PLLMUL         at 0 range 18 .. 21;
      OTGFSPRE       at 0 range 22 .. 22;
      Reserved_23_23 at 0 range 23 .. 23;
      MCO            at 0 range 24 .. 27;
      Reserved_28_31 at 0 range 28 .. 31;
   end record;

   ------------------
   -- CIR_Register --
   ------------------

   subtype CIR_LSIRDYF_Field is STM32.Bit;
   subtype CIR_LSERDYF_Field is STM32.Bit;
   subtype CIR_HSIRDYF_Field is STM32.Bit;
   subtype CIR_HSERDYF_Field is STM32.Bit;
   subtype CIR_PLLRDYF_Field is STM32.Bit;
   subtype CIR_PLL2RDYF_Field is STM32.Bit;
   subtype CIR_PLL3RDYF_Field is STM32.Bit;
   subtype CIR_CSSF_Field is STM32.Bit;
   subtype CIR_LSIRDYIE_Field is STM32.Bit;
   subtype CIR_LSERDYIE_Field is STM32.Bit;
   subtype CIR_HSIRDYIE_Field is STM32.Bit;
   subtype CIR_HSERDYIE_Field is STM32.Bit;
   subtype CIR_PLLRDYIE_Field is STM32.Bit;
   subtype CIR_PLL2RDYIE_Field is STM32.Bit;
   subtype CIR_PLL3RDYIE_Field is STM32.Bit;
   subtype CIR_LSIRDYC_Field is STM32.Bit;
   subtype CIR_LSERDYC_Field is STM32.Bit;
   subtype CIR_HSIRDYC_Field is STM32.Bit;
   subtype CIR_HSERDYC_Field is STM32.Bit;
   subtype CIR_PLLRDYC_Field is STM32.Bit;
   subtype CIR_PLL2RDYC_Field is STM32.Bit;
   subtype CIR_PLL3RDYC_Field is STM32.Bit;
   subtype CIR_CSSC_Field is STM32.Bit;

   --  Clock interrupt register (RCC_CIR)
   type CIR_Register is record
      --  Read-only. LSI Ready Interrupt flag
      LSIRDYF        : CIR_LSIRDYF_Field := 16#0#;
      --  Read-only. LSE Ready Interrupt flag
      LSERDYF        : CIR_LSERDYF_Field := 16#0#;
      --  Read-only. HSI Ready Interrupt flag
      HSIRDYF        : CIR_HSIRDYF_Field := 16#0#;
      --  Read-only. HSE Ready Interrupt flag
      HSERDYF        : CIR_HSERDYF_Field := 16#0#;
      --  Read-only. PLL Ready Interrupt flag
      PLLRDYF        : CIR_PLLRDYF_Field := 16#0#;
      --  Read-only. PLL2 Ready Interrupt flag
      PLL2RDYF       : CIR_PLL2RDYF_Field := 16#0#;
      --  Read-only. PLL3 Ready Interrupt flag
      PLL3RDYF       : CIR_PLL3RDYF_Field := 16#0#;
      --  Read-only. Clock Security System Interrupt flag
      CSSF           : CIR_CSSF_Field := 16#0#;
      --  LSI Ready Interrupt Enable
      LSIRDYIE       : CIR_LSIRDYIE_Field := 16#0#;
      --  LSE Ready Interrupt Enable
      LSERDYIE       : CIR_LSERDYIE_Field := 16#0#;
      --  HSI Ready Interrupt Enable
      HSIRDYIE       : CIR_HSIRDYIE_Field := 16#0#;
      --  HSE Ready Interrupt Enable
      HSERDYIE       : CIR_HSERDYIE_Field := 16#0#;
      --  PLL Ready Interrupt Enable
      PLLRDYIE       : CIR_PLLRDYIE_Field := 16#0#;
      --  PLL2 Ready Interrupt Enable
      PLL2RDYIE      : CIR_PLL2RDYIE_Field := 16#0#;
      --  PLL3 Ready Interrupt Enable
      PLL3RDYIE      : CIR_PLL3RDYIE_Field := 16#0#;
      --  unspecified
      Reserved_15_15 : STM32.Bit := 16#0#;
      --  Write-only. LSI Ready Interrupt Clear
      LSIRDYC        : CIR_LSIRDYC_Field := 16#0#;
      --  Write-only. LSE Ready Interrupt Clear
      LSERDYC        : CIR_LSERDYC_Field := 16#0#;
      --  Write-only. HSI Ready Interrupt Clear
      HSIRDYC        : CIR_HSIRDYC_Field := 16#0#;
      --  Write-only. HSE Ready Interrupt Clear
      HSERDYC        : CIR_HSERDYC_Field := 16#0#;
      --  Write-only. PLL Ready Interrupt Clear
      PLLRDYC        : CIR_PLLRDYC_Field := 16#0#;
      --  Write-only. PLL2 Ready Interrupt Clear
      PLL2RDYC       : CIR_PLL2RDYC_Field := 16#0#;
      --  Write-only. PLL3 Ready Interrupt Clear
      PLL3RDYC       : CIR_PLL3RDYC_Field := 16#0#;
      --  Write-only. Clock security system interrupt clear
      CSSC           : CIR_CSSC_Field := 16#0#;
      --  unspecified
      Reserved_24_31 : STM32.Byte := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CIR_Register use record
      LSIRDYF        at 0 range 0 .. 0;
      LSERDYF        at 0 range 1 .. 1;
      HSIRDYF        at 0 range 2 .. 2;
      HSERDYF        at 0 range 3 .. 3;
      PLLRDYF        at 0 range 4 .. 4;
      PLL2RDYF       at 0 range 5 .. 5;
      PLL3RDYF       at 0 range 6 .. 6;
      CSSF           at 0 range 7 .. 7;
      LSIRDYIE       at 0 range 8 .. 8;
      LSERDYIE       at 0 range 9 .. 9;
      HSIRDYIE       at 0 range 10 .. 10;
      HSERDYIE       at 0 range 11 .. 11;
      PLLRDYIE       at 0 range 12 .. 12;
      PLL2RDYIE      at 0 range 13 .. 13;
      PLL3RDYIE      at 0 range 14 .. 14;
      Reserved_15_15 at 0 range 15 .. 15;
      LSIRDYC        at 0 range 16 .. 16;
      LSERDYC        at 0 range 17 .. 17;
      HSIRDYC        at 0 range 18 .. 18;
      HSERDYC        at 0 range 19 .. 19;
      PLLRDYC        at 0 range 20 .. 20;
      PLL2RDYC       at 0 range 21 .. 21;
      PLL3RDYC       at 0 range 22 .. 22;
      CSSC           at 0 range 23 .. 23;
      Reserved_24_31 at 0 range 24 .. 31;
   end record;

   -----------------------
   -- APB2RSTR_Register --
   -----------------------

   subtype APB2RSTR_AFIORST_Field is STM32.Bit;
   subtype APB2RSTR_IOPARST_Field is STM32.Bit;
   subtype APB2RSTR_IOPBRST_Field is STM32.Bit;
   subtype APB2RSTR_IOPCRST_Field is STM32.Bit;
   subtype APB2RSTR_IOPDRST_Field is STM32.Bit;
   subtype APB2RSTR_IOPERST_Field is STM32.Bit;
   subtype APB2RSTR_ADC1RST_Field is STM32.Bit;
   subtype APB2RSTR_ADC2RST_Field is STM32.Bit;
   subtype APB2RSTR_TIM1RST_Field is STM32.Bit;
   subtype APB2RSTR_SPI1RST_Field is STM32.Bit;
   subtype APB2RSTR_USART1RST_Field is STM32.Bit;

   --  APB2 peripheral reset register (RCC_APB2RSTR)
   type APB2RSTR_Register is record
      --  Alternate function I/O reset
      AFIORST        : APB2RSTR_AFIORST_Field := 16#0#;
      --  unspecified
      Reserved_1_1   : STM32.Bit := 16#0#;
      --  IO port A reset
      IOPARST        : APB2RSTR_IOPARST_Field := 16#0#;
      --  IO port B reset
      IOPBRST        : APB2RSTR_IOPBRST_Field := 16#0#;
      --  IO port C reset
      IOPCRST        : APB2RSTR_IOPCRST_Field := 16#0#;
      --  IO port D reset
      IOPDRST        : APB2RSTR_IOPDRST_Field := 16#0#;
      --  IO port E reset
      IOPERST        : APB2RSTR_IOPERST_Field := 16#0#;
      --  unspecified
      Reserved_7_8   : STM32.UInt2 := 16#0#;
      --  ADC 1 interface reset
      ADC1RST        : APB2RSTR_ADC1RST_Field := 16#0#;
      --  ADC 2 interface reset
      ADC2RST        : APB2RSTR_ADC2RST_Field := 16#0#;
      --  TIM1 timer reset
      TIM1RST        : APB2RSTR_TIM1RST_Field := 16#0#;
      --  SPI 1 reset
      SPI1RST        : APB2RSTR_SPI1RST_Field := 16#0#;
      --  unspecified
      Reserved_13_13 : STM32.Bit := 16#0#;
      --  USART1 reset
      USART1RST      : APB2RSTR_USART1RST_Field := 16#0#;
      --  unspecified
      Reserved_15_31 : STM32.UInt17 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB2RSTR_Register use record
      AFIORST        at 0 range 0 .. 0;
      Reserved_1_1   at 0 range 1 .. 1;
      IOPARST        at 0 range 2 .. 2;
      IOPBRST        at 0 range 3 .. 3;
      IOPCRST        at 0 range 4 .. 4;
      IOPDRST        at 0 range 5 .. 5;
      IOPERST        at 0 range 6 .. 6;
      Reserved_7_8   at 0 range 7 .. 8;
      ADC1RST        at 0 range 9 .. 9;
      ADC2RST        at 0 range 10 .. 10;
      TIM1RST        at 0 range 11 .. 11;
      SPI1RST        at 0 range 12 .. 12;
      Reserved_13_13 at 0 range 13 .. 13;
      USART1RST      at 0 range 14 .. 14;
      Reserved_15_31 at 0 range 15 .. 31;
   end record;

   -----------------------
   -- APB1RSTR_Register --
   -----------------------

   subtype APB1RSTR_TIM2RST_Field is STM32.Bit;
   subtype APB1RSTR_TIM3RST_Field is STM32.Bit;
   subtype APB1RSTR_TIM4RST_Field is STM32.Bit;
   subtype APB1RSTR_TIM5RST_Field is STM32.Bit;
   subtype APB1RSTR_TIM6RST_Field is STM32.Bit;
   subtype APB1RSTR_TIM7RST_Field is STM32.Bit;
   subtype APB1RSTR_WWDGRST_Field is STM32.Bit;
   subtype APB1RSTR_SPI2RST_Field is STM32.Bit;
   subtype APB1RSTR_SPI3RST_Field is STM32.Bit;
   subtype APB1RSTR_USART2RST_Field is STM32.Bit;
   subtype APB1RSTR_USART3RST_Field is STM32.Bit;
   subtype APB1RSTR_USART4RST_Field is STM32.Bit;
   subtype APB1RSTR_USART5RST_Field is STM32.Bit;
   subtype APB1RSTR_I2C1RST_Field is STM32.Bit;
   subtype APB1RSTR_I2C2RST_Field is STM32.Bit;
   subtype APB1RSTR_CAN1RST_Field is STM32.Bit;
   subtype APB1RSTR_CAN2RST_Field is STM32.Bit;
   subtype APB1RSTR_BKPRST_Field is STM32.Bit;
   subtype APB1RSTR_PWRRST_Field is STM32.Bit;
   subtype APB1RSTR_DACRST_Field is STM32.Bit;

   --  APB1 peripheral reset register (RCC_APB1RSTR)
   type APB1RSTR_Register is record
      --  Timer 2 reset
      TIM2RST        : APB1RSTR_TIM2RST_Field := 16#0#;
      --  Timer 3 reset
      TIM3RST        : APB1RSTR_TIM3RST_Field := 16#0#;
      --  Timer 4 reset
      TIM4RST        : APB1RSTR_TIM4RST_Field := 16#0#;
      --  Timer 5 reset
      TIM5RST        : APB1RSTR_TIM5RST_Field := 16#0#;
      --  Timer 6 reset
      TIM6RST        : APB1RSTR_TIM6RST_Field := 16#0#;
      --  Timer 7 reset
      TIM7RST        : APB1RSTR_TIM7RST_Field := 16#0#;
      --  unspecified
      Reserved_6_10  : STM32.UInt5 := 16#0#;
      --  Window watchdog reset
      WWDGRST        : APB1RSTR_WWDGRST_Field := 16#0#;
      --  unspecified
      Reserved_12_13 : STM32.UInt2 := 16#0#;
      --  SPI2 reset
      SPI2RST        : APB1RSTR_SPI2RST_Field := 16#0#;
      --  SPI3 reset
      SPI3RST        : APB1RSTR_SPI3RST_Field := 16#0#;
      --  unspecified
      Reserved_16_16 : STM32.Bit := 16#0#;
      --  USART 2 reset
      USART2RST      : APB1RSTR_USART2RST_Field := 16#0#;
      --  USART 3 reset
      USART3RST      : APB1RSTR_USART3RST_Field := 16#0#;
      --  USART 4 reset
      USART4RST      : APB1RSTR_USART4RST_Field := 16#0#;
      --  USART 5 reset
      USART5RST      : APB1RSTR_USART5RST_Field := 16#0#;
      --  I2C1 reset
      I2C1RST        : APB1RSTR_I2C1RST_Field := 16#0#;
      --  I2C2 reset
      I2C2RST        : APB1RSTR_I2C2RST_Field := 16#0#;
      --  unspecified
      Reserved_23_24 : STM32.UInt2 := 16#0#;
      --  CAN1 reset
      CAN1RST        : APB1RSTR_CAN1RST_Field := 16#0#;
      --  CAN2 reset
      CAN2RST        : APB1RSTR_CAN2RST_Field := 16#0#;
      --  Backup interface reset
      BKPRST         : APB1RSTR_BKPRST_Field := 16#0#;
      --  Power interface reset
      PWRRST         : APB1RSTR_PWRRST_Field := 16#0#;
      --  DAC interface reset
      DACRST         : APB1RSTR_DACRST_Field := 16#0#;
      --  unspecified
      Reserved_30_31 : STM32.UInt2 := 16#0#;
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
      Reserved_6_10  at 0 range 6 .. 10;
      WWDGRST        at 0 range 11 .. 11;
      Reserved_12_13 at 0 range 12 .. 13;
      SPI2RST        at 0 range 14 .. 14;
      SPI3RST        at 0 range 15 .. 15;
      Reserved_16_16 at 0 range 16 .. 16;
      USART2RST      at 0 range 17 .. 17;
      USART3RST      at 0 range 18 .. 18;
      USART4RST      at 0 range 19 .. 19;
      USART5RST      at 0 range 20 .. 20;
      I2C1RST        at 0 range 21 .. 21;
      I2C2RST        at 0 range 22 .. 22;
      Reserved_23_24 at 0 range 23 .. 24;
      CAN1RST        at 0 range 25 .. 25;
      CAN2RST        at 0 range 26 .. 26;
      BKPRST         at 0 range 27 .. 27;
      PWRRST         at 0 range 28 .. 28;
      DACRST         at 0 range 29 .. 29;
      Reserved_30_31 at 0 range 30 .. 31;
   end record;

   ---------------------
   -- AHBENR_Register --
   ---------------------

   subtype AHBENR_DMA1EN_Field is STM32.Bit;
   subtype AHBENR_DMA2EN_Field is STM32.Bit;
   subtype AHBENR_SRAMEN_Field is STM32.Bit;
   subtype AHBENR_FLITFEN_Field is STM32.Bit;
   subtype AHBENR_CRCEN_Field is STM32.Bit;
   subtype AHBENR_OTGFSEN_Field is STM32.Bit;

   --  AHB Peripheral Clock enable register (RCC_AHBENR)
   type AHBENR_Register is record
      --  DMA1 clock enable
      DMA1EN         : AHBENR_DMA1EN_Field := 16#0#;
      --  DMA2 clock enable
      DMA2EN         : AHBENR_DMA2EN_Field := 16#0#;
      --  SRAM interface clock enable
      SRAMEN         : AHBENR_SRAMEN_Field := 16#1#;
      --  unspecified
      Reserved_3_3   : STM32.Bit := 16#0#;
      --  FLITF clock enable
      FLITFEN        : AHBENR_FLITFEN_Field := 16#1#;
      --  unspecified
      Reserved_5_5   : STM32.Bit := 16#0#;
      --  CRC clock enable
      CRCEN          : AHBENR_CRCEN_Field := 16#0#;
      --  unspecified
      Reserved_7_11  : STM32.UInt5 := 16#0#;
      --  USB OTG FS clock enable
      OTGFSEN        : AHBENR_OTGFSEN_Field := 16#0#;
      --  unspecified
      Reserved_13_31 : STM32.UInt19 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHBENR_Register use record
      DMA1EN         at 0 range 0 .. 0;
      DMA2EN         at 0 range 1 .. 1;
      SRAMEN         at 0 range 2 .. 2;
      Reserved_3_3   at 0 range 3 .. 3;
      FLITFEN        at 0 range 4 .. 4;
      Reserved_5_5   at 0 range 5 .. 5;
      CRCEN          at 0 range 6 .. 6;
      Reserved_7_11  at 0 range 7 .. 11;
      OTGFSEN        at 0 range 12 .. 12;
      Reserved_13_31 at 0 range 13 .. 31;
   end record;

   ----------------------
   -- APB2ENR_Register --
   ----------------------

   subtype APB2ENR_AFIOEN_Field is STM32.Bit;
   subtype APB2ENR_IOPAEN_Field is STM32.Bit;
   subtype APB2ENR_IOPBEN_Field is STM32.Bit;
   subtype APB2ENR_IOPCEN_Field is STM32.Bit;
   subtype APB2ENR_IOPDEN_Field is STM32.Bit;
   subtype APB2ENR_IOPEEN_Field is STM32.Bit;
   subtype APB2ENR_ADC1EN_Field is STM32.Bit;
   subtype APB2ENR_ADC2EN_Field is STM32.Bit;
   subtype APB2ENR_TIM1EN_Field is STM32.Bit;
   subtype APB2ENR_SPI1EN_Field is STM32.Bit;
   subtype APB2ENR_USART1EN_Field is STM32.Bit;

   --  APB2 peripheral clock enable register (RCC_APB2ENR)
   type APB2ENR_Register is record
      --  Alternate function I/O clock enable
      AFIOEN         : APB2ENR_AFIOEN_Field := 16#0#;
      --  unspecified
      Reserved_1_1   : STM32.Bit := 16#0#;
      --  I/O port A clock enable
      IOPAEN         : APB2ENR_IOPAEN_Field := 16#0#;
      --  I/O port B clock enable
      IOPBEN         : APB2ENR_IOPBEN_Field := 16#0#;
      --  I/O port C clock enable
      IOPCEN         : APB2ENR_IOPCEN_Field := 16#0#;
      --  I/O port D clock enable
      IOPDEN         : APB2ENR_IOPDEN_Field := 16#0#;
      --  I/O port E clock enable
      IOPEEN         : APB2ENR_IOPEEN_Field := 16#0#;
      --  unspecified
      Reserved_7_8   : STM32.UInt2 := 16#0#;
      --  ADC 1 interface clock enable
      ADC1EN         : APB2ENR_ADC1EN_Field := 16#0#;
      --  ADC 2 interface clock enable
      ADC2EN         : APB2ENR_ADC2EN_Field := 16#0#;
      --  TIM1 Timer clock enable
      TIM1EN         : APB2ENR_TIM1EN_Field := 16#0#;
      --  SPI 1 clock enable
      SPI1EN         : APB2ENR_SPI1EN_Field := 16#0#;
      --  unspecified
      Reserved_13_13 : STM32.Bit := 16#0#;
      --  USART1 clock enable
      USART1EN       : APB2ENR_USART1EN_Field := 16#0#;
      --  unspecified
      Reserved_15_31 : STM32.UInt17 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for APB2ENR_Register use record
      AFIOEN         at 0 range 0 .. 0;
      Reserved_1_1   at 0 range 1 .. 1;
      IOPAEN         at 0 range 2 .. 2;
      IOPBEN         at 0 range 3 .. 3;
      IOPCEN         at 0 range 4 .. 4;
      IOPDEN         at 0 range 5 .. 5;
      IOPEEN         at 0 range 6 .. 6;
      Reserved_7_8   at 0 range 7 .. 8;
      ADC1EN         at 0 range 9 .. 9;
      ADC2EN         at 0 range 10 .. 10;
      TIM1EN         at 0 range 11 .. 11;
      SPI1EN         at 0 range 12 .. 12;
      Reserved_13_13 at 0 range 13 .. 13;
      USART1EN       at 0 range 14 .. 14;
      Reserved_15_31 at 0 range 15 .. 31;
   end record;

   ----------------------
   -- APB1ENR_Register --
   ----------------------

   subtype APB1ENR_TIM2EN_Field is STM32.Bit;
   subtype APB1ENR_TIM3EN_Field is STM32.Bit;
   subtype APB1ENR_TIM4EN_Field is STM32.Bit;
   subtype APB1ENR_TIM5EN_Field is STM32.Bit;
   subtype APB1ENR_TIM6EN_Field is STM32.Bit;
   subtype APB1ENR_TIM7EN_Field is STM32.Bit;
   subtype APB1ENR_WWDGEN_Field is STM32.Bit;
   subtype APB1ENR_SPI2EN_Field is STM32.Bit;
   subtype APB1ENR_SPI3EN_Field is STM32.Bit;
   subtype APB1ENR_USART2EN_Field is STM32.Bit;
   subtype APB1ENR_USART3EN_Field is STM32.Bit;
   subtype APB1ENR_UART4EN_Field is STM32.Bit;
   subtype APB1ENR_UART5EN_Field is STM32.Bit;
   subtype APB1ENR_I2C1EN_Field is STM32.Bit;
   subtype APB1ENR_I2C2EN_Field is STM32.Bit;
   subtype APB1ENR_CAN1EN_Field is STM32.Bit;
   subtype APB1ENR_CAN2EN_Field is STM32.Bit;
   subtype APB1ENR_BKPEN_Field is STM32.Bit;
   subtype APB1ENR_PWREN_Field is STM32.Bit;
   subtype APB1ENR_DACEN_Field is STM32.Bit;

   --  APB1 peripheral clock enable register (RCC_APB1ENR)
   type APB1ENR_Register is record
      --  Timer 2 clock enable
      TIM2EN         : APB1ENR_TIM2EN_Field := 16#0#;
      --  Timer 3 clock enable
      TIM3EN         : APB1ENR_TIM3EN_Field := 16#0#;
      --  Timer 4 clock enable
      TIM4EN         : APB1ENR_TIM4EN_Field := 16#0#;
      --  Timer 5 clock enable
      TIM5EN         : APB1ENR_TIM5EN_Field := 16#0#;
      --  Timer 6 clock enable
      TIM6EN         : APB1ENR_TIM6EN_Field := 16#0#;
      --  Timer 7 clock enable
      TIM7EN         : APB1ENR_TIM7EN_Field := 16#0#;
      --  unspecified
      Reserved_6_10  : STM32.UInt5 := 16#0#;
      --  Window watchdog clock enable
      WWDGEN         : APB1ENR_WWDGEN_Field := 16#0#;
      --  unspecified
      Reserved_12_13 : STM32.UInt2 := 16#0#;
      --  SPI 2 clock enable
      SPI2EN         : APB1ENR_SPI2EN_Field := 16#0#;
      --  SPI 3 clock enable
      SPI3EN         : APB1ENR_SPI3EN_Field := 16#0#;
      --  unspecified
      Reserved_16_16 : STM32.Bit := 16#0#;
      --  USART 2 clock enable
      USART2EN       : APB1ENR_USART2EN_Field := 16#0#;
      --  USART 3 clock enable
      USART3EN       : APB1ENR_USART3EN_Field := 16#0#;
      --  UART 4 clock enable
      UART4EN        : APB1ENR_UART4EN_Field := 16#0#;
      --  UART 5 clock enable
      UART5EN        : APB1ENR_UART5EN_Field := 16#0#;
      --  I2C 1 clock enable
      I2C1EN         : APB1ENR_I2C1EN_Field := 16#0#;
      --  I2C 2 clock enable
      I2C2EN         : APB1ENR_I2C2EN_Field := 16#0#;
      --  unspecified
      Reserved_23_24 : STM32.UInt2 := 16#0#;
      --  CAN1 clock enable
      CAN1EN         : APB1ENR_CAN1EN_Field := 16#0#;
      --  CAN2 clock enable
      CAN2EN         : APB1ENR_CAN2EN_Field := 16#0#;
      --  Backup interface clock enable
      BKPEN          : APB1ENR_BKPEN_Field := 16#0#;
      --  Power interface clock enable
      PWREN          : APB1ENR_PWREN_Field := 16#0#;
      --  DAC interface clock enable
      DACEN          : APB1ENR_DACEN_Field := 16#0#;
      --  unspecified
      Reserved_30_31 : STM32.UInt2 := 16#0#;
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
      Reserved_6_10  at 0 range 6 .. 10;
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
      Reserved_23_24 at 0 range 23 .. 24;
      CAN1EN         at 0 range 25 .. 25;
      CAN2EN         at 0 range 26 .. 26;
      BKPEN          at 0 range 27 .. 27;
      PWREN          at 0 range 28 .. 28;
      DACEN          at 0 range 29 .. 29;
      Reserved_30_31 at 0 range 30 .. 31;
   end record;

   -------------------
   -- BDCR_Register --
   -------------------

   subtype BDCR_LSEON_Field is STM32.Bit;
   subtype BDCR_LSERDY_Field is STM32.Bit;
   subtype BDCR_LSEBYP_Field is STM32.Bit;
   subtype BDCR_RTCSEL_Field is STM32.UInt2;
   subtype BDCR_RTCEN_Field is STM32.Bit;
   subtype BDCR_BDRST_Field is STM32.Bit;

   --  Backup domain control register (RCC_BDCR)
   type BDCR_Register is record
      --  External Low Speed oscillator enable
      LSEON          : BDCR_LSEON_Field := 16#0#;
      --  Read-only. External Low Speed oscillator ready
      LSERDY         : BDCR_LSERDY_Field := 16#0#;
      --  External Low Speed oscillator bypass
      LSEBYP         : BDCR_LSEBYP_Field := 16#0#;
      --  unspecified
      Reserved_3_7   : STM32.UInt5 := 16#0#;
      --  RTC clock source selection
      RTCSEL         : BDCR_RTCSEL_Field := 16#0#;
      --  unspecified
      Reserved_10_14 : STM32.UInt5 := 16#0#;
      --  RTC clock enable
      RTCEN          : BDCR_RTCEN_Field := 16#0#;
      --  Backup domain software reset
      BDRST          : BDCR_BDRST_Field := 16#0#;
      --  unspecified
      Reserved_17_31 : STM32.UInt15 := 16#0#;
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

   ------------------
   -- CSR_Register --
   ------------------

   subtype CSR_LSION_Field is STM32.Bit;
   subtype CSR_LSIRDY_Field is STM32.Bit;
   subtype CSR_RMVF_Field is STM32.Bit;
   subtype CSR_PINRSTF_Field is STM32.Bit;
   subtype CSR_PORRSTF_Field is STM32.Bit;
   subtype CSR_SFTRSTF_Field is STM32.Bit;
   subtype CSR_IWDGRSTF_Field is STM32.Bit;
   subtype CSR_WWDGRSTF_Field is STM32.Bit;
   subtype CSR_LPWRRSTF_Field is STM32.Bit;

   --  Control/status register (RCC_CSR)
   type CSR_Register is record
      --  Internal low speed oscillator enable
      LSION          : CSR_LSION_Field := 16#0#;
      --  Read-only. Internal low speed oscillator ready
      LSIRDY         : CSR_LSIRDY_Field := 16#0#;
      --  unspecified
      Reserved_2_23  : STM32.UInt22 := 16#0#;
      --  Remove reset flag
      RMVF           : CSR_RMVF_Field := 16#0#;
      --  unspecified
      Reserved_25_25 : STM32.Bit := 16#0#;
      --  PIN reset flag
      PINRSTF        : CSR_PINRSTF_Field := 16#1#;
      --  POR/PDR reset flag
      PORRSTF        : CSR_PORRSTF_Field := 16#1#;
      --  Software reset flag
      SFTRSTF        : CSR_SFTRSTF_Field := 16#0#;
      --  Independent watchdog reset flag
      IWDGRSTF       : CSR_IWDGRSTF_Field := 16#0#;
      --  Window watchdog reset flag
      WWDGRSTF       : CSR_WWDGRSTF_Field := 16#0#;
      --  Low-power reset flag
      LPWRRSTF       : CSR_LPWRRSTF_Field := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CSR_Register use record
      LSION          at 0 range 0 .. 0;
      LSIRDY         at 0 range 1 .. 1;
      Reserved_2_23  at 0 range 2 .. 23;
      RMVF           at 0 range 24 .. 24;
      Reserved_25_25 at 0 range 25 .. 25;
      PINRSTF        at 0 range 26 .. 26;
      PORRSTF        at 0 range 27 .. 27;
      SFTRSTF        at 0 range 28 .. 28;
      IWDGRSTF       at 0 range 29 .. 29;
      WWDGRSTF       at 0 range 30 .. 30;
      LPWRRSTF       at 0 range 31 .. 31;
   end record;

   ----------------------
   -- AHBRSTR_Register --
   ----------------------

   subtype AHBRSTR_OTGFSRST_Field is STM32.Bit;

   --  AHB peripheral clock reset register (RCC_AHBRSTR)
   type AHBRSTR_Register is record
      --  unspecified
      Reserved_0_11  : STM32.UInt12 := 16#0#;
      --  USB OTG FS reset
      OTGFSRST       : AHBRSTR_OTGFSRST_Field := 16#0#;
      --  unspecified
      Reserved_13_31 : STM32.UInt19 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for AHBRSTR_Register use record
      Reserved_0_11  at 0 range 0 .. 11;
      OTGFSRST       at 0 range 12 .. 12;
      Reserved_13_31 at 0 range 13 .. 31;
   end record;

   --------------------
   -- CFGR2_Register --
   --------------------

   ------------------
   -- CFGR2.PREDIV --
   ------------------

   --  CFGR2_PREDIV array element
   subtype CFGR2_PREDIV_Element is STM32.UInt4;

   --  CFGR2_PREDIV array
   type CFGR2_PREDIV_Field_Array is array (1 .. 2) of CFGR2_PREDIV_Element
     with Component_Size => 4, Size => 8;

   --  Type definition for CFGR2_PREDIV
   type CFGR2_PREDIV_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  PREDIV as a value
            Val : STM32.Byte;
         when True =>
            --  PREDIV as an array
            Arr : CFGR2_PREDIV_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 8;

   for CFGR2_PREDIV_Field use record
      Val at 0 range 0 .. 7;
      Arr at 0 range 0 .. 7;
   end record;

   subtype CFGR2_PLL2MUL_Field is STM32.UInt4;
   subtype CFGR2_PLL3MUL_Field is STM32.UInt4;
   subtype CFGR2_PREDIV1SRC_Field is STM32.Bit;
   subtype CFGR2_I2S2SRC_Field is STM32.Bit;
   subtype CFGR2_I2S3SRC_Field is STM32.Bit;

   --  Clock configuration register2 (RCC_CFGR2)
   type CFGR2_Register is record
      --  PREDIV1 division factor
      PREDIV         : CFGR2_PREDIV_Field :=
                        (As_Array => False, Val => 16#0#);
      --  PLL2 Multiplication Factor
      PLL2MUL        : CFGR2_PLL2MUL_Field := 16#0#;
      --  PLL3 Multiplication Factor
      PLL3MUL        : CFGR2_PLL3MUL_Field := 16#0#;
      --  PREDIV1 entry clock source
      PREDIV1SRC     : CFGR2_PREDIV1SRC_Field := 16#0#;
      --  I2S2 clock source
      I2S2SRC        : CFGR2_I2S2SRC_Field := 16#0#;
      --  I2S3 clock source
      I2S3SRC        : CFGR2_I2S3SRC_Field := 16#0#;
      --  unspecified
      Reserved_19_31 : STM32.UInt13 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CFGR2_Register use record
      PREDIV         at 0 range 0 .. 7;
      PLL2MUL        at 0 range 8 .. 11;
      PLL3MUL        at 0 range 12 .. 15;
      PREDIV1SRC     at 0 range 16 .. 16;
      I2S2SRC        at 0 range 17 .. 17;
      I2S3SRC        at 0 range 18 .. 18;
      Reserved_19_31 at 0 range 19 .. 31;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  Reset and clock control
   type RCC_Peripheral is record
      --  Clock control register
      CR       : CR_Register;
      --  Clock configuration register (RCC_CFGR)
      CFGR     : CFGR_Register;
      --  Clock interrupt register (RCC_CIR)
      CIR      : CIR_Register;
      --  APB2 peripheral reset register (RCC_APB2RSTR)
      APB2RSTR : APB2RSTR_Register;
      --  APB1 peripheral reset register (RCC_APB1RSTR)
      APB1RSTR : APB1RSTR_Register;
      --  AHB Peripheral Clock enable register (RCC_AHBENR)
      AHBENR   : AHBENR_Register;
      --  APB2 peripheral clock enable register (RCC_APB2ENR)
      APB2ENR  : APB2ENR_Register;
      --  APB1 peripheral clock enable register (RCC_APB1ENR)
      APB1ENR  : APB1ENR_Register;
      --  Backup domain control register (RCC_BDCR)
      BDCR     : BDCR_Register;
      --  Control/status register (RCC_CSR)
      CSR      : CSR_Register;
      --  AHB peripheral clock reset register (RCC_AHBRSTR)
      AHBRSTR  : AHBRSTR_Register;
      --  Clock configuration register2 (RCC_CFGR2)
      CFGR2    : CFGR2_Register;
   end record
     with Volatile;

   for RCC_Peripheral use record
      CR       at 0 range 0 .. 31;
      CFGR     at 4 range 0 .. 31;
      CIR      at 8 range 0 .. 31;
      APB2RSTR at 12 range 0 .. 31;
      APB1RSTR at 16 range 0 .. 31;
      AHBENR   at 20 range 0 .. 31;
      APB2ENR  at 24 range 0 .. 31;
      APB1ENR  at 28 range 0 .. 31;
      BDCR     at 32 range 0 .. 31;
      CSR      at 36 range 0 .. 31;
      AHBRSTR  at 40 range 0 .. 31;
      CFGR2    at 44 range 0 .. 31;
   end record;

   --  Reset and clock control
   RCC_Periph : aliased RCC_Peripheral
     with Import, Address => RCC_Base;

end STM32.RCC;
