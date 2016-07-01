--  This spec has been automatically generated from STM32F105xx.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

package STM32.GPIO is
   pragma Preelaborate;

   ---------------
   -- Registers --
   ---------------

   ------------------
   -- CRL_Register --
   ------------------

   subtype CRL_MODE0_Field is STM32.UInt2;
   subtype CRL_CNF0_Field is STM32.UInt2;
   subtype CRL_MODE1_Field is STM32.UInt2;
   subtype CRL_CNF1_Field is STM32.UInt2;
   subtype CRL_MODE2_Field is STM32.UInt2;
   subtype CRL_CNF2_Field is STM32.UInt2;
   subtype CRL_MODE3_Field is STM32.UInt2;
   subtype CRL_CNF3_Field is STM32.UInt2;
   subtype CRL_MODE4_Field is STM32.UInt2;
   subtype CRL_CNF4_Field is STM32.UInt2;
   subtype CRL_MODE5_Field is STM32.UInt2;
   subtype CRL_CNF5_Field is STM32.UInt2;
   subtype CRL_MODE6_Field is STM32.UInt2;
   subtype CRL_CNF6_Field is STM32.UInt2;
   subtype CRL_MODE7_Field is STM32.UInt2;
   subtype CRL_CNF7_Field is STM32.UInt2;

   --  Port configuration register low (GPIOn_CRL)
   type CRL_Register is record
      --  Port n.0 mode bits
      MODE0 : CRL_MODE0_Field := 16#0#;
      --  Port n.0 configuration bits
      CNF0  : CRL_CNF0_Field := 16#1#;
      --  Port n.1 mode bits
      MODE1 : CRL_MODE1_Field := 16#0#;
      --  Port n.1 configuration bits
      CNF1  : CRL_CNF1_Field := 16#1#;
      --  Port n.2 mode bits
      MODE2 : CRL_MODE2_Field := 16#0#;
      --  Port n.2 configuration bits
      CNF2  : CRL_CNF2_Field := 16#1#;
      --  Port n.3 mode bits
      MODE3 : CRL_MODE3_Field := 16#0#;
      --  Port n.3 configuration bits
      CNF3  : CRL_CNF3_Field := 16#1#;
      --  Port n.4 mode bits
      MODE4 : CRL_MODE4_Field := 16#0#;
      --  Port n.4 configuration bits
      CNF4  : CRL_CNF4_Field := 16#1#;
      --  Port n.5 mode bits
      MODE5 : CRL_MODE5_Field := 16#0#;
      --  Port n.5 configuration bits
      CNF5  : CRL_CNF5_Field := 16#1#;
      --  Port n.6 mode bits
      MODE6 : CRL_MODE6_Field := 16#0#;
      --  Port n.6 configuration bits
      CNF6  : CRL_CNF6_Field := 16#1#;
      --  Port n.7 mode bits
      MODE7 : CRL_MODE7_Field := 16#0#;
      --  Port n.7 configuration bits
      CNF7  : CRL_CNF7_Field := 16#1#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CRL_Register use record
      MODE0 at 0 range 0 .. 1;
      CNF0  at 0 range 2 .. 3;
      MODE1 at 0 range 4 .. 5;
      CNF1  at 0 range 6 .. 7;
      MODE2 at 0 range 8 .. 9;
      CNF2  at 0 range 10 .. 11;
      MODE3 at 0 range 12 .. 13;
      CNF3  at 0 range 14 .. 15;
      MODE4 at 0 range 16 .. 17;
      CNF4  at 0 range 18 .. 19;
      MODE5 at 0 range 20 .. 21;
      CNF5  at 0 range 22 .. 23;
      MODE6 at 0 range 24 .. 25;
      CNF6  at 0 range 26 .. 27;
      MODE7 at 0 range 28 .. 29;
      CNF7  at 0 range 30 .. 31;
   end record;

   ------------------
   -- CRH_Register --
   ------------------

   subtype CRH_MODE8_Field is STM32.UInt2;
   subtype CRH_CNF8_Field is STM32.UInt2;
   subtype CRH_MODE9_Field is STM32.UInt2;
   subtype CRH_CNF9_Field is STM32.UInt2;
   subtype CRH_MODE10_Field is STM32.UInt2;
   subtype CRH_CNF10_Field is STM32.UInt2;
   subtype CRH_MODE11_Field is STM32.UInt2;
   subtype CRH_CNF11_Field is STM32.UInt2;
   subtype CRH_MODE12_Field is STM32.UInt2;
   subtype CRH_CNF12_Field is STM32.UInt2;
   subtype CRH_MODE13_Field is STM32.UInt2;
   subtype CRH_CNF13_Field is STM32.UInt2;
   subtype CRH_MODE14_Field is STM32.UInt2;
   subtype CRH_CNF14_Field is STM32.UInt2;
   subtype CRH_MODE15_Field is STM32.UInt2;
   subtype CRH_CNF15_Field is STM32.UInt2;

   --  Port configuration register high (GPIOn_CRL)
   type CRH_Register is record
      --  Port n.8 mode bits
      MODE8  : CRH_MODE8_Field := 16#0#;
      --  Port n.8 configuration bits
      CNF8   : CRH_CNF8_Field := 16#1#;
      --  Port n.9 mode bits
      MODE9  : CRH_MODE9_Field := 16#0#;
      --  Port n.9 configuration bits
      CNF9   : CRH_CNF9_Field := 16#1#;
      --  Port n.10 mode bits
      MODE10 : CRH_MODE10_Field := 16#0#;
      --  Port n.10 configuration bits
      CNF10  : CRH_CNF10_Field := 16#1#;
      --  Port n.11 mode bits
      MODE11 : CRH_MODE11_Field := 16#0#;
      --  Port n.11 configuration bits
      CNF11  : CRH_CNF11_Field := 16#1#;
      --  Port n.12 mode bits
      MODE12 : CRH_MODE12_Field := 16#0#;
      --  Port n.12 configuration bits
      CNF12  : CRH_CNF12_Field := 16#1#;
      --  Port n.13 mode bits
      MODE13 : CRH_MODE13_Field := 16#0#;
      --  Port n.13 configuration bits
      CNF13  : CRH_CNF13_Field := 16#1#;
      --  Port n.14 mode bits
      MODE14 : CRH_MODE14_Field := 16#0#;
      --  Port n.14 configuration bits
      CNF14  : CRH_CNF14_Field := 16#1#;
      --  Port n.15 mode bits
      MODE15 : CRH_MODE15_Field := 16#0#;
      --  Port n.15 configuration bits
      CNF15  : CRH_CNF15_Field := 16#1#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for CRH_Register use record
      MODE8  at 0 range 0 .. 1;
      CNF8   at 0 range 2 .. 3;
      MODE9  at 0 range 4 .. 5;
      CNF9   at 0 range 6 .. 7;
      MODE10 at 0 range 8 .. 9;
      CNF10  at 0 range 10 .. 11;
      MODE11 at 0 range 12 .. 13;
      CNF11  at 0 range 14 .. 15;
      MODE12 at 0 range 16 .. 17;
      CNF12  at 0 range 18 .. 19;
      MODE13 at 0 range 20 .. 21;
      CNF13  at 0 range 22 .. 23;
      MODE14 at 0 range 24 .. 25;
      CNF14  at 0 range 26 .. 27;
      MODE15 at 0 range 28 .. 29;
      CNF15  at 0 range 30 .. 31;
   end record;

   ------------------
   -- IDR_Register --
   ------------------

   -------------
   -- IDR.IDR --
   -------------

   --  IDR array element
   subtype IDR_Element is STM32.Bit;

   --  IDR array
   type IDR_Field_Array is array (0 .. 15) of IDR_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for IDR
   type IDR_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  IDR as a value
            Val : STM32.Short;
         when True =>
            --  IDR as an array
            Arr : IDR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for IDR_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   --  Port input data register (GPIOn_IDR)
   type IDR_Register is record
      --  Read-only. Port input data
      IDR            : IDR_Field;
      --  unspecified
      Reserved_16_31 : STM32.Short;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for IDR_Register use record
      IDR            at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   ------------------
   -- ODR_Register --
   ------------------

   -------------
   -- ODR.ODR --
   -------------

   --  ODR array element
   subtype ODR_Element is STM32.Bit;

   --  ODR array
   type ODR_Field_Array is array (0 .. 15) of ODR_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for ODR
   type ODR_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  ODR as a value
            Val : STM32.Short;
         when True =>
            --  ODR as an array
            Arr : ODR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for ODR_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   --  Port output data register (GPIOn_ODR)
   type ODR_Register is record
      --  Port output data
      ODR            : ODR_Field := (As_Array => False, Val => 16#0#);
      --  unspecified
      Reserved_16_31 : STM32.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for ODR_Register use record
      ODR            at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   -------------------
   -- BSRR_Register --
   -------------------

   -------------
   -- BSRR.BS --
   -------------

   --  BSRR_BS array element
   subtype BSRR_BS_Element is STM32.Bit;

   --  BSRR_BS array
   type BSRR_BS_Field_Array is array (0 .. 15) of BSRR_BS_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for BSRR_BS
   type BSRR_BS_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  BS as a value
            Val : STM32.Short;
         when True =>
            --  BS as an array
            Arr : BSRR_BS_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for BSRR_BS_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   -------------
   -- BSRR.BR --
   -------------

   --  BSRR_BR array element
   subtype BSRR_BR_Element is STM32.Bit;

   --  BSRR_BR array
   type BSRR_BR_Field_Array is array (0 .. 15) of BSRR_BR_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for BSRR_BR
   type BSRR_BR_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  BR as a value
            Val : STM32.Short;
         when True =>
            --  BR as an array
            Arr : BSRR_BR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for BSRR_BR_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   --  Port bit set/reset register (GPIOn_BSRR)
   type BSRR_Register is record
      --  Write-only. Set bit 0
      BS : BSRR_BS_Field := (As_Array => False, Val => 16#0#);
      --  Write-only. Reset bit 0
      BR : BSRR_BR_Field := (As_Array => False, Val => 16#0#);
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for BSRR_Register use record
      BS at 0 range 0 .. 15;
      BR at 0 range 16 .. 31;
   end record;

   ------------------
   -- BRR_Register --
   ------------------

   ------------
   -- BRR.BR --
   ------------

   --  BRR_BR array element
   subtype BRR_BR_Element is STM32.Bit;

   --  BRR_BR array
   type BRR_BR_Field_Array is array (0 .. 15) of BRR_BR_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for BRR_BR
   type BRR_BR_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  BR as a value
            Val : STM32.Short;
         when True =>
            --  BR as an array
            Arr : BRR_BR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for BRR_BR_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   --  Port bit reset register (GPIOn_BRR)
   type BRR_Register is record
      --  Write-only. Reset bit 0
      BR             : BRR_BR_Field := (As_Array => False, Val => 16#0#);
      --  unspecified
      Reserved_16_31 : STM32.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for BRR_Register use record
      BR             at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   -------------------
   -- LCKR_Register --
   -------------------

   --------------
   -- LCKR.LCK --
   --------------

   --  LCKR_LCK array element
   subtype LCKR_LCK_Element is STM32.Bit;

   --  LCKR_LCK array
   type LCKR_LCK_Field_Array is array (0 .. 15) of LCKR_LCK_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for LCKR_LCK
   type LCKR_LCK_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  LCK as a value
            Val : STM32.Short;
         when True =>
            --  LCK as an array
            Arr : LCKR_LCK_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for LCKR_LCK_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   subtype LCKR_LCKK_Field is STM32.Bit;

   --  Port configuration lock register
   type LCKR_Register is record
      --  Port A Lock bit 0
      LCK            : LCKR_LCK_Field := (As_Array => False, Val => 16#0#);
      --  Lock key
      LCKK           : LCKR_LCKK_Field := 16#0#;
      --  unspecified
      Reserved_17_31 : STM32.UInt15 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for LCKR_Register use record
      LCK            at 0 range 0 .. 15;
      LCKK           at 0 range 16 .. 16;
      Reserved_17_31 at 0 range 17 .. 31;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  General purpose I/O
   type GPIO_Peripheral is record
      --  Port configuration register low (GPIOn_CRL)
      CRL  : CRL_Register;
      --  Port configuration register high (GPIOn_CRL)
      CRH  : CRH_Register;
      --  Port input data register (GPIOn_IDR)
      IDR  : IDR_Register;
      --  Port output data register (GPIOn_ODR)
      ODR  : ODR_Register;
      --  Port bit set/reset register (GPIOn_BSRR)
      BSRR : BSRR_Register;
      --  Port bit reset register (GPIOn_BRR)
      BRR  : BRR_Register;
      --  Port configuration lock register
      LCKR : LCKR_Register;
   end record
     with Volatile;

   for GPIO_Peripheral use record
      CRL  at 0 range 0 .. 31;
      CRH  at 4 range 0 .. 31;
      IDR  at 8 range 0 .. 31;
      ODR  at 12 range 0 .. 31;
      BSRR at 16 range 0 .. 31;
      BRR  at 20 range 0 .. 31;
      LCKR at 24 range 0 .. 31;
   end record;

   --  General purpose I/O
   GPIOA_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOA_Base;

   --  General purpose I/O
   GPIOB_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOB_Base;

   --  General purpose I/O
   GPIOC_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOC_Base;

   --  General purpose I/O
   GPIOD_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOD_Base;

   --  General purpose I/O
   GPIOE_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOE_Base;

end STM32.GPIO;
