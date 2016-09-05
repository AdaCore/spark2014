--  This spec has been automatically generated from STM32F429x.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

package STM32_SVD.GPIO is
   pragma Preelaborate;

   ---------------
   -- Registers --
   ---------------

   --  MODER array element
   subtype MODER_Element is STM32_SVD.UInt2;

   --  MODER array
   type MODER_Field_Array is array (0 .. 15) of MODER_Element
     with Component_Size => 2, Size => 32;

   --  GPIO port mode register
   type MODER_Register
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  MODER as a value
            Val : STM32_SVD.Word;
         when True =>
            --  MODER as an array
            Arr : MODER_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 32, Volatile_Full_Access,
          Bit_Order => System.Low_Order_First;

   for MODER_Register use record
      Val at 0 range 0 .. 31;
      Arr at 0 range 0 .. 31;
   end record;

   --  OTYPER_OT array element
   subtype OTYPER_OT_Element is STM32_SVD.Bit;

   --  OTYPER_OT array
   type OTYPER_OT_Field_Array is array (0 .. 15) of OTYPER_OT_Element
     with Component_Size => 1, Size => 16;

   --  Type definition for OTYPER_OT
   type OTYPER_OT_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  OT as a value
            Val : STM32_SVD.Short;
         when True =>
            --  OT as an array
            Arr : OTYPER_OT_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 16;

   for OTYPER_OT_Field use record
      Val at 0 range 0 .. 15;
      Arr at 0 range 0 .. 15;
   end record;

   --  GPIO port output type register
   type OTYPER_Register is record
      --  Port x configuration bits (y = 0..15)
      OT             : OTYPER_OT_Field := (As_Array => False, Val => 16#0#);
      --  unspecified
      Reserved_16_31 : STM32_SVD.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for OTYPER_Register use record
      OT             at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   --  OSPEEDR array element
   subtype OSPEEDR_Element is STM32_SVD.UInt2;

   --  OSPEEDR array
   type OSPEEDR_Field_Array is array (0 .. 15) of OSPEEDR_Element
     with Component_Size => 2, Size => 32;

   --  GPIO port output speed register
   type OSPEEDR_Register
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  OSPEEDR as a value
            Val : STM32_SVD.Word;
         when True =>
            --  OSPEEDR as an array
            Arr : OSPEEDR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 32, Volatile_Full_Access,
          Bit_Order => System.Low_Order_First;

   for OSPEEDR_Register use record
      Val at 0 range 0 .. 31;
      Arr at 0 range 0 .. 31;
   end record;

   --  PUPDR array element
   subtype PUPDR_Element is STM32_SVD.UInt2;

   --  PUPDR array
   type PUPDR_Field_Array is array (0 .. 15) of PUPDR_Element
     with Component_Size => 2, Size => 32;

   --  GPIO port pull-up/pull-down register
   type PUPDR_Register
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  PUPDR as a value
            Val : STM32_SVD.Word;
         when True =>
            --  PUPDR as an array
            Arr : PUPDR_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 32, Volatile_Full_Access,
          Bit_Order => System.Low_Order_First;

   for PUPDR_Register use record
      Val at 0 range 0 .. 31;
      Arr at 0 range 0 .. 31;
   end record;

   --  IDR array element
   subtype IDR_Element is STM32_SVD.Bit;

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
            Val : STM32_SVD.Short;
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

   --  GPIO port input data register
   type IDR_Register is record
      --  Read-only. Port input data (y = 0..15)
      IDR            : IDR_Field;
      --  unspecified
      Reserved_16_31 : STM32_SVD.Short;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for IDR_Register use record
      IDR            at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   --  ODR array element
   subtype ODR_Element is STM32_SVD.Bit;

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
            Val : STM32_SVD.Short;
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

   --  GPIO port output data register
   type ODR_Register is record
      --  Port output data (y = 0..15)
      ODR            : ODR_Field := (As_Array => False, Val => 16#0#);
      --  unspecified
      Reserved_16_31 : STM32_SVD.Short := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for ODR_Register use record
      ODR            at 0 range 0 .. 15;
      Reserved_16_31 at 0 range 16 .. 31;
   end record;

   --  BSRR_BS array element
   subtype BSRR_BS_Element is STM32_SVD.Bit;

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
            Val : STM32_SVD.Short;
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

   --  BSRR_BR array element
   subtype BSRR_BR_Element is STM32_SVD.Bit;

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
            Val : STM32_SVD.Short;
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

   --  GPIO port bit set/reset register
   type BSRR_Register is record
      --  Write-only. Port x set bit y (y= 0..15)
      BS : BSRR_BS_Field := (As_Array => False, Val => 16#0#);
      --  Write-only. Port x set bit y (y= 0..15)
      BR : BSRR_BR_Field := (As_Array => False, Val => 16#0#);
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for BSRR_Register use record
      BS at 0 range 0 .. 15;
      BR at 0 range 16 .. 31;
   end record;

   --  LCKR_LCK array element
   subtype LCKR_LCK_Element is STM32_SVD.Bit;

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
            Val : STM32_SVD.Short;
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

   subtype LCKR_LCKK_Field is STM32_SVD.Bit;

   --  GPIO port configuration lock register
   type LCKR_Register is record
      --  Port x lock bit y (y= 0..15)
      LCK            : LCKR_LCK_Field := (As_Array => False, Val => 16#0#);
      --  Port x lock bit y (y= 0..15)
      LCKK           : LCKR_LCKK_Field := 16#0#;
      --  unspecified
      Reserved_17_31 : STM32_SVD.UInt15 := 16#0#;
   end record
     with Volatile_Full_Access, Size => 32,
          Bit_Order => System.Low_Order_First;

   for LCKR_Register use record
      LCK            at 0 range 0 .. 15;
      LCKK           at 0 range 16 .. 16;
      Reserved_17_31 at 0 range 17 .. 31;
   end record;

   --  AFRL array element
   subtype AFRL_Element is STM32_SVD.UInt4;

   --  AFRL array
   type AFRL_Field_Array is array (0 .. 7) of AFRL_Element
     with Component_Size => 4, Size => 32;

   --  GPIO alternate function low register
   type AFRL_Register
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  AFRL as a value
            Val : STM32_SVD.Word;
         when True =>
            --  AFRL as an array
            Arr : AFRL_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 32, Volatile_Full_Access,
          Bit_Order => System.Low_Order_First;

   for AFRL_Register use record
      Val at 0 range 0 .. 31;
      Arr at 0 range 0 .. 31;
   end record;

   --  AFRH array element
   subtype AFRH_Element is STM32_SVD.UInt4;

   --  AFRH array
   type AFRH_Field_Array is array (8 .. 15) of AFRH_Element
     with Component_Size => 4, Size => 32;

   --  GPIO alternate function high register
   type AFRH_Register
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  AFRH as a value
            Val : STM32_SVD.Word;
         when True =>
            --  AFRH as an array
            Arr : AFRH_Field_Array;
      end case;
   end record
     with Unchecked_Union, Size => 32, Volatile_Full_Access,
          Bit_Order => System.Low_Order_First;

   for AFRH_Register use record
      Val at 0 range 0 .. 31;
      Arr at 0 range 0 .. 31;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  General-purpose I/Os
   type GPIO_Peripheral is record
      --  GPIO port mode register
      MODER   : MODER_Register;
      --  GPIO port output type register
      OTYPER  : OTYPER_Register;
      --  GPIO port output speed register
      OSPEEDR : OSPEEDR_Register;
      --  GPIO port pull-up/pull-down register
      PUPDR   : PUPDR_Register;
      --  GPIO port input data register
      IDR     : IDR_Register;
      --  GPIO port output data register
      ODR     : ODR_Register;
      --  GPIO port bit set/reset register
      BSRR    : BSRR_Register;
      --  GPIO port configuration lock register
      LCKR    : LCKR_Register;
      --  GPIO alternate function low register
      AFRL    : AFRL_Register;
      --  GPIO alternate function high register
      AFRH    : AFRH_Register;
   end record
     with Volatile;

   for GPIO_Peripheral use record
      MODER   at 0 range 0 .. 31;
      OTYPER  at 4 range 0 .. 31;
      OSPEEDR at 8 range 0 .. 31;
      PUPDR   at 12 range 0 .. 31;
      IDR     at 16 range 0 .. 31;
      ODR     at 20 range 0 .. 31;
      BSRR    at 24 range 0 .. 31;
      LCKR    at 28 range 0 .. 31;
      AFRL    at 32 range 0 .. 31;
      AFRH    at 36 range 0 .. 31;
   end record;

   --  General-purpose I/Os
   GPIOA_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOA_Base;

   --  General-purpose I/Os
   GPIOB_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOB_Base;

   --  General-purpose I/Os
   GPIOC_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOC_Base;

   --  General-purpose I/Os
   GPIOD_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOD_Base;

   --  General-purpose I/Os
   GPIOE_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOE_Base;

   --  General-purpose I/Os
   GPIOF_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOF_Base;

   --  General-purpose I/Os
   GPIOG_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOG_Base;

   --  General-purpose I/Os
   GPIOH_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOH_Base;

   --  General-purpose I/Os
   GPIOI_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOI_Base;

   --  General-purpose I/Os
   GPIOJ_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOJ_Base;

   --  General-purpose I/Os
   GPIOK_Periph : aliased GPIO_Peripheral
     with Import, Address => GPIOK_Base;

end STM32_SVD.GPIO;
