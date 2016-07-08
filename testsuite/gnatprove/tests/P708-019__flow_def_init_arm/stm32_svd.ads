package STM32_SVD is

   type UInt3 is mod 2**3
     with Size => 3;

   type UInt6 is mod 2**6
     with Size => 6;

   ---------------
   -- Registers --
   ---------------

   ---------------
   -- CFGR.PPRE --
   ---------------

   --  CFGR_PPRE array element
   subtype CFGR_PPRE_Element is UInt3;

   --  CFGR_PPRE array
   type CFGR_PPRE_Field_Array is array (1 .. 2) of CFGR_PPRE_Element;

   --  Type definition for CFGR_PPRE
   type CFGR_PPRE_Field
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            --  PPRE as a value
            Val : UInt6;
         when True =>
            --  PPRE as an array
            Arr : CFGR_PPRE_Field_Array;
      end case;
   end record;

   --  clock configuration register
   type CFGR_Register is record
      --  APB Low speed prescaler (APB1)
      PPRE : CFGR_PPRE_Field := (As_Array => False, Val => 16#0#);
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  Reset and clock control
   type RCC_Peripheral is record
      --  clock configuration register
      CFGR : CFGR_Register;
   end record;

   --  Reset and clock control
   RCC_Periph : RCC_Peripheral;

end STM32_SVD;
