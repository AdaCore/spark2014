package System.BB.MCU_Parameters is
   pragma No_Elaboration_Code_All;
   pragma Preelaborate;

   Number_Of_Interrupts : constant := 92;

   type Bit is mod 2**1
     with Size => 1;

   subtype CSR_VOSRDY_Field is Bit;

   --  power control/status register
   type CSR_Register is record
      VOSRDY         : CSR_VOSRDY_Field := 16#0#;
   end record;

   -----------------
   -- Peripherals --
   -----------------

   --  Power control
   type PWR_Peripheral is record
      --  power control/status register
      CSR : CSR_Register;
   end record;

   PWR_Periph : PWR_Peripheral;

   function Is_PWR_Stabilized return Boolean
     is (PWR_Periph.CSR.VOSRDY = 1);

end System.BB.MCU_Parameters;
