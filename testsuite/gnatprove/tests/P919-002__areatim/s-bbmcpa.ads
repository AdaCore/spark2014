package System.BB.MCU_Parameters is

   type PWR_Peripheral is record
      VOSRDY : Integer := 0;
   end record;

   PWR_Periph : PWR_Peripheral;

   function Is_PWR_Stabilized return Boolean
     is (PWR_Periph.VOSRDY = 1);

end System.BB.MCU_Parameters;
