--  This spec has been automatically generated from STM32F429x.svd

pragma Restrictions (No_Elaboration_Code);
pragma Ada_2012;

with System;

--  STM32F429x
package STM32_SVD is
   pragma Preelaborate;

   --------------------
   -- Base addresses --
   --------------------

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

end STM32_SVD;
