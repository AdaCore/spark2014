--  Demonstration code for the AdaPilot project
--  (http://adapilot.likeabird.eu).
--  Copyright (C) 2016 Simon Wright <simon@pushface.org>

with STM32_SVD.GPIO;
with STM32_SVD.I2C;
with STM32_SVD.RCC;

package I2C
with SPARK_Mode => On
is

   --  The I2C address of the peripheral being addressed
   subtype Chip_Address is STM32_SVD.Byte;

   subtype GPIO_Pin is Integer range 0 .. 15;

   generic
      --  Enables the GPIO used by the SCL
      SCL_Enable   : STM32_SVD.RCC.AHB1ENR_Register;

      --  The GPIO used by the SCL
      SCL_GPIO     : in out STM32_SVD.GPIO.GPIO_Peripheral;

      --  The pin used by the SCL
      SCL_Pin      : GPIO_Pin;

      --  Enables the GPIO used by the SDA
      SDA_Enable   : STM32_SVD.RCC.AHB1ENR_Register;

      --  The GPIO used by the SDA
      SDA_GPIO     : in out STM32_SVD.GPIO.GPIO_Peripheral;

      --  The pin used by the SDA
      SDA_Pin      : GPIO_Pin;

      --  Enables the I2C
      I2C_Enable   : STM32_SVD.RCC.APB1ENR_Register;

      --  The I2C used
      I2C_Periph   : in out STM32_SVD.I2C.I2C_Peripheral;
   package G
   is

      function Initialized return Boolean;

      procedure Initialize
      with
        Pre => not Initialized,
        Post => Initialized;

      function Read (From : Chip_Address) return STM32_SVD.Byte
      with
        Pre => Initialized;

      procedure Write (To : Chip_Address; B : STM32_SVD.Byte)
      with Pre => Initialized;

   end G;

end I2C;
