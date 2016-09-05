with I2C;
with STM32_SVD.GPIO;
with STM32_SVD.I2C;

package I2C3_Support
with
  SPARK_Mode => Off
is

   package Instantiation is new I2C.G
     (SCL_Enable => (GPIOAEN => 1, others => <>),
      SCL_GPIO   => STM32_SVD.GPIO.GPIOA_Periph,
      SCL_Pin    => 8,
      SDA_Enable => (GPIOCEN => 1, others => <>),
      SDA_GPIO   => STM32_SVD.GPIO.GPIOC_Periph,
      SDA_Pin    => 9,
      I2C_Enable => (I2C3EN => 1, others => <>),
      I2C_Periph => STM32_SVD.I2C.I2C3_Periph);

end I2C3_Support;
