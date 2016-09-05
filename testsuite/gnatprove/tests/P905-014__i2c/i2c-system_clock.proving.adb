package body I2C.System_Clock
with SPARK_Mode => Off
is

   function PCLK1 return Frequency is (42_000_000);

end I2C.System_Clock;
