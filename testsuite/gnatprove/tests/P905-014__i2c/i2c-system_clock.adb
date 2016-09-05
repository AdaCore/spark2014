pragma Warnings (Off, "*internal GNAT unit");
with System.STM32;
pragma Warnings (On, "*internal GNAT unit");

package body I2C.System_Clock
with SPARK_Mode => Off
is

   function PCLK1 return Frequency
   is (Frequency'(System.STM32.System_Clocks.PCLK1));

end I2C.System_Clock;
