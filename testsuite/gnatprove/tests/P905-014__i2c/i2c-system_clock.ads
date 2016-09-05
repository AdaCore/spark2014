with Interfaces;

private package I2C.System_Clock
with SPARK_Mode => Off
is

   subtype Frequency is Interfaces.Unsigned_32;  -- e.g.42 MHz

   function PCLK1 return Frequency
   with
     Inline;

end I2C.System_Clock;
