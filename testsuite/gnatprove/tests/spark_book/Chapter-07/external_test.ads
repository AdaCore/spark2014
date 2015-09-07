package External_Test
   with Spark_Mode => On
is
   type Byte is mod 256;

   procedure Test (Item : out Byte);
end External_Test;
