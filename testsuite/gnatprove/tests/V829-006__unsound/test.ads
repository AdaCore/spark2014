package Test
  with Spark_Mode => On
is
   type Nibble is mod 2**4;

   procedure Wrong
     with Post => False; --@POSTCONDITION:FAIL
end Test;
