with System.Storage_Elements;
package Numeric_Display
  with SPARK_Mode => On
is
   type Octet is mod 2**8;

   Value : Octet
     with
       Size => 8,  -- Use exactly 8 bits for this variable
       Volatile         => True,
       Async_Readers    => True,
       Effective_Writes => True,
       Address => System.Storage_Elements.To_Address(16#FFFF0000#);

end Numeric_Display;
