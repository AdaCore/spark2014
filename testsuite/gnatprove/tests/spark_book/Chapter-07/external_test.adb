with System.Storage_Elements;
package body External_Test
   with Spark_Mode => On
is

   Value : Byte
     with
       Volatile,
       Async_Readers,
       Effective_Writes,
       Address => System.Storage_Elements.To_Address(16#FFFF0000#);


   procedure Test (Item : out Byte) is
   begin
      Item := Value;
      Item := Value;

      Value := 5;
      Value := 17;

   end Test;

end External_Test;
