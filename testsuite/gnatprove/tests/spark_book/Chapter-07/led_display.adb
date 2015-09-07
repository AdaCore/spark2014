with System.Storage_Elements;
package body Led_Display
   with SPARK_Mode    => On,
        Refined_State => (LED_State => Value)
is
   type Octet is mod 2 ** 8;

   Value : Octet
      with
         Size => 8,  -- Use exactly 8 bits for this variable
         Volatile         => True,
         Async_Readers    => True,
         Effective_Writes => True,
         Address => System.Storage_Elements.To_Address(16#FFFF0000#);

   -- Segments 'a' through 'g' are in order from least to most ignificant bit.
   -- Active high.
   Patterns : constant array (Digit_Type) of Octet :=
              (2#0011_1111#, 2#0000_0110#, 2#0101_1011#, 2#0100_1111#,
               2#0110_0110#, 2#0110_1101#, 2#0111_1101#, 2#0000_0111#,
               2#0111_1111#, 2#0110_0111#);

   procedure Display_Digit (Digit : in Digit_Type)
      with Refined_Global => (Output => Value)
   is
   begin
      Value := Patterns (Digit);
   end Display_Digit;

end LED_Display;
