--bit_converter.ads

package Bit_Converter
  with SPARK_Mode => On
is

  type Modular_Type is mod 2**8;
  subtype Zero_or_One is Modular_Type range 0 .. 1;
  subtype Index_Type is Positive range 1 .. Modular_Type'Size;
  type Bit_Array is array (Index_Type range <>) of Boolean;

  function To_Number( Bool : in Boolean ) return Zero_or_One
    with Global => null;

  function To_Modular_Type( Array_of_Bits : in Bit_Array )return Modular_Type
    with Global => null,
         Pre => Array_of_Bits'Size > 0;
           -- ! used Size instead of Length attribute and got the error !

end Bit_Converter;
