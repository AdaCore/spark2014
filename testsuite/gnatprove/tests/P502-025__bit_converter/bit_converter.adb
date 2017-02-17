
--bit_converter.adb

package body Bit_Converter
  with SPARK_Mode => On
is

  function To_Number( Bool : in Boolean ) return Zero_or_One is
  begin
    return (case Bool is
              when False => 0,
              when True => 1);
  end To_Number;


  function To_Modular_Type( Array_of_Bits : in Bit_Array )
                           return Modular_Type
  is

    First_Index : constant Index_Type := Array_of_Bits'First;
    Last_Index  : constant Index_Type := Array_of_Bits'Last;
    Bits : Modular_Type := 0;
    Bit : Zero_or_One;

  begin
    Bit := To_Number( Array_of_Bits(First_Index) );
    Bits := Bits or Bit;

    for I in First_Index + 1 .. Last_Index loop
      Bits := Bits * 2;
      Bit := To_Number( Array_of_Bits(I) );
      Bits := Bits or Bit;
    end loop;

    return Bits;
  end To_Modular_Type;

end Bit_Converter;
