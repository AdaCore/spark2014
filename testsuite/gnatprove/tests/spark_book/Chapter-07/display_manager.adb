package body Display_Manager
  with SPARK_Mode => On
is

   procedure Display_Digit(Digit : Digit_Type) is
      -- Segments 'a' through 'g' are in order from least to most significant bit. Active high.
      Patterns : constant array(Digit_Type) of Numeric_Display.Octet :=
        (2#0011_1111#, 2#0000_0110#, 2#0101_1011#, 2#0100_1111#, 2#0110_0110#,
         2#0110_1101#, 2#0111_1101#, 2#0000_0111#, 2#0111_1111#, 2#0110_0111#);
   begin
      Numeric_Display.Value := 0;
      Numeric_Display.Value := Patterns(Digit);
   end Display_Digit;

end Display_Manager;
