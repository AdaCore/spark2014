with Numeric_Display;

package Display_Manager
  with SPARK_Mode => On
is
   subtype Digit_Type is Integer range 0 .. 9;

   procedure Display_Digit(Digit : in Digit_Type)
     with
       Global => (Output => Numeric_Display.Value);

end Display_Manager;
