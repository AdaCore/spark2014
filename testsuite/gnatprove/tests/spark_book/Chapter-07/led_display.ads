package LED_Display
   with Spark_Mode     => On,
        Abstract_State => (LED_State
                              with External => (Async_Readers    => True,
                                                Effective_Writes => True))
is
   subtype Digit_Type is Integer range 0 .. 9;

   procedure Display_Digit (Digit : in Digit_Type)
     with
        Global => (Output => LED_State);

end LED_Display;
