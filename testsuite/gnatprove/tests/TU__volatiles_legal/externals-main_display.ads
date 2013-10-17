private package Externals.Main_Display
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Readers,
                                     Part_Of  => Externals.Displays)
is
   procedure Display (Text: in String)
     with Global => (Output => State),
          Depends => (State => Text);
end Externals.Main_Display;
