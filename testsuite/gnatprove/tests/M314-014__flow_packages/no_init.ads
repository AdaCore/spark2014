package No_Init
  with SPARK_Mode,
       Abstract_State => S,
       Initializes => null
is
   pragma Elaborate_Body (No_Init);
   X : Integer;
end No_Init;
