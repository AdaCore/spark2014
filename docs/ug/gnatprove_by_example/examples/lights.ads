package Lights
  with SPARK_Mode,
       Abstract_State => (State with External)
is

   procedure Init
     with Global => (Output => State),
          Depends => (State => null);

   procedure Toggle
     with Global => (In_Out => State),
          Depends => (State => State);

   procedure Explode
     with Global => (Output => State),
          No_Return;

end Lights;
