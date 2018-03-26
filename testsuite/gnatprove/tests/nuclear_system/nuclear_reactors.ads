package Nuclear_Reactors with
  SPARK_Mode,
  Abstract_State => (State with Synchronous),
  Initializes    => State
is
   procedure Shut_Down
     with Global => (In_Out => State);
   pragma Annotate (GNATprove, Intentional, "global Input .* not read",
                    "The model of nuclear reactor does not read state");

   procedure Emergency_Stop
     with Global => (In_Out => State);
   pragma Annotate (GNATprove, Intentional, "global Input .* not read",
                    "The model of nuclear reactor does not read state");
end Nuclear_Reactors;
