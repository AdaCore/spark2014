package Nuclear_Reactors with
  SPARK_Mode,
  Abstract_State => (State with Synchronous),
  Initializes    => State
is
   pragma Warnings (GNATprove, Off,
     "unused initial value of ""Cur_State"" constituent of ""State""",
     Reason => "The model of nuclear reactor does not read state");
   procedure Shut_Down
     with Global => (In_Out => State);

   pragma Warnings (GNATprove, Off,
     "unused initial value of ""Cur_State"" constituent of ""State""",
     Reason => "The model of nuclear reactor does not read state");
   procedure Emergency_Stop
     with Global => (In_Out => State);

end Nuclear_Reactors;
