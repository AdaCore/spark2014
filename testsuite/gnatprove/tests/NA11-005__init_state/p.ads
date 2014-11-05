package P with
  SPARK_Mode,
  Abstract_State => (State,
                     State2,
                     State3,
                     State4),
  Initializes => State2
is
   procedure PP with
     Global => (In_Out => State);

   procedure PP2 with
     Global => (Output => State3);

   procedure PP3;
end P;
