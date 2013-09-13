package Test
with SPARK_Mode,
     Abstract_State => State, Initializes => State
is

   procedure Procedure_With_Refinement (X : Integer;
                                        Y : out Integer)
   with Global => (In_Out => State),
        Depends => (State => (State, X),
                    Y     => State);

end Test;
