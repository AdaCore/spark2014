package Bad_Refinement
  with Abstract_State => (State, State2),
       Initializes    => (State, State2)
is
   procedure Liar (I : out Integer)
     with Global => State;

   procedure Liar2 (I : out Integer)
     with Global => State2;

   procedure Liar3 (I : out Integer)
     with Global => State;

   function Liar4 return Integer
     with Depends => (Liar4'Result => State);

   procedure Liar5 (I : out Integer)
     with Depends => (I      => State,
                      State2 => State);

   procedure Liar6 (I, J : out Integer)
     with Global  => State,
          Depends => ((I, J) => State);

   procedure Liar7 (I, J : out Integer)
     with Depends => ((I, J) => State);

   procedure Liar8
     with Global  => (Input  => State2,
                      Output => State),
          Depends => (State  => State2);

   procedure Liar9 (I : out Integer)
     with Depends => (I      => State2,
                      State2 => null);
end Bad_Refinement;
