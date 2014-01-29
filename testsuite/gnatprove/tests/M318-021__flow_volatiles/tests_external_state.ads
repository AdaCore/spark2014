package Tests_External_State
  with SPARK_Mode,
       Abstract_State => (State with External)
is
   procedure Set (X : Integer)
     with Global  => (Output => State),
          Depends => (State => X);

   procedure Get (X : out Integer)
     with Global  => (In_Out => State),
          Depends => ((X, State) => State);
end Tests_External_State;
