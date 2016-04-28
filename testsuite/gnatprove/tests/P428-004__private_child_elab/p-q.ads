private package P.Q with
  Abstract_State => (State with Part_Of => P.State),
  Initializes => (State, X)
is
   X : Boolean := True with Part_Of => P.State;
   procedure Dummy with Global => null;
end P.Q;
