package P
  with Abstract_State => (State_A, State_B)
is

   procedure Proc (X : Integer;
                   Y : Integer)
     with Depends => (State_A => X,
                      State_B => X,
                      null    => Y);

end P;
