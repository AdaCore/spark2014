package P with Abstract_State => State, Initializes => State is
   procedure Flip with Global => (In_Out => State);
private
   X : Boolean := True with Part_Of => State;
end;
