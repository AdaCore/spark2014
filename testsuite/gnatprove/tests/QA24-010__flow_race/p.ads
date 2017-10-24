package P with Abstract_State => State, Initializes => State is

   procedure Flip with Global => (In_Out => State);

   task Insider; -- accesses State directly by its constituent

end;
