package P with Abstract_State => State, Initializes => State is

   generic
   procedure Flip with Global => (In_Out => State);
   --  This routine can be instantiated outside of this package,
   --  but its body will still see the refinement of State.

end;
