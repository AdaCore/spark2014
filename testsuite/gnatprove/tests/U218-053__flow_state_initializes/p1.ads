package P1 with Abstract_State => State1, Initializes => State1 is
   procedure Flip1 with Global => (In_Out => State1);
end;
