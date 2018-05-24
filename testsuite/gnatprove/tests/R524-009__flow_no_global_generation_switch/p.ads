package P with Abstract_State => State is
   procedure Initialize
     with Global => (Output => State);

end P;
