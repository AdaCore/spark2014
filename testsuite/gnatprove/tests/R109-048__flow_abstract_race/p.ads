package P with Abstract_State => (Solid_State, (Task_State with External)) is
   procedure Flip with Global => (In_Out => Solid_State);
end;
