package B with Abstract_State => State_A
is

   procedure P1 with Global => (Output => State_A);

   procedure P2 with Global => (In_Out => State_A);

   procedure P3 with Global => (In_Out => State_A);

   procedure P8 with Global => (In_Out => State_A);

private

   G : Boolean with Part_Of => State_A;

end B;
