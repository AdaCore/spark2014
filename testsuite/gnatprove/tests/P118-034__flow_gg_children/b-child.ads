package B.Child with Abstract_State => State_B
is

   procedure P4 with Global => (In_Out => State_A);

   procedure P5 with Global => (In_Out => State_A);

   procedure P6 with Global => (Input  => State_A,
                                Output => State_B);

   procedure P7 with Global => (In_Out => State_A);

private

   H : Boolean with Part_Of => State_B;

end B.Child;
