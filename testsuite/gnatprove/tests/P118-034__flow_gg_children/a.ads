package A with Abstract_State => State_A
is

   procedure P1;

   procedure P2;

   procedure P3;

   procedure P8;

private

   G : Boolean with Part_Of => State_A;

end A;
