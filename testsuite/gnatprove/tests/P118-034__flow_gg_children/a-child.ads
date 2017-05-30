package A.Child with Abstract_State => State_B
is

   procedure P4;

   procedure P5;

   procedure P6;

   procedure P7;

private

   H : Boolean with Part_Of => State_B;

end A.Child;
