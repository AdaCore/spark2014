package A with
   Abstract_State => State_A
is

   procedure P_1 (X : out Integer);

   function F_1 return Integer;

   function F_2 return Integer is (F_1);

   function F_3 return Integer;

   function F_4 return Integer is (F_3);

private

   G : Integer with Part_Of => State_A;

   function F_3 return Integer is (G);

end A;
