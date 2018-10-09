private package P.Child
  with Abstract_State => (C with Part_Of => P.State2),
       Initializes => C
is
   procedure Proc
     with Global => (Output => C);
end P.Child;
