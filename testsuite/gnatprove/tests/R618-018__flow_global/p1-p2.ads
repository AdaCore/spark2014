private package P1.P2 with
  Abstract_State => (S2 with Part_Of => S1),
  Initializes => S2
is
   function F2 return Integer with Global => S2;
end;
