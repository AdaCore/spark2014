package P
with Abstract_State => S,
     Initializes => (S, V),
     Elaborate_Body
is
   V : Integer := 0;
end P;
