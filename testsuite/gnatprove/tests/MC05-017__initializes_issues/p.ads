package P
   with Abstract_State => S,
        Initializes => (S, V)
is
   V : Integer := 0;
end P;
