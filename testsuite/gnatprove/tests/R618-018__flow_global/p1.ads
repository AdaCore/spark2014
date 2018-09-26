package P1 with
  Abstract_State => (S1, Dummy),
  Initializes => (S1, Dummy)
is
private
   function F1 return Integer with Global => Dummy;
end;
