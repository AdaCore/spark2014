private package Parent.Child
   with Abstract_State => (Child_State with Part_Of => State)
is
   procedure P
      with Global => (Output => (Child_State));
end Parent.Child;
