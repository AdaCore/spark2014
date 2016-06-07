private package Parent.Priv with
  Abstract_State => (State2 with Part_Of => Parent.State1)
is
   procedure P with Global => Parent.State1;
private
   X : Integer := 0 with Part_Of => State2;
end Parent.Priv;
