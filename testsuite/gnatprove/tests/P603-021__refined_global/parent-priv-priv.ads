private package Parent.Priv.Priv with
  Abstract_State => (State3 with Part_Of => Parent.Priv.State2)
is
   procedure P with Global => Parent.State1;
private
   X : Integer := 0 with Part_Of => State3;
end Parent.Priv.Priv;
