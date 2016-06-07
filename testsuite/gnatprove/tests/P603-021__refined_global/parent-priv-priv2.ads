private package Parent.Priv.Priv2 with
  Abstract_State => (State4 with Part_Of => Parent.Priv.State2)
is
   procedure P with Global => Parent.State1;
private
   X : Integer := 0 with Part_Of => State4;
end Parent.Priv.Priv2;
