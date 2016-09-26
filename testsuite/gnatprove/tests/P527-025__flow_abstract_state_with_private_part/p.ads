package P with
   Elaborate_Body,
   Abstract_State => (State)
is

private
   X : Integer := 0 with Part_Of => State;
end P;
