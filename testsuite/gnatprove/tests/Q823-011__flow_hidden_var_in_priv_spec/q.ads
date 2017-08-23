package Q with Abstract_State => State
is
   procedure Dummy;

private
   B : Integer with Part_Of => State;
end;
