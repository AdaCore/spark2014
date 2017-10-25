package P
  with Abstract_State => State
is
   V : Integer := 3;
   procedure Foo;
private
   A : constant Integer := V; -- needs Part_Of
   B : constant Integer := V with Part_Of => State;
end;
