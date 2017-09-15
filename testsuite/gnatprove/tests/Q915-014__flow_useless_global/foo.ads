package Foo
  with Abstract_State => State, Initializes => State
is

   procedure Stuff with Global => null;

end Foo;
