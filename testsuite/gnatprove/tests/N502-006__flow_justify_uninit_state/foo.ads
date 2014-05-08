package Foo
  with Abstract_State => State
is
   procedure Init
   with
      Global => (Output => State);
end Foo;
