private package Foo.Bar with
   Abstract_State => (State with Part_Of => Foo.State)
is

   procedure Write (B : Boolean)
   with Global => (Output => State);

end Foo.Bar;
