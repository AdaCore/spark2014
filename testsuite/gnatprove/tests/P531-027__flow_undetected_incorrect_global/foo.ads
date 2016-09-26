package Foo
with SPARK_Mode,
     Abstract_State => (State,
                        (Atomics_State with External))
is

   procedure Update
      with Global => (In_Out => (State,
                                 Atomics_State));

   function read return Integer with Global => State;

end Foo;
