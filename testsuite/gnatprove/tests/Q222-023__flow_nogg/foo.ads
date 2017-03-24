package Foo
  with SPARK_Mode  => On,
    Abstract_State => State
is
   procedure Initialize
     with Global => (Output => State);

   pragma Assert (True);

end Foo;
