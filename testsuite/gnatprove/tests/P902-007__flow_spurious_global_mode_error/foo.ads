package Foo with
   Abstract_State => State
is

   procedure Test (S : String)
   with Pre    => S'Length > 0,
        Global => (Output => State);

end Foo;
