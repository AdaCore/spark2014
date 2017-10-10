package Foo with Abstract_State => (S with External => (Async_Readers,
                                                        Async_Writers)),
                 Elaborate_Body
is

   procedure Set (X : Boolean)
   with Global => (Output => S);

   procedure Get (X : out Boolean)
   with Global => (Input => S);

end Foo;
