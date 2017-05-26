package Parent
   with Abstract_State => (Foo, State)
is
   pragma Elaborate_Body;
end Parent;
