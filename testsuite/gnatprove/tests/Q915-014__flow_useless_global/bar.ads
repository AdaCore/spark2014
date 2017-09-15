with Foo;

package Bar is

   procedure P with Global => null;

   procedure Q with Global => (Input => Foo.State);  -- unreferenced global

   procedure R with Global => (Output => Foo.State); -- unreferenced global

   procedure S with Global => (In_Out => Foo.State); -- unreferenced global

end Bar;
