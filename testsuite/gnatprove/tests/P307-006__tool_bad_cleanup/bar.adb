with Foo;

package body Bar is

   procedure Test_01
   with Global => null
   is
   begin
      Foo.P;
   end Test_01;

end Bar;
