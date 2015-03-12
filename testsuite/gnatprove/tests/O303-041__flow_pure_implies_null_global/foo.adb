with Ada.Numerics.Generic_Elementary_Functions;

package body Foo
is

   package FF is new Ada.Numerics.Generic_Elementary_Functions (Float);
   use FF;

   procedure Test_01 (N : in out Float)
   is
   begin
      N := Log (N);
   end Test_01;

end Foo;
