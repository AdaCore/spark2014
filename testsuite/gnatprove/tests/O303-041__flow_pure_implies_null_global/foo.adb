with Ada.Numerics.Generic_Elementary_Functions;

procedure Foo (N : in out Float) is

   package FF is new Ada.Numerics.Generic_Elementary_Functions (Float);
   use FF;

begin
   N := Log (N);
end Foo;
