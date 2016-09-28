with Ada.Numerics.Elementary_Functions;

procedure Foo (N : in out Float) is

   use Ada.Numerics.Elementary_Functions;

begin
   N := Log (N);
end Foo;
