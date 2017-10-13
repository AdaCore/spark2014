with Types;
package body P
  with Refined_State => (State => Refined)
is
   Refined : Types.T;

   procedure Foo is null;
end;
