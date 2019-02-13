with Repro.B;

package body Repro
with Refined_State => (State => (Foo, Repro.B.BState))
is

   Foo : Byte := 42;

   -----------------------------------------------------------------------------

   function Get_Foo return Byte
   is (Foo);

end Repro;
