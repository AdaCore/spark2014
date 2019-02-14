with Repro.B;

package body Repro
with Refined_State => (State => (Foo, B.State))
is

   pragma Warnings (Off, "* is not modified, could be declared constant");

   Foo : Byte := 42;

   pragma Warnings (On, "* is not modified, could be declared constant");

   -----------------------------------------------------------------------------

   function Condition return Boolean
   is (Foo = 42);

   -----------------------------------------------------------------------------

   function Get_Foo return Byte
   is (Foo);

end Repro;
