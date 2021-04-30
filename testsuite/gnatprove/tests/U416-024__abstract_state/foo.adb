with Interfaces;

package body Foo
with
   SPARK_Mode => On,
   Refined_State => (State => Instance)
is

   -------------------------------------------------------------------------

   function Get return Bar_Type
   is (Instance);

   -------------------------------------------------------------------------

   procedure Set (Value : Bar_Type)
   is
   begin
      Instance := Instance + Value;
   end Set;

end Foo;
