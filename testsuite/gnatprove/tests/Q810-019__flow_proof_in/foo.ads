with Bar;

package Foo
with
   SPARK_Mode => On,
   Abstract_State => State,
   Initializes    => State
is

   procedure Process (Value : Natural)
   with
      Global => (Output  => State,
                 --Input    => Bar.ID); -- 17.2 required Input
                 Proof_In => Bar.ID);   -- but Proof_In is correct

end Foo;
