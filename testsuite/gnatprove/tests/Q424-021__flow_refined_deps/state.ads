pragma SPARK_Mode;

with Foo;

package State with
  Ghost,
  Abstract_State => State,
  Initializes => State
is

   procedure Test
     with Ghost,
     Global => (In_Out => State,
                Input => Foo.F),
     Depends => (State =>+ Foo.F);
private

   S : Integer := 0
     with Part_Of => State;

end State;
