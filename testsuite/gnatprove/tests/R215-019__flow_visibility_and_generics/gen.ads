generic
package Gen
  with Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Foo_Ghost
is
   function Foo_Ghost return Boolean
     with Ghost,
          Global => State;

   procedure Proc
     with Global => (In_Out => State),
          Post   => Foo_Ghost;

end Gen;
