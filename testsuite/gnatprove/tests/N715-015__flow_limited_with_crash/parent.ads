limited with Parent.Child_1;

package Parent
with Abstract_State => State
is
   pragma SPARK_Mode;

   procedure Initialise
     with Global => (Output => (State,
                                Parent.Child_1.State));

end Parent;
