with External;

package Test
with
   Abstract_State => State,
   Initializes => (State => External.State)
is

   procedure Update;

end Test;
