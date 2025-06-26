with External;

package Test2
with
   Abstract_State => State,
   Initializes => (State => External.State)
is

   procedure Update;

end Test2;
