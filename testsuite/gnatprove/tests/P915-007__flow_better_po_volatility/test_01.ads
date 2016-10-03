--  This should be correct.

package Test_01 with
   Abstract_State => (State with External => (Async_Readers, Async_Writers)),
   Initializes    => State
is

   function Get_Reading return Integer
   with Volatile_Function,
        Global => State;

end Test_01;
