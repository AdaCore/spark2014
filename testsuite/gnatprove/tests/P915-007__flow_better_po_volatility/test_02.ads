--  In this test we have a po that is too volatile for the given spec here.

package Test_02 with
   Abstract_State => (State with External => (Async_Readers, Async_Writers)),
   Initializes    => State
is

   function Get_Reading return Integer
   with Volatile_Function,
        Global => State;

end Test_02;
