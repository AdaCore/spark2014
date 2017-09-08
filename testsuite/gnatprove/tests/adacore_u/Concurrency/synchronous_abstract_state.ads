package Synchronous_Abstract_State with
  SPARK_Mode,
  Abstract_State => (State with Synchronous, External => (Async_Readers, Async_Writers))
is
   pragma Elaborate_Body;
end Synchronous_Abstract_State;
