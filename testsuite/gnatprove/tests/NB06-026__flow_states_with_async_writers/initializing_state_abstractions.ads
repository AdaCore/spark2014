package Initializing_State_Abstractions with
  Abstract_State => ((State_A with External => Async_Writers),
                     State_B),
  Initializes    => State_B
is
   pragma Elaborate_Body;
end Initializing_State_Abstractions;
