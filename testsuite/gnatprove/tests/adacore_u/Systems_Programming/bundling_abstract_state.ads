package Bundling_Abstract_State
  with SPARK_Mode,
       Abstract_State => (State with External),
       Initializes => State
is
   pragma Elaborate_Body;
end Bundling_Abstract_State;
