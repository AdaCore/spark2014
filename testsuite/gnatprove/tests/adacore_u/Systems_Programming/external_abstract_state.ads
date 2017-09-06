package External_Abstract_State
  with SPARK_Mode,
       Abstract_State => ((AR_State with External),
                          (AW_State with External => (Async_Writers, Effective_Reads)))
is
   pragma Elaborate_Body;
end External_Abstract_State;
