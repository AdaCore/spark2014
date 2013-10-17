with System.Storage_Elements;

package body Volatiles_Illegal_6
  with SPARK_Mode,
       Refined_State => (State => Vol)  --  Aspect Effective_Writes is set
                                        --  for Vol while it is not set
                                        --  for State.
is
   Vol : Natural
     with Volatile,
          Async_Readers,
          Effective_Writes,
          Address => System.Storage_Elements.To_Address (16#B0D1E50#);
end Volatiles_Illegal_6;
