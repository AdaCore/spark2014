with System.Storage_Elements;

package body Volatiles_Illegal_1
  with SPARK_Mode,
       Refined_State => (State => Vol)  --  Aspect Async_Writers is set
                                        --  for Vol while it is not set
                                        --  for State1.

is
   Vol : Natural
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEAD0#);
end Volatiles_Illegal_1;
