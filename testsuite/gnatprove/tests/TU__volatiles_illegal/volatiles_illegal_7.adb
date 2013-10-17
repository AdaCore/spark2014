with System.Storage_Elements;

package body Volatiles_Illegal_7
  with SPARK_Mode,
       Refined_State => (State => Vol)  --  State was not declared as
                                        --  External.
is
   Vol : Natural
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address (16#A12E0#);
end Volatiles_Illegal_7;
