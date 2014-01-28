with System.Storage_Elements;

package body Volatiles_Illegal_1
  with SPARK_Mode,
       Refined_State => (State  => Vol,  --  Aspect Async_Readers is NOT set
                                         --  for Vol while it is set for State.

                         State2 => Vol2) --  Aspect Async_Writers is set for
                                         --  Vol2 while it is NOT set for
                                         --  State2.
is
   Vol : Natural
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEAD0#);

   Vol2 : Natural
     with Volatile,
          Async_Readers,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#BEEF0#);
end Volatiles_Illegal_1;
