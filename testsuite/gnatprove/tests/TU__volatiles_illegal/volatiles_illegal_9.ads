with System.Storage_Elements;

package Volatiles_Illegal_9
  with SPARK_Mode
is
   pragma Elaborate_Body (Volatiles_Illegal_9);

   A : Integer;

   Vol : Integer
     with Volatile,
          Async_Readers,
          Async_Writers,
          Effective_Reads,
          Address => System.Storage_Elements.To_Address (16#A110#);
end Volatiles_Illegal_9;
