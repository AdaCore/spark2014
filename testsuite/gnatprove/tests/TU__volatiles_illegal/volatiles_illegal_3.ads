with Volatiles_Illegal_Helper;
with System.Storage_Elements;

package Volatiles_Illegal_3
  with SPARK_Mode
is
   type Vol_T is new Natural with Volatile;

   Vol : Natural
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#BBC0#);

   Vol2 : Natural
     with Volatile,
          Async_Writers,
          Effective_Reads,
          Address => System.Storage_Elements.To_Address (16#CAB0#);

   package P is new Volatiles_Illegal_Helper.Gen (Size => Vol);
   --  TU: 8. A Volatile object shall not be used as an actual parameter in a
   --  generic instantiation.

   function F return Boolean
     with Global => Vol;
   --  TU: 9. A Volatile object shall not be a ``global_item`` of a function.

   function F2 (Par : Vol_T) return Boolean;
   --  TU: 10. A function shall not have a formal parameter of a Volatile type.
end Volatiles_Illegal_3;
