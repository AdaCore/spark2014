with Volatiles_Illegal_Helper; pragma Elaborate (Volatiles_Illegal_Helper);
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
   --  TU: 7. An effectively volatile object shall not be used as an
   --  actual parameter in a generic instantiation.

   function F return Boolean
     with Global => Vol;
   --  TU: 8. A ``global_item`` of a nonvolatile function, or of a function
   --  which is nonvolatile for internal calls, shall not denote either an
   --  effectively volatile object or an external state abstraction.

   function F2 (Par : Vol_T) return Boolean;
   --  TU: 9. A formal parameter (or result) of a nonvolatile function, or of a
   --  function which is nonvolatile for internal calls, shall not be of an
   --  effectively volatile type. [For a protected function, this rule does not
   --  apply to the notional parameter denoting the current instance of the
   --  associated protected unit described in section :ref:`global-aspects`.]
end Volatiles_Illegal_3;
