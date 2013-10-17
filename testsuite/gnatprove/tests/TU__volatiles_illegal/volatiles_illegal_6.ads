with System.Storage_Elements;

package Volatiles_Illegal_6
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Readers)
       --  TU: 3. An External state abstraction shall have each of the
       --  properties set to True which are True for any of its
       --  ``constituents``.
is
   pragma Elaborate_Body (Volatiles_Illegal_6);
end Volatiles_Illegal_6;
