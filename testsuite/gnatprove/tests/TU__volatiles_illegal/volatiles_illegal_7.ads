with System.Storage_Elements;

package Volatiles_Illegal_7
  with SPARK_Mode,
       Abstract_State => State
       --  TU: 1. A state abstraction that is not specified as External shall
       --  not have ``constituents`` which are External states.

       --  TU: 8. An External state abstraction is one declared with an
       --  ``option_list`` that includes the External ``option``
       --  (see :ref:`external_state`).
is
   pragma Elaborate_Body (Volatiles_Illegal_7);
end Volatiles_Illegal_7;
