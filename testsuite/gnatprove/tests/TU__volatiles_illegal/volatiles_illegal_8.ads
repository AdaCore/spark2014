with System.Storage_Elements;

package Volatiles_Illegal_8
  with SPARK_Mode,
       Abstract_State => (State with External)
       --  TU: 2. An External state abstraction shall have at least one
       --  ``constituent`` that is External state, or shall have a null
       --  refinement.
is
   pragma Elaborate_Body (Volatiles_Illegal_8);
end Volatiles_Illegal_8;

