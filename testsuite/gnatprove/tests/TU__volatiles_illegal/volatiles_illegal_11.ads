with System.Storage_Elements;

package Volatiles_Illegal_11
  with SPARK_Mode,
       Abstract_State => (State with External)
  --  TU: 1. If an external state is declared without any of the external
  --  properties specified then all of the properties default to a value
  --  of True.
is
   procedure Proc
     with Global => (Input => State);
   --  State has Effective_Reads set to True, so it cannot be a
   --  Global Input parameter.
end Volatiles_Illegal_11;
