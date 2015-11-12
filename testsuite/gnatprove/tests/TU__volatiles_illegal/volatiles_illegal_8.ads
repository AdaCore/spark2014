package Volatiles_Illegal_8
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers)
       --  TU: 2. An External state abstraction shall have each of the
       --  properties set to True which are True for any of its
       --  ``constituents``.
is
   pragma Elaborate_Body (Volatiles_Illegal_8);
end Volatiles_Illegal_8;
