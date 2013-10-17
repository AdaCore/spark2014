with System.Storage_Elements;

package Volatiles_Illegal_1
  with SPARK_Mode,
       Abstract_State => (State with External => (Async_Readers,
                                                  Async_Writers => True))
       --  TU: 2. If just the name of the property is given then its value
       --  defaults to True [; for instance Async_Readers defaults to
       --  Async_Readers => True].

       --  TU: 4. If any one property is explicitly defined, all undefined
       --  properties default to a value of False.
is
   pragma Elaborate_Body (Volatiles_Illegal_1);
end Volatiles_Illegal_1;
