package A with
  Abstract_State =>
    (State,
     (Ext_State with External => (Async_Readers, Async_Writers)))
is

   procedure Test_01;
   procedure Test_02;

end A;
