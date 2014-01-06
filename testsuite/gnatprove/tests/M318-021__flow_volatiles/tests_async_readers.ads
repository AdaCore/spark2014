package Tests_Async_Readers
  with Abstract_State => (State_With_Async_Readers
                          with External => (Async_Readers, Effective_Writes))
is
   pragma Elaborate_Body;
end Tests_Async_Readers;
