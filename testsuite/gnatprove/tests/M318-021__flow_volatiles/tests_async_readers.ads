package Tests_Async_Readers
   with Abstract_State => (State_With_Async_Readers with External => Async_Readers)
is
   pragma Elaborate_Body (Tests_Async_Readers);
end Tests_Async_Readers;
