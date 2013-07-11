package Tests_Async_Readers
   with Abstract_State => State With_Async_Readers
-- When implemented the syntax will be:
-- with Abstract_State => (State with External => Async_Readers)
is
   pragma Elaborate_Body (Tests_Async_Readers);
end Tests_Async_Readers;
