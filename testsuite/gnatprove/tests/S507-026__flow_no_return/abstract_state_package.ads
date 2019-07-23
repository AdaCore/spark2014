package abstract_state_package
with Abstract_State => ( some_state with External => ( Async_Readers, Effective_Writes ) )
is

   procedure state_change with Global => ( Output => some_state ),
     Inline_Always;

end abstract_state_package;
