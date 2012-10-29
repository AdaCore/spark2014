package body asm_abstract_state_refined_in_private_child_05.Source_A
is
   State : Integer;

   procedure Read (Level : out Integer)
   is
   begin
      Level := State;
   end Read;
end asm_abstract_state_refined_in_private_child_05.Source_A;
