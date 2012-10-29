private package asm_abstract_state_refined_in_private_child_14.Source_A
with
   Abstract_State => State;
is
   procedure Read (Level : out Integer);
   with
      Global => State,
      Depends => (Level => State);
end asm_abstract_state_refined_in_private_child_14.Source_A;
