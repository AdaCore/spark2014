--# inherit asm_abstract_state_refined_in_embedded_and_private_child_05;
private package asm_abstract_state_refined_in_embedded_and_private_child_05.Source_B
--# own State;
is
   procedure Read (Level : out Integer);
   --# global State;
   --# derives Level from State;
end asm_abstract_state_refined_in_embedded_and_private_child_05.Source_B;
