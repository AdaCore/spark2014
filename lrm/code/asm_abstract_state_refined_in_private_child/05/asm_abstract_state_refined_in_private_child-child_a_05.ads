--# inherit asm_abstract_state_refined_in_private_child_05;
private package asm_abstract_state_refined_in_private_child_05.Source_A
--# own State;
is
   procedure Read (Level : out Integer);
   --# global State;
   --# derives Level from State;
end asm_abstract_state_refined_in_private_child_05.Source_A;
