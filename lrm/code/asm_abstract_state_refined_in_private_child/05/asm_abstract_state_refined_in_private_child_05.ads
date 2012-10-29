-- Use of child packages to encapsulate state
package asm_abstract_state_refined_in_private_child_05
--# own State;
is
   procedure Read_Power(Level : out Integer);
   --# global State;
   --# derives Level from State;
end asm_abstract_state_refined_in_private_child_05;
