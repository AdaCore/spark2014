-- Use of child packages to encapsulate state
package asm_abstract_state_refined_in_private_child_14
with
   Abstract_State => State;
is
   procedure Read_Power(Level : out Integer);
   with
      Global  => State,
      Depends => (Level => State);
end asm_abstract_state_refined_in_private_child_14;
