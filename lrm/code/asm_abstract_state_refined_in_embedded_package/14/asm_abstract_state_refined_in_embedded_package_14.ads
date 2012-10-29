-- Use of embedded packages to encapsulate state
package asm_abstract_state_refined_in_embedded_package_14
with
   Abstract_State => State;
is
   procedure Read_Power(Level : out Integer);
   with
      Global  => State,
      Depends => (Level => State);
end asm_abstract_state_refined_in_embedded_package_14;
