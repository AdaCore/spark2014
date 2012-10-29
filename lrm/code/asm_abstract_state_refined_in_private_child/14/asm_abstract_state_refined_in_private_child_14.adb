with asm_abstract_state_refined_in_private_child_14.Source_A, asm_abstract_state_refined_in_private_child_14.Source_B;

package body asm_abstract_state_refined_in_private_child_14
with
   Refined_State => (State => (Power.Source_A.State, Power.Source_B.State));
is

  procedure Read_Power(Level : out Integer)
  with
     Global => (Source_A.State, Source_B.State),
     Depends => (Level => (Source_A.State, Source_B.State));
  is
     Level_A : Integer;
     Level_B : Integer;
  begin
     Source_A. Read (Level_A);
     Source_B.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end asm_abstract_state_refined_in_private_child_14;
