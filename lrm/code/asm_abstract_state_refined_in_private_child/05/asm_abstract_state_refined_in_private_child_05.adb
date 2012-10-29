with asm_abstract_state_refined_in_private_child_05.Source_A, asm_abstract_state_refined_in_private_child_05.Source_B;

package body asm_abstract_state_refined_in_private_child_05
--# own State is asm_abstract_state_refined_in_private_child_05.Source_A.State,
--#              asm_abstract_state_refined_in_private_child_05.Source_B.State;
is

  procedure Read_Power(Level : out Integer)
  --# global Source_A.State, Source_B.State;
  --# derives
  --#     Level
  --#     from
  --#         Source_A.State,
  --#         Source_B.State;
  is
     Level_A : Integer;
     Level_B : Integer;
  begin
     Source_A.Read (Level_A);
     Source_B.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end asm_abstract_state_refined_in_private_child_05;
