with asm_abstract_state_refined_in_embedded_and_private_child_05.Source_B;

package body asm_abstract_state_refined_in_embedded_and_private_child_05
--# own State is Source_A.State,
--#              asm_abstract_state_refined_in_embedded_and_private_child_05.Source_B.State;
is

  --  Embedded package spec for Source_A
  package Source_A
  --# own State;        
  is
     procedure Read (Level : out Integer);
      --# global State;
      --# derives Level from State;
  end Source_A;

  --  Embedded package body for Source_A
  package body Source_A
  is
    State : Integer;

    procedure Read (Level : out Integer)
    is
    begin
      Level := State;
    end Read;
  end Source_A;

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
     Source_A. Read (Level_A);
     Source_B.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end asm_abstract_state_refined_in_embedded_and_private_child_05;
