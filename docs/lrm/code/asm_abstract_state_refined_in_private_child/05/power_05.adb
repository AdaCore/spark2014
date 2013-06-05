with Power_05.Source_A_05, Power_05.Source_B_05;

package body Power_05
--# own State is Power_05.Source_A_05.State,
--#              Power_05.Source_B_05.State;
is

  procedure Read_Power(Level : out Integer)
  --# global Source_A_05.State, Source_B_05.State;
  --# derives
  --#     Level
  --#     from
  --#         Source_A_05.State,
  --#         Source_B_05.State;
  is
     Level_A : Integer;
     Level_B : Integer;
  begin
     Source_A_05.Read (Level_A);
     Source_B_05.Read (Level_B);
     Level := Level_A + Level_B;
  end Read_Power;

end Power_05;
