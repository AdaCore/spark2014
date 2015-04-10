with Power_14.Source_A_14,
     Power_14.Source_B_14;

package body Power_14
  with SPARK_Mode,
       Refined_State => (State => (Power_14.Source_A_14.State,
                                   Power_14.Source_B_14.State))
is
   procedure Read_Power(Level : out Integer)
     with Refined_Global  => (Source_A_14.State, Source_B_14.State),
          Refined_Depends => (Level => (Source_A_14.State,
                                        Source_B_14.State))
   is
      Level_A : Integer;
      Level_B : Integer;
   begin
      Source_A_14.Read (Level_A);
      Source_B_14.Read (Level_B);
      Level := Level_A + Level_B;
   end Read_Power;
end Power_14;
