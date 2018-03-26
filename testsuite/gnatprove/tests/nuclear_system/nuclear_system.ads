pragma Partition_Elaboration_Policy (Sequential);
pragma Profile (Ravenscar);

with Ada.Real_Time;
with Nuclear_Reactors; use Nuclear_Reactors;

package Nuclear_System with SPARK_Mode is
   package RT renames Ada.Real_Time;
   use type RT.Time;

   task Reaction_Monitor;

   type Nuclear_Reaction is (Stable, Uncontrolled);

   protected Safety_System is
      procedure Current_Status (Status : Nuclear_Reaction)
        with Global => (Input => RT.Clock_Time, In_Out => Nuclear_Reactors.State);
      entry Get_Deadline (Time : out RT.Time);
      procedure Timeout
         with Global => (Input => RT.Clock_Time, In_Out => Nuclear_Reactors.State);
   private
      Deadline : RT.Time := RT.Time_First;
      Timer_Active : Boolean := False;
   end Safety_System;

   task Timer
     with Global =>
       (Input  => RT.Clock_Time,
        In_Out => (Nuclear_Reactors.State, Safety_System));

end Nuclear_System;
