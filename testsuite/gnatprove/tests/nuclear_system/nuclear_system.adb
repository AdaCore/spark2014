with External_Model;

package body Nuclear_System with SPARK_Mode is

   task body Reaction_Monitor is
   begin
      loop
         delay until External_Model.Random_Wait;
         Safety_System.Current_Status (Stable);
      end loop;
   end Reaction_Monitor;

   task body Timer is
      Deadline : RT.Time;
   begin
      loop
         Safety_System.Get_Deadline (Deadline);
         delay until Deadline;
         Safety_System.Timeout;
      end loop;
   end Timer;

   protected body Safety_System is
      procedure Current_Status (Status : Nuclear_Reaction) is
         Current_Time : RT.Time := RT.Clock;
      begin
         Deadline := Current_Time + RT.Seconds (2);
         Timer_Active := True;
         case Status is
            when Stable =>
               null;
            when Uncontrolled =>
               Nuclear_Reactors.Shut_Down;
         end case;
      end Current_Status;

      entry Get_Deadline (Time : out RT.Time) when Timer_Active is
      begin
         Time := Deadline;
      end Get_Deadline;

      procedure Timeout is
         Current_Time : RT.Time := RT.Clock;
      begin
         if Current_Time >= Deadline then
            Timer_Active := False;
            Nuclear_Reactors.Emergency_Stop;
         end if;
      end Timeout;
   end Safety_System;
end Nuclear_System;
