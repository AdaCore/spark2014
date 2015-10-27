with Ada.Text_IO;   use Ada.Text_IO;
with Ada.Real_Time;

use type Ada.Real_Time.Time;

pragma Warnings (Off, "assuming * has no effect on global items");

--  TU: 2. Task and protected units are in |SPARK|, but their use requires the
--  Ravenscar Profile. [In other words, a task or protected unit is not in
--  |SPARK| if the Ravenscar profile does not apply to the enclosing
--  compilation unit.] Similarly, the use of task or protected units also
--  requires a Partition_Elaboration_Policy of Sequential. [This is to prevent
--  data races during library unit elaboration.]  Similarly, the use of any
--  subprogram which references the predefined state abstraction
--  Ada.Task_Identification.Tasking_State (described below) as a global
--  requires the Ravenscar Profile.

procedure T is
   Release_Time : Ada.Real_Time.Time;
   Period       : constant Ada.Real_Time.Time_Span := Ada.Real_Time.Seconds (1);
begin

   Put_Line("This is in the main program.");

   declare
      task First_Task;
      task Second_Task;
      task Third_Task;

      task body First_Task is
      begin
         for Index in 1..4 loop
            Release_Time := Ada.Real_Time.Clock + Period;
            delay until Release_Time;
            Put_Line("This is in First_Task.");
         end loop;
      end First_Task;

      task body Second_Task is
      begin
         for Index in 1..4 loop
            Release_Time := Ada.Real_Time.Clock + Period;
            delay until Release_Time;
            Put_Line("This is in Second_Task.");
         end loop;
      end Second_Task;

      task body Third_Task is
      begin
         for Index in 1..8 loop
            Release_Time := Ada.Real_Time.Clock + Period;
            delay until Release_Time;
            Put_Line("This is in Third_Task.");
         end loop;
      end Third_Task;
   begin
      Release_Time := Ada.Real_Time.Clock + Period;
      delay until Release_Time;
      Put_Line("This is in the block body.");
      Release_Time := Ada.Real_Time.Clock + Period;
      delay until Release_Time;
      Put_Line("This is also in the block body.");
   end; -- of declare

   Put_Line("This is at the end of the main program.");

end T;
