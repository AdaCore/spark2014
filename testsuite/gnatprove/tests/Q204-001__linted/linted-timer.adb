-- Copyright 2015,2016 Steven Stewart-Gallus
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
-- implied.  See the License for the specific language governing
-- permissions and limitations under the License.
with Linted.Channels;

package body Linted.Timer is
   package Real_Time renames Ada.Real_Time;

   type Command is record
      Time : Real_Time.Time := Real_Time.Time_First;
   end record;

   package Command_Channels is new Linted.Channels (Command);

   package body Worker with
        Refined_State =>
        (Reader => (My_Command_Channel),
         Writer => (Timer_Task))
   is
      task Timer_Task;
      My_Command_Channel : Command_Channels.Channel;

      procedure Wait_Until (Time : Real_Time.Time) is
      begin
         Command_Channels.Push (My_Command_Channel, (Time => Time));
      end Wait_Until;

      task body Timer_Task is
         use type Real_Time.Time;
         New_Command : Command;
      begin
         loop
            Command_Channels.Pop (My_Command_Channel, New_Command);
            declare
               Time : constant Real_Time.Time := New_Command.Time;
            begin
               delay until Time;
	       On_Tick;
            end;
         end loop;
      end Timer_Task;
   end Worker;
end Linted.Timer;
