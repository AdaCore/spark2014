------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--             P O L Y O R B _ H I . S P O R A D I C _ T A S K              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2015 ESA & ISAE.      --
--                                                                          --
-- PolyORB-HI is free software; you can redistribute it and/or modify under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. PolyORB-HI is distributed in the hope that it will be useful, but  --
-- WITHOUT ANY WARRANTY; without even the implied warranty of               --
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
--              PolyORB-HI/Ada is maintained by the TASTE project           --
--                      (taste-users@lists.tuxfamily.org)                   --
--                                                                          --
------------------------------------------------------------------------------

with PolyORB_HI.Output;
with PolyORB_HI.Suspenders;

package body PolyORB_HI.Sporadic_Task is

   use Ada.Real_Time;
   use PolyORB_HI.Errors;
   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Suspenders;

   Next_Deadline_Val : Time;

   -----------------------
   -- The_Sporadic_Task --
   -----------------------

   task body The_Sporadic_Task is
      Port       : Port_Type;
      Next_Start : Time;
      Error : Error_Kind;

   begin
      --  Run the initialize entrypoint (if any)

      Activate_Entrypoint;

      --  Wait for the network initialization to be finished

      pragma Debug
        (Put_Line
         (Verbose,
          "Sporadic Task "
          + Entity_Image (Entity)
          + ": Wait initialization"));

      Block_Task (Entity);
      delay until System_Startup_Time;

      pragma Debug (Put_Line
                    (Verbose,
                     "Sporadic task initialized for entity "
                     + Entity_Image (Entity)));


      --  Main task loop

      loop
         pragma Debug
           (Put_Line
            (Verbose,
             "Sporadic Task "
             + Entity_Image (Entity)
             + ": New Dispatch"));

         --  Block until an event is received

         Wait_For_Incoming_Events (Entity, Port);

         pragma Debug
           (Put_Line
            (Verbose,
             "Sporadic Task "
             + Entity_Image (Entity)
             + ": received event"));

         --  Calculate the next start time according to the minimal
         --  inter-arrival time.

         Next_Start        := Ada.Real_Time.Clock + Task_Period;
         Next_Deadline_Val := Ada.Real_Time.Clock + Task_Deadline;

         --  Execute the job

         Error := Job (Port);

         if Error /= Error_None then
            Recover_Entrypoint;
         end if;

         --  Sleep to guarantee at least the minimal inter-arrival
         --  time elapses.

         delay until Next_Start;
      end loop;
   end The_Sporadic_Task;

   -------------------
   -- Next_Deadline --
   -------------------

   function Next_Deadline return Ada.Real_Time.Time is
   begin
      return Next_Deadline_Val;
   end Next_Deadline;

end PolyORB_HI.Sporadic_Task;
