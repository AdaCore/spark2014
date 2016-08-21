------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                  P O L Y O R B _ H I . I S R _ T A S K                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                   Copyright (C) 2013-2015 ESA & ISAE.                    --
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

with Ada.Synchronous_Task_Control;

with PolyORB_HI.Output;
with PolyORB_HI.Suspenders;

package body PolyORB_HI.ISR_Task is

   use PolyORB_HI.Errors;
   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Suspenders;
   use Ada.Real_Time;
   use Ada.Synchronous_Task_Control;

   -------------
   -- Handler --
   -------------

   protected body Handler is

      ----------
      -- Wait --
      ----------

      entry Wait when ISR_Pending is
      begin
         ISR_Pending := False;
      end Wait;

      ------------
      -- Handle --
      ------------

      procedure Handle is
      begin
         ISR_Pending := True;
      end Handle;

   end Handler;

   Next_Deadline_Val : Time;

   ------------------
   -- The_ISR_Task --
   ------------------

   task body The_ISR_Task is
      Next_Start : Time;
      Error : Error_Kind;

   begin
      --  Run the initialize entrypoint (if any)

      Activate_Entrypoint;

      --  Wait for the network initialization to be finished

      pragma Debug
        (Put_Line
         (Verbose,
          "ISR Task "
          & Entity_Image (Entity)
          & ": Wait initialization"));

      Suspend_Until_True (Task_Suspension_Objects (Entity));
      --      delay until System_Startup_Time;

      pragma Debug (Put_Line
                    (Verbose,
                     "ISR task initialized for entity "
                     & Entity_Image (Entity)));


      --  Main task loop

      loop
         pragma Debug
           (Put_Line
            (Verbose,
             "ISR Task "
             & Entity_Image (Entity)
             & ": New Dispatch"));

         --  Block until an event is received

         Handler.Wait;

         pragma Debug
           (Put_Line
            (Verbose,
             "ISR Task "
             & Entity_Image (Entity)
             & ": received event"));

         --  Calculate the next start time according to the minimal
         --  inter-arrival time.

         Next_Start        := Ada.Real_Time.Clock + Task_Period;
         Next_Deadline_Val := Ada.Real_Time.Clock + Task_Deadline;

         --  Execute the job

         Error := Job;

         if Error /= Error_None then
            Recover_Entrypoint;
         end if;

         --  Sleep to guarantee at least the minimal inter-arrival
         --  time elapses.

         delay until Next_Start;
      end loop;
   end The_ISR_Task;

   -------------------
   -- Next_Deadline --
   -------------------

   function Next_Deadline return Ada.Real_Time.Time is
   begin
      return Next_Deadline_Val;
   end Next_Deadline;

end PolyORB_HI.ISR_Task;
