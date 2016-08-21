------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--           P O L Y O R B _ H I . B A C K G R O U N D _ T A S K            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--       Copyright (C) 2009 Telecom ParisTech, 2010-2015 ESA & ISAE.        --
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

package body PolyORB_HI.Background_Task is

   use PolyORB_HI.Errors;
   use PolyORB_HI.Output;
   use PolyORB_HI_Generated.Deployment;
   use PolyORB_HI.Suspenders;
   use Ada.Real_Time;

   --------------------------
   -- The_Background_Task --
   -------------------------

   task body The_Background_Task is
      Error : Error_Kind;

   begin
      --  Run the initialize entrypoint (if any)

      Activate_Entrypoint;

      --  Wait for the network initialization to be finished

      pragma Debug
        (Put_Line
         (Verbose,
          "Background Task "
          + Entity_Image (Entity)
          + ": Wait initialization"));

      Block_Task (Entity);
      delay until System_Startup_Time;

      pragma Debug (Put_Line
                    (Verbose,
                     "Background task initialized for entity "
                     + Entity_Image (Entity)));

      pragma Debug
        (Put_Line
         (Verbose,
          "Background Task "
            + Entity_Image (Entity)
            + ": Run job"));

      Error := Job;

      if Error /= Error_None then
         Recover_Entrypoint;
      end if;
   end The_Background_Task;

   -------------------
   -- Next_Deadline --
   -------------------

   function Next_Deadline return Ada.Real_Time.Time is
   begin
      return Ada.Real_Time.Clock;
   end Next_Deadline;

end PolyORB_HI.Background_Task;
