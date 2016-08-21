------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--        P O L Y O R B _ H I . H Y B R I D _ T A S K _ D R I V E R         --
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

with PolyORB_HI.Utils;
with PolyORB_HI.Output;
with PolyORB_HI.Port_Type_Marshallers;
with PolyORB_HI.Messages;
with PolyORB_HI.Suspenders;

package body PolyORB_HI.Hybrid_Task_Driver is

   package body Driver is
      use PolyORB_HI.Utils;
      use PolyORB_HI.Output;
      use PolyORB_HI_Generated.Deployment;
      use Ada.Real_Time;
      use PolyORB_HI.Streams;
      use Ada.Synchronous_Task_Control;
      use PolyORB_HI.Port_Type_Marshallers;
      use PolyORB_HI.Messages;
      use PolyORB_HI.Suspenders;

      procedure Trigger (T : Hybrid_Task_Info);
      --  Sends an event to the Period ports of task T.The_Task

      -------------
      -- Trigger --
      -------------

      procedure Trigger (T : Hybrid_Task_Info) is
         Message : aliased PolyORB_HI.Messages.Message_Type;
      begin
         Marshall (Internal_Code (T.Period_Event), Message);
         Deliver (T.The_Task, Encapsulate (Message, T.The_Task, T.The_Task));
      end Trigger;

      ----------------
      -- The_Driver --
      ----------------

      task body The_Driver is
         Next_Start     : Time;
         New_Next_Start : Time;
      begin
         --  Wait for the network initialization to be finished

         pragma Debug
           (Put_Line (Verbose, "Hybrid thread driver: Wait initialization"));

         Suspend_Until_True (Driver_Suspender);
         delay until System_Startup_Time;

         pragma Debug
           (Put_Line (Verbose, "Hybrid thread driver initialized"));

         Next_Start := Clock;

         --  Main task loop

         loop
            pragma Debug
              (Put_Line (Verbose, "Hybrid thread driver: new cycle"));

            --  Trigger the tasks that have to be triggered

            for TI in Hybrid_Task_Set'Range loop
               declare
                  T : Hybrid_Task_Info renames Hybrid_Task_Set (TI);
               begin
                  if T.Eligible then
                     T.Eligible := False;

                     pragma Debug
                       (Put_Line
                        (Verbose,
                         "Hybrid thread driver: Triggering task: "
                         + Entity_Image (T.The_Task)));

                     Trigger (T);
                  end if;
               end;
            end loop;

            --  Compute the next dispatch time of each hybrid task and
            --  set Next_Start to the closest activation time.

            New_Next_Start := Time_Last;

            for TI in Hybrid_Task_Set'Range loop
               declare
                  T : Hybrid_Task_Info renames Hybrid_Task_Set (TI);
               begin
                  if T.Next_Periodic_Dispatch <= Next_Start then
                     T.Next_Periodic_Dispatch :=
                       T.Next_Periodic_Dispatch + T.Period;
                  end if;

                  if T.Next_Periodic_Dispatch <= New_Next_Start then
                     New_Next_Start := T.Next_Periodic_Dispatch;
                  end if;
               end;
            end loop;

            Next_Start := New_Next_Start;

            --  Set eligible tasks

            for TI in Hybrid_Task_Set'Range loop
               declare
                  T : Hybrid_Task_Info renames Hybrid_Task_Set (TI);
               begin
                  if T.Next_Periodic_Dispatch <= Next_Start then
                     pragma Debug
                       (Put_Line
                        (Verbose,
                         "Hybrid thread driver: Eligible task: "
                         + Entity_Image (T.The_Task)));

                     T.Eligible := True;
                  end if;
               end;
            end loop;

            delay until Next_Start;
         end loop;
      end The_Driver;
   end Driver;

end PolyORB_HI.Hybrid_Task_Driver;
