------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                 P O L Y O R B _ H I . N U L L _ T A S K                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                   Copyright (C) 2014-2015 ESA & ISAE.                    --
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

--  Define a "null" task as a job to be scheduled by a
--  software-defined scheduler in place of a OS scheduler. Its
--  interface mimics the one of a periodic task.
--
--  Expected usage is for a Round-Robin non-preemptive scheduler
--  defined through a cyclic function.

with System;
with Ada.Real_Time;
with PolyORB_HI_Generated.Deployment;
with PolyORB_HI.Errors;

generic
   Entity          : in PolyORB_HI_Generated.Deployment.Entity_Type;
   --  So that the task know from which AADL entity it has been
   --  mapped.

   Task_Priority   : in System.Any_Priority;
   --  Task priority

   Task_Stack_Size : in Natural;
   --  Task stack size

   Task_Period     : in Ada.Real_Time.Time_Span;
   --  Task period

   Task_Deadline   : in Ada.Real_Time.Time_Span;
   --  Task deadline

   with function Job return PolyORB_HI.Errors.Error_Kind;
   --  Procedure to call at each dispatch of the sporadic thread

   with procedure Activate_Entrypoint is null;
   --  If given, the task run Activate_Entrypoint after the global
   --  initialization and before the task main loop.

   with procedure Recover_Entrypoint is null;
   --  If given, the task runs Recover_Entrypoint when an error is
   --  detected.

package PolyORB_HI.Null_Task is
   --  The following parameters are not used for now. The usage is
   --  reserved for future extensions.

   pragma Unreferenced (Task_Priority);
   pragma Unreferenced (Task_Stack_Size);
   pragma Unreferenced (Task_Period);
   pragma Unreferenced (Task_Deadline);

   procedure The_Null_Task;

   function Next_Deadline return Ada.Real_Time.Time;
   --  Return the value of the next deadline (in absolute time)

end PolyORB_HI.Null_Task;
