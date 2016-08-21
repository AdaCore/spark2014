------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                P O L Y O R B _ H I . S U S P E N D E R S                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2007-2009 Telecom ParisTech, 2010-2016 ESA & ISAE.      --
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

with Ada.Synchronous_Task_Control;    use Ada.Synchronous_Task_Control;
pragma Elaborate_All (Ada.Synchronous_Task_Control);

package body PolyORB_HI.Suspenders
  with Refined_State => (Elaborated_Variables => Task_Suspension_Objects),
       Spark_Mode => Off

is

   Task_Suspension_Objects : array (Entity_Type'Range) of Suspension_Object;
   --  This array is used so that each task waits on its corresponding
   --  suspension object until the transport layer initialization is
   --  complete. We are obliged to do so since Ravenscar forbids that
   --  more than one task wait on a protected object entry.

   ----------------
   -- Block_Task --
   ----------------

   procedure Block_Task (Entity : Entity_Type) is
   begin
      Suspend_Until_True (Task_Suspension_Objects (Entity));
   end Block_Task;

   ---------------------
   -- Suspend_Forever --
   ---------------------

   procedure Suspend_Forever is
   begin
      delay until Ada.Real_Time.Time_Last;
   end Suspend_Forever;

   -----------------------
   -- Unblock_All_Tasks --
   -----------------------

   procedure Unblock_All_Tasks is
   begin
      PolyORB_HI.Epoch.Set_Epoch;

      for J in Entity_Type'Range loop
         Set_True (Task_Suspension_Objects (J));
      end loop;
   end Unblock_All_Tasks;

end PolyORB_HI.Suspenders;
