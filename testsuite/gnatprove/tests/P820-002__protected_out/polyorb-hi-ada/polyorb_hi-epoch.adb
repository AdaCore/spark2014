------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                     P O L Y O R B _ H I . E P O C H                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                   Copyright (C) 2015-2016 ESA & ISAE.                    --
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

package body PolyORB_HI.Epoch
  with Refined_State => (Elaborated_Variables => (Epoch_Data))
is

   use type Ada.Real_Time.Time;

   ----------------
   -- Epoch_Data --
   ----------------

   protected type Epoch_Data_T is
     function System_Startup_Time return Ada.Real_Time.Time;
     procedure Set_Epoch (The_Time : Ada.Real_Time.Time);

   private
      The_System_Startup_Time : Ada.Real_Time.Time
        := Ada.Real_Time.Time_First;
   end Epoch_Data_T;

   Epoch_Data : Epoch_Data_T;

   protected body Epoch_Data_T is

     function System_Startup_Time return Ada.Real_Time.Time is
     begin
        return The_System_Startup_Time;
     end System_Startup_Time;

     procedure Set_Epoch (The_Time : Ada.Real_Time.Time) is
     begin
        The_System_Startup_Time := The_Time;
     end Set_Epoch;

   end Epoch_Data_T;

  -------------------------
  -- System_Startup_Time --
  -------------------------

   procedure System_Startup_Time (SST: out Ada.Real_Time.Time) is
   begin
      SST := Epoch_Data.System_Startup_Time;
   end System_Startup_Time;

   ---------------
   -- Set_Epoch --
   ---------------

   procedure Set_Epoch is
      CTime : constant Ada.Real_Time.Time
        := Ada.Real_Time.Clock;
   begin
      Epoch_Data.Set_Epoch
        (CTime + Ada.Real_Time.Milliseconds (1_000));
   end Set_Epoch;

end PolyORB_HI.Epoch;
