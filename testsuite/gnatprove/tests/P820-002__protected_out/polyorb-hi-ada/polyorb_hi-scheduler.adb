------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                 P O L Y O R B _ H I . S C H E D U L E R                  --
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

package body PolyORB_HI.Scheduler is

   procedure Next_Iteration;

   Current_Iteration : Integer := 0;

   --------------------
   -- Mode_Scheduler --
   --------------------

   procedure Mode_Scheduler is
   begin
      Next_Iteration;
      Change_Mode (Schedule_Table (Current_Iteration));
   end Mode_Scheduler;

   --------------------
   -- Next_Iteration --
   --------------------

   procedure Next_Iteration is
   begin
      if Current_Iteration < Array_Size then
         Current_Iteration := Current_Iteration + 1;
      else
         Current_Iteration := 0;
      end if;
      --  should be
      --  Current_Iteration := (Current_Iteration +1) mod Array_Size;
      --  but not analyzable by bound-t...
   end Next_Iteration;

   -----------------
   -- Next_Period --
   -----------------

   procedure Next_Period is
   begin
      R_Continue := False;
   end Next_Period;

end PolyORB_HI.Scheduler;
