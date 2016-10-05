------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                     P O L Y O R B _ H I . E P O C H                      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2015 ESA & ISAE.                       --
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

with Ada.Real_Time;

package PolyORB_HI.Epoch
  with Abstract_State => (Elaborated_Variables with Synchronous,
                          External => (Effective_Reads,
                                       Effective_Writes,
                                       Async_Writers,
                                       Async_Readers)),
       Initializes => Elaborated_Variables
is

   procedure System_Startup_Time (SST: out Ada.Real_Time.Time)
     with Global => (Input => Elaborated_Variables);
   --  Startup time of user tasks

   procedure Set_Epoch
     with Global => (In_Out => Elaborated_Variables,
                     Input  => Ada.Real_Time.Clock_Time);
end PolyORB_HI.Epoch;
