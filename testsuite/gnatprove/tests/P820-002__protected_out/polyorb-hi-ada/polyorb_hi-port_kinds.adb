------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--                P O L Y O R B _ H I . P O R T _ K I N D S                 --
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

package body PolyORB_HI.Port_Kinds is

   -----------
   -- Is_In --
   -----------

   function Is_In (K : Port_Kind) return Boolean is
   begin
      return K in In_Event_Port .. In_Out_Data_Port;
   end Is_In;

   ------------
   -- Is_Out --
   ------------

   function Is_Out (K : Port_Kind) return Boolean is
   begin
      return K in In_Out_Event_Port .. Out_Data_Port;
   end Is_Out;

   --------------
   -- Is_Event --
   --------------

   function Is_Event (K : Port_Kind) return Boolean is
   begin
      return K in In_Event_Port .. In_Event_Data_Port
        or else K in In_Out_Event_Port .. In_Out_Event_Data_Port
        or else K in Out_Event_Port .. Out_Event_Data_Port;
   end Is_Event;

   -------------
   -- Is_Data --
   -------------

   function Is_Data (K : Port_Kind) return Boolean is
   begin
      return K in In_Event_Data_Port .. In_Data_Port
        or else K in In_Out_Event_Data_Port .. In_Out_Data_Port
        or else K in Out_Event_Data_Port .. Out_Data_Port;
   end Is_Data;

end PolyORB_HI.Port_Kinds;
