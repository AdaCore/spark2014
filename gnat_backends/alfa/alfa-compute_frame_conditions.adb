------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--         A L F A . C O M P U T E _ F R A M E _ C O N D I T I O N S        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line;      use Ada.Command_Line;
with Ada.Text_IO;
with ALFA.Frame_Conditions; use ALFA.Frame_Conditions;

procedure ALFA.Compute_Frame_Conditions is

   Stop : exception;
   --  Terminate execution

begin
   if Argument_Count = 0 then
      Ada.Text_IO.Put_Line ("Usage: compute_fc FILE1.ali FILE2.ali ...");
      raise Stop;
   end if;

   for J in 1 .. Argument_Count loop
      Load_ALFA (Argument (J));
   end loop;

   Display_Maps;
end ALFA.Compute_Frame_Conditions;
