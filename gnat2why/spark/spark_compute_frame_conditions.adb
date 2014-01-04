------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--        S P A R K _ C O M P U T E _ F R A M E _ C O N D I T I O N S       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2014, AdaCore                  --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Command_Line;       use Ada.Command_Line;
with Ada.Text_IO;            use Ada.Text_IO;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;

procedure SPARK_Compute_Frame_Conditions is

   Stop : exception;
   --  Terminate execution

begin
   if Argument_Count = 0 then
      Put_Line ("Usage: compute_fc FILE1.ali FILE2.ali ...");
      raise Stop;
   end if;

   for J in 1 .. Argument_Count loop
      Load_SPARK_Xrefs (Argument (J));
   end loop;

   Put_Line ("");
   Put_Line ("## Before propagation ##");
   Put_Line ("");
   Display_Maps;

   Propagate_Through_Call_Graph (Ignore_Errors => False);

   Put_Line ("");
   Put_Line ("## After propagation ##");
   Put_Line ("");
   Display_Maps;
end SPARK_Compute_Frame_Conditions;
