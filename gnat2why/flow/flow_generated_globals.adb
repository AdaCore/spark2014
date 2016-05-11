------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . G E N E R A T E D _ G L O B A L S              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2015-2016, Altran UK Limited                 --
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
------------------------------------------------------------------------------

with Output; use Output;

package body Flow_Generated_Globals is

   ----------------------------
   -- Print_Tasking_Info_Bag --
   ----------------------------

   procedure Print_Tasking_Info_Bag (P : Phase) is

      Debug_Print_Tasking_Info : constant Boolean := False;
      --  Enables printing of tasking-related information

      use Name_Graphs;

   begin
      if not Debug_Print_Tasking_Info then
         return;
      end if;

      for Kind in Tasking_Info_Kind loop
         Write_Line ("Tasking: " & Kind'Img);
         Indent;
         if not Tasking_Info_Bag (P, Kind).Is_Empty then
            for C in Tasking_Info_Bag (P, Kind).Iterate loop
               declare
                  Subp : Entity_Name   renames Key (C);
                  Objs : Name_Sets.Set renames Tasking_Info_Bag (P, Kind) (C);
               begin
                  if not Objs.Is_Empty then
                     Write_Line (To_String (Subp) & ":");
                     Indent;
                     for Obj of Objs loop
                        Write_Line (To_String (Obj));
                     end loop;
                     Outdent;
                  end if;
               end;
            end loop;
         end if;
         Outdent;
      end loop;
   end Print_Tasking_Info_Bag;

end Flow_Generated_Globals;
