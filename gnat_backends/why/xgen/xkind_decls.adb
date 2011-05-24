------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X K I N D _ D E C L S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Xkind_Tables; use Xkind_Tables;

package body Xkind_Decls is

   Kind_Type_Name : constant Wide_String := "Why_Node_Kind";

   ------------------------
   -- Print_Node_Classes --
   ------------------------

   procedure Print_Node_Classes (O : in out Output_Record) is
      First : Boolean := True;
   begin
      for Class of Classes loop
         if First then
            First := False;
         else
            NL (O);
         end if;

         PL (O,
             "subtype " & Class.Name.all & " is " & Kind_Type_Name & " range");
         PL (O, "  " & Class.First.all &" ..");
         PL (O, "  " & Class.Last.all & ";");
      end loop;
   end Print_Node_Classes;

   ----------------------
   -- Print_Node_Kinds --
   ----------------------

   procedure Print_Node_Kinds (O : in out Output_Record) is
      First : Boolean := True;
   begin
      PL (O, "type " & Kind_Type_Name &" is");
      PL (O, "  (");
      Relative_Indent (O, 3);

      for Kind of Kinds loop
         if First then
            First := False;
         else
            PL (O, ",");
         end if;

         P (O, Kind.all);
      end loop;
      Relative_Indent (O, -3);
      PL (O, ");");
   end Print_Node_Kinds;

end Xkind_Decls;
