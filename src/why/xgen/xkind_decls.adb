------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X K I N D _ D E C L S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Why.Sinfo;    use Why.Sinfo;
with Xkind_Tables; use Xkind_Tables;

package body Xkind_Decls is

   Kind_Type_Name : constant String := "Why_Node_Kind";

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

         PL (O, "    " & Class.First.all & " ..");
         for Kind in Why_Node_Kind'Succ (Class_First (Class))
           .. Why_Node_Kind'Pred (Class_Last (Class)) loop
            PL (O, "--  " & Mixed_Case_Name (Kind));
         end loop;
         PL (O, "    " & Class.Last.all & ";");
      end loop;
   end Print_Node_Classes;

end Xkind_Decls;
