------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ D E C L S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Xkind_Tables; use Xkind_Tables;
with Xtree_Tables; use Xtree_Tables;
with Why.Sinfo;    use Why.Sinfo;

package body Xtree_Decls is

   Node_Kind_Name : constant Wide_String := "Why_Node_Kind";
   Node_Type_Name : constant Wide_String := "Why_Node";
   Kind_Name      : constant Wide_String := "Kind";

   ---------------------
   -- Print_Node_Type --
   ---------------------

   procedure Print_Node_Type (O : in out Output_Record) is
      use Node_Lists;
   begin
      PL (O, "type " & Node_Type_Name
          & " (" & Kind_Name  & " : " & Node_Kind_Name
          & " := " & Default_Kind & ")"
          & " is record");
      Relative_Indent (O, 3);

      PL (O, "--  Basic type for nodes in the abstract syntax tree.");

      NL (O);
      Print_Box (O, "Common Fields");
      NL (O);

      PL (O, "--  Fields that are shared amongst all node kinds");
      NL (O);

      for FI of Common_Fields.Fields loop
         PL (O, Field_Name (FI)  & " : " & Type_Name (FI, Opaque)  & ";");
         NL (O);
      end loop;

      Print_Box (O, "Variant Part");
      NL (O);

      PL (O, "case " & Kind_Name & " is");
      Relative_Indent (O, 3);

      for Kind in Why_Tree_Info'Range loop
         PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
         Relative_Indent (O, 3);

         if Is_Empty (Why_Tree_Info (Kind).Fields) then
            PL (O, "null;");
         else
            for FI of Why_Tree_Info (Kind).Fields loop
               P (O, Field_Name (FI));
               Adjust_Columns (O,
                               Field_Name (FI)'Length,
                               Why_Tree_Info (Kind).Max_Field_Name_Length);
               PL (O, ": " & Type_Name (FI, Opaque)  & ";");
            end loop;
         end if;

         NL (O);
         Relative_Indent (O, -3);
      end loop;

      Relative_Indent (O, -3);
      PL (O, "end case;");
      Relative_Indent (O, -3);
      PL (O, "end record;");
   end Print_Node_Type;

end Xtree_Decls;
