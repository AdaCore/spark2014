------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ C H E C K S                          --
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

with Xkind_Tables; use Xkind_Tables;

package body Xtree_Checks is
   --  This package provides routines to print tree-validity checks

   Node_Id_Param : constant String := "Id";

   procedure Print_Tree_Checks_Specification
     (O      : in out Output_Record;
      Prefix : String;
      M      : Id_Multiplicity);
   --  Print subprogram specification for the kind-validity check of
   --  a node kind.

   -------------------------
   -- Print_Checks_Bodies --
   -------------------------

   procedure Print_Checks_Bodies (O : in out Output_Record) is

      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Tree_Check_Body, but only for nodes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Tree_Check_Body, but only for classes

      procedure Print_Tree_Check_Body (Prefix : String);
      --  Print the body of kind-validity checks for the given node kind

      ---------------------------
      -- Print_Tree_Check_Body --
      ---------------------------

      procedure Print_Tree_Check_Body (Prefix : String) is
      begin
         for M in Id_Multiplicity'Range loop
            declare
               Check_One : constant String := Cache_Check (Id_One);
            begin
               Print_Tree_Checks_Specification (O, Prefix, M);
               PL (O, " is");

               Relative_Indent (O, 2);
               case M is
                  when Id_One =>
                     PL (O,
                         "(" & Check_One
                         & " (" & Node_Id_Param & ")");
                     PL (O,
                         " or else "
                         & Children_Check (Prefix, M)
                         & " (" & Node_Id_Param  & "));");

                  when Id_Lone =>
                     PL (O,
                         "(" & Node_Id_Param & " = Why_Empty");
                     PL (O,
                         " or else "
                         & Tree_Check (Prefix, Id_One)
                         & " (" & Node_Id_Param & "));");

                  when Id_Some =>
                     PL (O, "(not Is_Empty (" & Node_Id_Param & ")");

                     if False then
                        PL (O,
                            " and then for all Element in Get_List ("
                            & Node_Id_Param & ") | ");
                        PL (O, Check_One & " (Element));");
                     else
                        PL (O, " and then True);");
                        Relative_Indent (O, -2);
                        PL (O, "--  ??? Partial implementation;");
                        PL (O, "--  ??? universal quantif on containers "
                            & "has not been implemented yet.");
                        Relative_Indent (O, 2);
                     end if;

                  when Id_Set =>
                     PL (O,
                         "(Is_Empty (" & Node_Id_Param & ")");
                     PL (O,
                         " or else "
                         & Tree_Check (Prefix, Id_Some)
                         & " (" & Node_Id_Param & "));");
               end case;
               Relative_Indent (O, -2);

               if M /= Id_Multiplicity'Last then
                  NL (O);
               end if;
            end;
         end loop;
      end Print_Tree_Check_Body;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Tree_Check_Body (Class_Name (CI));

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant String_Access := String_Lists.Element (Position);
      begin
         Print_Tree_Check_Body (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   --  Start of processing for Print_Checks_Bodies

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Checks_Bodies;

   -------------------------------
   -- Print_Checks_Declarations --
   -------------------------------

   procedure Print_Checks_Declarations (O : in out Output_Record) is

      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Tree_Checks_Declaration, but only for node classes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Tree_Checks_Declaration, but only for node kinds

      procedure Print_Tree_Checks_Declaration (Prefix : String);
      --  Print the declarations of kind-validity checks for the given node
      --  kind; S tells us if the Prefix designates a node kind
      --  or a node class.

      -----------------------------------
      -- Print_Tree_Checks_Declaration --
      -----------------------------------

      procedure Print_Tree_Checks_Declaration (Prefix : String) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Tree_Checks_Specification (O, Prefix, M);
            PL (O, ";");

            if M /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Tree_Checks_Declaration;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Tree_Checks_Declaration (Class_Name (CI));

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant String_Access := String_Lists.Element (Position);
      begin
         Print_Tree_Checks_Declaration (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   --  Start of processing for Print_Checks_Declarations

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Checks_Declarations;

   -------------------------------------
   -- Print_Tree_Checks_Specification --
   -------------------------------------

   procedure Print_Tree_Checks_Specification
     (O      : in out Output_Record;
      Prefix : String;
      M      : Id_Multiplicity)
   is
      Check_Name : constant String := Tree_Check (Prefix, M);
   begin
      PL (O, "function " & Check_Name);
      PL (O, "  (" & Node_Id_Param & " : "
          & Id_Subtype (Prefix, Unchecked, M) & ")");
      P (O, "  return Boolean");
   end Print_Tree_Checks_Specification;

end Xtree_Checks;
