------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X T R E E _ C H E C K S                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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

package body Xtree_Checks is
   --  This package provides routines to print tree-validity checks

   Node_Id_Param : constant Wide_String := "Id";

   procedure Print_Tree_Checks_Specification
     (O                : in out Output_Record;
      Prefix           : Wide_String;
      M                : Id_Multiplicity;
      Check_Cache_Only : Boolean);
   --  Print subprogram specification for the kind-validity check of
   --  a node kind.

   procedure Print_Checks_Bodies
     (O                : in out Output_Record;
      Check_Cache_Only : Boolean);

   procedure Print_Checks_Declarations
     (O                : in out Output_Record;
      Check_Cache_Only : Boolean);

   -------------------------------
   -- Print_Cache_Checks_Bodies --
   -------------------------------

   procedure Print_Cache_Checks_Bodies (O : in out Output_Record) is
   begin
      Print_Checks_Bodies (O, True);
   end Print_Cache_Checks_Bodies;

   -------------------------------------
   -- Print_Cache_Checks_Declarations --
   -------------------------------------

   procedure Print_Cache_Checks_Declarations (O : in out Output_Record) is
   begin
      Print_Checks_Declarations (O, True);
   end Print_Cache_Checks_Declarations;

   -------------------------
   -- Print_Checks_Bodies --
   -------------------------

   procedure Print_Checks_Bodies (O : in out Output_Record) is
   begin
      Print_Checks_Bodies (O, False);
   end Print_Checks_Bodies;

   procedure Print_Checks_Bodies
     (O                : in out Output_Record;
      Check_Cache_Only : Boolean)
   is

      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Tree_Check_Body, but only for nodes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Tree_Check_Body, but only for classes

      procedure Print_Tree_Check_Body (Prefix : Wide_String);
      --  Print the body of kind-validity checks for the given node kind

      ---------------------------
      -- Print_Tree_Check_Body --
      ---------------------------

      procedure Print_Tree_Check_Body (Prefix : Wide_String) is
      begin
         for M in Id_Multiplicity'Range loop
            declare
               Check_One  : constant Wide_String :=
                              (if Check_Cache_Only
                               then Cache_Check (Prefix, Id_One)
                               else Tree_Check (Prefix, Id_One));
               Check_Some  : constant Wide_String :=
                              (if Check_Cache_Only
                               then Cache_Check (Prefix, Id_Some)
                               else Tree_Check (Prefix, Id_Some));
            begin
               Print_Tree_Checks_Specification (O, Prefix, M,
                                                Check_Cache_Only);
               PL (O, " is");

               Relative_Indent (O, 2);
               case M is
                  when Id_One =>
                     if Check_Cache_Only then
                        PL (O, "(Get_Node (" & Node_Id_Param & ").Checked);");
                     else
                        PL (O,
                            "(" & Cache_Check (Prefix, M)
                            & " (" & Node_Id_Param & ")");
                        PL (O,
                            " or else "
                            & Children_Check (Prefix, M)
                            & " (" & Node_Id_Param  & "));");
                     end if;

                  when Id_Lone =>
                     PL (O,
                         "(" & Node_Id_Param & " = Why_Empty");
                     PL (O,
                         " or else "
                         & Check_One
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
                         & Check_Some
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
         S : constant Wide_String_Access := String_Lists.Element (Position);
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
   begin
      Print_Checks_Declarations (O, False);
   end Print_Checks_Declarations;

   procedure Print_Checks_Declarations
     (O                : in out Output_Record;
      Check_Cache_Only : Boolean)
   is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      -- Same as Print_Tree_Checks_Declaration, but only for node classes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      -- Same as Print_Tree_Checks_Declaration, but only for node kinds

      procedure Print_Tree_Checks_Declaration (Prefix : Wide_String);
      --  Print the declarations of kind-validity checks for the given node
      --  kind; S tells us if the Prefix designates a node kind
      --  or a node class.

      -----------------------------------
      -- Print_Tree_Checks_Declaration --
      -----------------------------------

      procedure Print_Tree_Checks_Declaration (Prefix : Wide_String) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Tree_Checks_Specification (O, Prefix, M, Check_Cache_Only);
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
         S : constant Wide_String_Access := String_Lists.Element (Position);
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
     (O                : in out Output_Record;
      Prefix           : Wide_String;
      M                : Id_Multiplicity;
      Check_Cache_Only : Boolean)
   is
      Check_Name : constant Wide_String :=
                     (if Check_Cache_Only then
                      Cache_Check (Prefix, M)
                      else Tree_Check (Prefix, M));
   begin
      PL (O, "function " & Check_Name);
      PL (O, "  (" & Node_Id_Param & " : "
          & Id_Subtype (Prefix, Unchecked, M) & ")");
      P (O, "  return Boolean");
   end Print_Tree_Checks_Specification;

end Xtree_Checks;
