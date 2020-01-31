------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                X T R E E _ C H I L D R E N _ C H E C K S                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Xkind_Tables;  use Xkind_Tables;
with Xtree_Tables;  use Xtree_Tables;
with Xtree_Classes; use Xtree_Classes;
with Why.Sinfo;     use Why.Sinfo;

package body Xtree_Children_Checks is
   --  This package provides routines to print kind-validity checks

   Node_Id_Param : constant Wide_String := "Id";

   procedure Print_Children_Checks_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String;
      M      : Id_Multiplicity);
   --  Print subprogram specification for the kind-validity check of
   --  a node kind.

   procedure Print_Children_Check_Expression
     (O      : in out Output_Record;
      Prefix : Wide_String);

   procedure Print_Class_Check_Expression
     (O      : in out Output_Record;
      CI     : Class_Info);

   ----------------------------------
   -- Print_Children_Checks_Bodies --
   ----------------------------------

   procedure Print_Children_Checks_Bodies (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Children_Check_Body, but only for nodes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Children_Check_Body, but only for classes

      procedure Print_Children_Check_Body
        (Prefix : Wide_String;
         CI     : Class_Info);
      --  Print the body of kind-validity checks for the given node
      --  kind if CI.Name is null; otherwise, print a children check
      --  for the corresponding node class.

      -------------------------------
      -- Print_Children_Check_Body --
      -------------------------------

      procedure Print_Children_Check_Body
        (Prefix : Wide_String;
         CI     : Class_Info) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Children_Checks_Specification (O, Prefix, M);
            PL (O, " is");

            Relative_Indent (O, 2);
            case M is
               when Id_One =>
                  if CI.Name = null then
                     Print_Children_Check_Expression (O, Prefix);
                  else
                     Print_Class_Check_Expression (O, CI);
                  end if;
                  NL (O);

               when Id_Lone =>
                  PL (O,
                      "(" & Node_Id_Param & " = Why_Empty");
                  PL (O,
                      " or else "
                      & Children_Check (Prefix, Id_One)
                      & " (" & Node_Id_Param & "));");

               when Id_Some =>
                  PL (O, "(not Is_Empty (" & Node_Id_Param & ")");
                  PL (O, " and then "
                      & Cache_Check (Id_Some)
                      & " (" & Node_Id_Param & "));");

               when Id_Set =>
                  PL (O,
                      "(Is_Empty (" & Node_Id_Param & ")");
                  PL (O,
                      " or else "
                      & Children_Check (Prefix, Id_Some)
                      & " (" & Node_Id_Param & "));");
            end case;
            Relative_Indent (O, -2);

            if M /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Children_Check_Body;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Children_Check_Body (Class_Name (CI), CI);

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
         Print_Children_Check_Body (S.all, (null, null, null, null));

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Children_Checks_Bodies;

   ----------------------------------------
   -- Print_Children_Checks_Declarations --
   ----------------------------------------

   procedure Print_Children_Checks_Declarations (O : in out Output_Record)
   is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Kind_Checks_Declaration, but only for node classes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Kind_Checks_Declaration, but only for node kinds

      procedure Print_Children_Checks_Declaration (Prefix : Wide_String);
      --  Print the declarations of kind-validity checks for the given node
      --  kind; S tells us if the Prefix designates a node kind
      --  or a node class.

      ---------------------------------------
      -- Print_Children_Checks_Declaration --
      ---------------------------------------

      procedure Print_Children_Checks_Declaration (Prefix : Wide_String) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Children_Checks_Specification (O, Prefix, M);
            PL (O, ";");

            if M /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Children_Checks_Declaration;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Children_Checks_Declaration (Class_Name (CI));

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
         Print_Children_Checks_Declaration (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Children_Checks_Declarations;

   --------------------------------------
   -- Print_Children_Checks_Expression --
   --------------------------------------

   procedure Print_Children_Check_Expression
     (O      : in out Output_Record;
      Prefix : Wide_String)
   is
      use Node_Lists;

      Kind : constant Why_Node_Kind :=
               Why_Node_Kind'Wide_Value (Prefix);

      procedure Print_Field_Check (Position : Cursor);

      -----------------------
      -- Print_Field_Check --
      -----------------------

      procedure Print_Field_Check (Position : Cursor) is
         FI : constant Field_Info := Element (Position);
      begin
         if Previous (Position) /= No_Element then
            Relative_Indent (O, 2);
         end if;

         if Is_Why_Id (FI) then
            PL (O, Cache_Check (Multiplicity (FI)));
            P (O, "  (Get_Node"
               & " (" & Node_Id_Param & ")"
               & "."  & Field_Name (FI) & ")");
         else
            P (O, "True");
         end if;

         if Previous (Position) /= No_Element then
            Relative_Indent (O, -2);
         end if;

         if Next (Position) /= No_Element then
            NL (O);
            PL (O, "and then");
         end if;
      end Print_Field_Check;

   begin
      P (O, "(");

      if Has_Variant_Part (Kind) then
         Why_Tree_Info (Kind).Fields.Iterate (Print_Field_Check'Access);
      else
         P (O, "True");
      end if;

      P (O, ");");
   end Print_Children_Check_Expression;

   -----------------------------------------
   -- Print_Children_Checks_Specification --
   -----------------------------------------

   procedure Print_Children_Checks_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String;
      M      : Id_Multiplicity) is
   begin
      PL (O, "function " & Children_Check (Prefix, M));
      PL (O, "  (" & Node_Id_Param & " : "
          & Id_Subtype (Prefix, Unchecked, M) & ")");
      P (O, "  return Boolean");
   end Print_Children_Checks_Specification;

   ----------------------------------
   -- Print_Class_Check_Expression --
   ----------------------------------

   procedure Print_Class_Check_Expression
     (O  : in out Output_Record;
      CI : Class_Info)
   is
      procedure Print_Kind_Expression
        (O    : in out Output_Record;
         Kind : Why_Node_Kind);

      ---------------------------
      -- Print_Kind_Expression --
      ---------------------------

      procedure Print_Kind_Expression
        (O    : in out Output_Record;
         Kind : Why_Node_Kind) is
      begin
         P (O, Children_Check (Mixed_Case_Name (Kind), Id_One)
            & " (" & Node_Id_Param & ")");
      end Print_Kind_Expression;

   begin
      Print_Class_Case_Expression (O, CI, Node_Id_Param, "False",
                                   Print_Kind_Expression'Access);
   end Print_Class_Check_Expression;

end Xtree_Children_Checks;
