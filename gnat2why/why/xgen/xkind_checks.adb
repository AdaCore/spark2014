------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         X K I N D _ C H E C K S                          --
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

package body Xkind_Checks is
   --  This package provides routines to print kind-validity checks

   Node_Id_Param : constant Wide_String := "Id";

   procedure Print_Kind_Checks_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String;
      M      : Id_Multiplicity);
   --  Print subprogram specification for the kind-validity check of
   --  a node kind.

   ------------------------------
   -- Print_Kind_Checks_Bodies --
   ------------------------------

   procedure Print_Kind_Checks_Bodies (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      type State is (Processing_Classes, Processing_Nodes);

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Kind_Check_Body, but only for nodes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Kind_Check_Body, but only for classes

      procedure Print_Kind_Check_Body (Prefix : Wide_String; S : State);
      --  Print the body of kind-validity checks for the given node
      --  kind; S tells us if the Prefix designates a node kind
      --  or a node class.

      ---------------------------
      -- Print_Kind_Check_Body --
      ---------------------------

      procedure Print_Kind_Check_Body (Prefix : Wide_String; S : State) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Kind_Checks_Specification (O, Prefix, M);
            PL (O, " is");

            Relative_Indent (O, 2);
            case M is
               when Id_One =>
                  P (O,
                     "(Get_Kind (" & Node_Id_Param & ")");

                  case S is
                     when Processing_Nodes =>
                        P (O, " = " & Prefix);
                     when Processing_Classes =>
                        P (O, " in " & Prefix & "'Range");
                  end case;

                  PL (O, ");");

               when Id_Lone =>
                  PL (O,
                      "(" & Node_Id_Param & " = Why_Empty");
                  PL (O,
                      " or else "
                      & Kind_Check (Prefix, Id_One)
                      & " (" & Node_Id_Param & "));");

               when Id_Some =>
                  PL (O, "(not Is_Empty (" & Node_Id_Param & ")");

                  if False then
                     PL (O,
                         " and then for all Element in Get_List ("
                         & Node_Id_Param & ") | ");
                     PL (O, Kind_Check (Prefix, Id_One) & " (Element));");
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
                      & Kind_Check (Prefix, Id_Some)
                      & " (" & Node_Id_Param & "));");
            end case;
            Relative_Indent (O, -2);

            if M /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Kind_Check_Body;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Kind_Check_Body (Class_Name (CI), Processing_Classes);

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
         Print_Kind_Check_Body (S.all, Processing_Nodes);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Kind_Checks_Bodies;

   ------------------------------------
   -- Print_Kind_Checks_Declarations --
   ------------------------------------

   procedure Print_Kind_Checks_Declarations (O : in out Output_Record)
   is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Kind_Checks_Declaration, but only for node classes

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Kind_Checks_Declaration, but only for node kinds

      procedure Print_Kind_Checks_Declaration (Prefix : Wide_String);
      --  Print the declarations of kind-validity checks for the given node
      --  kind; S tells us if the Prefix designates a node kind
      --  or a node class.

      -----------------------------------
      -- Print_Kind_Checks_Declaration --
      -----------------------------------

      procedure Print_Kind_Checks_Declaration (Prefix : Wide_String) is
      begin
         for M in Id_Multiplicity'Range loop
            Print_Kind_Checks_Specification (O, Prefix, M);
            PL (O, ";");

            if M /= Id_Multiplicity'Last then
               NL (O);
            end if;
         end loop;
      end Print_Kind_Checks_Declaration;

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Kind_Checks_Declaration (Class_Name (CI));

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
         Print_Kind_Checks_Declaration (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_Kind_Checks_Declarations;

   -------------------------------------
   -- Print_Kind_Checks_Specification --
   -------------------------------------

   procedure Print_Kind_Checks_Specification
     (O      : in out Output_Record;
      Prefix : Wide_String;
      M      : Id_Multiplicity) is
   begin
      PL (O, "function " & Kind_Check (Prefix, M));
      PL (O, "  (" & Node_Id_Param & " : "
          & Id_Subtype (Prefix, Opaque, M) & ")");
      P (O, "  return Boolean");
   end Print_Kind_Checks_Specification;

end Xkind_Checks;
