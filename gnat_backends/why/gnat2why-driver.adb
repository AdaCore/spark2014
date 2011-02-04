------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
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

with Atree;                use Atree;
with Gnat2Why.Locs;        use Gnat2Why.Locs;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Gnat2Why.Types;       use Gnat2Why.Types;
with Nlists;               use Nlists;
with Opt;                  use Opt;
with Outputs;              use Outputs;
with Sinfo;                use Sinfo;
with Sprint;               use Sprint;
with Switch;               use Switch;
with Stand;                use Stand;
with Treepr;
with Why;                  use Why;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Mutators;   use Why.Atree.Mutators;
with Why.Atree.Sprint;     use Why.Atree.Sprint;
with Why.Atree.Treepr;     use Why.Atree.Treepr;
with Why.Ids;              use Why.Ids;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id);
   --  Take a list of Ada declarations and translate them to Why declarations

   ------------------------
   -- Is_Back_End_Switch --
   ------------------------

   function Is_Back_End_Switch (Switch : String) return Boolean is
      First : constant Positive := Switch'First + 1;
      Last  : Natural           := Switch'Last;
   begin
      if Last >= First
        and then Switch (Last) = ASCII.NUL
      then
         Last := Last - 1;
      end if;

      if not Is_Switch (Switch) then
         return False;
      end if;

      --  For now we just allow the -g and -O switches, even though they
      --  will have no effect.

      case Switch (First) is
         when 'g' | 'O' =>
            return True;

         when others =>
            return False;
      end case;
   end Is_Back_End_Switch;

   -----------------------------
   -- Translate_List_Of_Decls --
   -----------------------------

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id)
   is
      Decl  : Node_Id;
   begin
      Decl := First (Decls);
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration | N_Subtype_Declaration =>
               Why_Type_Decl_of_Gnat_Type_Decl (File, Decl);

            when N_Subprogram_Body =>
               Why_Decl_of_Ada_Subprogram (File, Decl);

            when N_Object_Declaration =>
               case Nkind (Object_Definition (Decl)) is
               when N_Identifier =>
                  File_Append_To_Declarations
                    (File,
                     New_Parameter_Declaration
                       (Ada_Node => Decl,
                        Names =>
                          (1 =>
                            New_Identifier (Symbol =>
                              Chars (Defining_Identifier (Decl)))),
                        Parameter_Type =>
                           Why_Prog_Type_of_Ada_Type
                             (Object_Definition (Decl))));
               when N_Constrained_Array_Definition | N_Subtype_Indication =>
                  null;
               when others =>
                  raise Not_Implemented;
               end case;

            --  The following declarations are ignored for now:
            when N_Pragma | N_Package_Declaration | N_Exception_Declaration
               | N_Exception_Renaming_Declaration | N_Subprogram_Declaration
               | N_Freeze_Entity | N_Itype_Reference =>
               null;

            when others =>
                  raise Not_Implemented;
         end case;

         Next (Decl);
      end loop;
   end Translate_List_Of_Decls;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id)
   is
      File : constant W_File_Id := New_File;
   begin
      if Print_Generated_Code then
         Treepr.Print_Node_Subtree (GNAT_Root);
         Sprint_Node (GNAT_Root);
      end if;

      Translate_List_Of_Decls
        (File,
         Visible_Declarations (Specification (Standard_Package_Node)));

      if Nkind (GNAT_Root) = N_Compilation_Unit then
         if Nkind (Unit (GNAT_Root)) = N_Subprogram_Body then
            Why_Decl_of_Ada_Subprogram (File, Unit (GNAT_Root));
         else
            case Nkind (Unit (GNAT_Root)) is
               when N_Package_Body =>
                  --  First translate the spec of the package, if any
                  Translate_List_Of_Decls
                    (File,
                     Visible_Declarations
                        (Parent (Corresponding_Spec (Unit (GNAT_Root)))));
                  Translate_List_Of_Decls
                    (File,
                     Declarations (Unit (GNAT_Root)));
               when N_Package_Declaration =>
                  Translate_List_Of_Decls
                    (File,
                     Visible_Declarations (Specification (Unit (GNAT_Root))));
               when others =>
                  raise Not_Implemented;
            end case;
         end if;
         --  ??? TBD: create a file that has a meaningful name, depending on
         --  the input file
         Open_Current_File ("out.why");
         Sprint_Why_Node (File, Current_File);
         Close_Current_File;

         Open_Current_File ("out.loc");
         Print_Locations_Table (Current_File);
         Close_Current_File;

         --  ??? TBD Do we really want to write the generated locations to
         --  stdout?
         Open_Current_File ("out.labels");
         Print_Label_List (Current_File);

         if Print_Generated_Code then
            wpn (File);
         end if;
      end if;
   end GNAT_To_Why;

end Gnat2Why.Driver;
