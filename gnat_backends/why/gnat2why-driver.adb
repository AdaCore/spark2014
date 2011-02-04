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

with AA_Util;              use AA_Util;
with Atree;                use Atree;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Opt;                  use Opt;
with Outputs;              use Outputs;
with Sinfo;                use Sinfo;
with Stand;                use Stand;
with Switch;               use Switch;

with ALFA.Filter;          use ALFA.Filter;

with Why;                  use Why;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Mutators;   use Why.Atree.Mutators;
with Why.Atree.Sprint;     use Why.Atree.Sprint;
with Why.Atree.Treepr;     use Why.Atree.Treepr;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Ids;              use Why.Ids;

with Gnat2Why.Locs;        use Gnat2Why.Locs;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Gnat2Why.Types;       use Gnat2Why.Types;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id);
   --  Take a list of Ada declarations and translate them to Why declarations

   procedure Translate_Context (File : W_File_Id; L : List_Id);
   procedure Translate_CUnit (GNAT_Root : Node_Id);

   procedure Translate_Package (File : W_File_Id; N : Node_Id);
   procedure Translate_Standard_Package;

   procedure Why_Include_Of_Ada_With_Clause (File : W_File_Id; N : Node_Id);

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
   begin
      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      Translate_Standard_Package;
      Filter_Package (Unit (GNAT_Root));

      for CU of ALFA_Compilation_Units loop
         Translate_CUnit (CU);
      end loop;
   end GNAT_To_Why;

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

            when N_Subprogram_Body        |
                 N_Subprogram_Declaration =>
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
               | N_Exception_Renaming_Declaration
               | N_Freeze_Entity | N_Itype_Reference =>
               null;

            when others =>
                  raise Not_Implemented;
         end case;

         Next (Decl);
      end loop;
   end Translate_List_Of_Decls;

   -----------------------
   -- Translate_Context --
   -----------------------

   procedure Translate_Context (File : W_File_Id; L : List_Id) is
      Cur : Node_Id;
   begin
      Cur := First (L);
      while Present (Cur) loop
         case Nkind (Cur) is
            when N_With_Clause =>
               Why_Include_Of_Ada_With_Clause (File, Cur);
            when others =>
               null;  --  ??? raise Program_Error when cases completed
         end case;
         Next (Cur);
      end loop;
   end Translate_Context;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit (GNAT_Root : Node_Id)
   is
      File : constant W_File_Id := New_File;
      N    : constant Node_Id   := Unit (GNAT_Root);
      Name : Name_Id;

   begin
      Name := Chars (Defining_Unit_Name (Specification (N)));

      if Nkind (GNAT_Root) = N_Compilation_Unit then

         Translate_Context (File, Context_Items (GNAT_Root));

         if Nkind (N) = N_Subprogram_Body then
            Why_Decl_of_Ada_Subprogram (File, N);
         else
            Translate_Package (File, N);
         end if;
         --  ??? TBD: create a file that has a meaningful name, depending on
         --  the input file
         Open_Current_File (Name_String (Name) & ".why");
         Sprint_Why_Node (File, Current_File);
         Close_Current_File;

         Open_Current_File (Name_String (Name) & ".loc");
         Print_Locations_Table (Current_File);
         Close_Current_File;

         --  ??? TBD Do we really want to write the generated locations to
         --  stdout?
         Open_Current_File (Name_String (Name) & ".labels");
         Print_Label_List (Current_File);
         Close_Current_File;

         if Print_Generated_Code then
            wpn (File);
         end if;
      end if;
   end Translate_CUnit;

   -----------------------
   -- Translate_Package --
   -----------------------

   procedure Translate_Package (File : W_File_Id; N : Node_Id) is
   begin
      case Nkind (N) is
         when N_Package_Body =>
            --  First translate the spec of the package, if any
            Translate_List_Of_Decls
              (File,
               Visible_Declarations
                 (Parent (Corresponding_Spec (N))));
            Translate_List_Of_Decls
              (File,
               Declarations (N));
         when N_Package_Declaration =>
            Translate_List_Of_Decls
              (File,
               Visible_Declarations (Specification (N)));
         when others =>
            raise Not_Implemented;
      end case;
   end Translate_Package;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is
      File : constant W_File_Id := New_File;

   begin
      Translate_Package (File, Standard_Package_Node);
      Open_Current_File ("standard.why");
      Sprint_Why_Node (File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (File);
      end if;
   end Translate_Standard_Package;

   ------------------------------------
   -- Why_Include_Of_Ada_With_Clause --
   ------------------------------------

   procedure Why_Include_Of_Ada_With_Clause (File : W_File_Id; N : Node_Id)
   is
      Id : constant Node_Id := Name (N);
   begin
      File_Append_To_Declarations
        (File,
         New_Include_Declaration
           (Ada_Node => N,
            Name     =>
              New_Identifier (Name_String (Chars (Id)) & ".why")));
   end Why_Include_Of_Ada_With_Clause;

end Gnat2Why.Driver;
