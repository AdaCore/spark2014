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
with Osint.C;               use Osint.C;
with Outputs;              use Outputs;
with Sinfo;                use Sinfo;
with Stand;                use Stand;
with Switch;               use Switch;

with ALFA.Filter;           use ALFA.Filter;
with ALFA.Frame_Conditions; use ALFA.Frame_Conditions;

with Why;                  use Why;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Sprint;     use Why.Atree.Sprint;
with Why.Atree.Treepr;     use Why.Atree.Treepr;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Ints;         use Why.Gen.Ints;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Ids;              use Why.Ids;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Locs;        use Gnat2Why.Locs;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;
with Gnat2Why.Types;       use Gnat2Why.Types;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_List_Of_Decls (File : W_File_Id; Decls : List_Id);
   --  Take a list of Ada declarations and translate them to Why declarations

   procedure Translate_Context (File : W_File_Id; L : List_Id);
   --  Translate the context of an Ada unit into Why includes

   procedure Translate_CUnit (GNAT_Root : Node_Id);
   --  Translate an Ada unit into Why declarations

   procedure Translate_Package (File : W_File_Id; N : Node_Id);
   --  Translate the declarations of a package into Why declarations

   procedure Translate_Standard_Package;
   --  Translate the Ada Standard package

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      Name : File_Name_Type;
      Text : Text_Buffer_Ptr;

   begin
      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  ??? Compute the frame condition. Currently only the ALI file for the
      --  current unit is read. This should be changed to read all dependent
      --  ALI files.

      Read_Library_Info (Name, Text);
      Load_ALFA (Name_String (Name_Id (Name)));
      Propagate_Through_Call_Graph;
      Declare_All_Entities;

      --  Start the translation to Why

      Translate_Standard_Package;
      Filter_Compilation_Unit (GNAT_Root);

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
               New_Include_Declaration
                 (File,
                  New_Identifier (Symbol => Chars (Name (Cur))));
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
            Why_Decl_Of_Ada_Subprogram (File, N);
         else
            Translate_Package (File, N);
         end if;
         Open_Current_File (Name_String (Name) & ".why");
         Sprint_Why_Node (File, Current_File);
         Close_Current_File;

         Open_Current_File (Name_String (Name) & ".loc");
         Print_Locations_Table (Current_File);
         Close_Current_File;

         Open_Current_File (Name_String (Name) & ".labels");
         Print_Label_List (Current_File);
         Close_Current_File;

         if Print_Generated_Code then
            wpn (File);
         end if;
      end if;
   end Translate_CUnit;

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
            when N_Full_Type_Declaration =>
               Why_Type_Decl_of_Full_Type_Decl
                  (File,
                   Defining_Identifier (Decl),
                   Type_Definition (Decl));

            when N_Subtype_Declaration =>
               Why_Type_Decl_of_Subtype_Decl
                  (File,
                   Defining_Identifier (Decl),
                   Subtype_Indication (Decl));

            when N_Subprogram_Body        |
                 N_Subprogram_Declaration =>
               Why_Decl_Of_Ada_Subprogram (File, Decl);

            when N_Object_Declaration =>
               Why_Decl_Of_Ada_Object_Decl (File, Decl);

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
      Declare_Boolean_Integer_Comparison (File);
      New_Include_Declaration
        (File => File,
         Name => New_Identifier ("divisions"));
      Sprint_Why_Node (File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (File);
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
