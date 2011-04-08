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

--  with Ada.Text_IO; use Ada.Text_IO; (debugging only)

with ALI;                   use ALI;
with ALI.Util;              use ALI.Util;
with AA_Util;               use AA_Util;
with Atree;                 use Atree;
with Debug;                 use Debug;
with Errout;                use Errout;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Opt;                   use Opt;
with Osint;                 use Osint;
with Osint.C;               use Osint.C;
with Outputs;               use Outputs;
with Sem;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with Stand;                 use Stand;
with Switch;                use Switch;

with ALFA.Definition;       use ALFA.Definition;
with ALFA.Filter;           use ALFA.Filter;
with ALFA.Frame_Conditions; use ALFA.Frame_Conditions;

with Why;                   use Why;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Sprint;      use Why.Atree.Sprint;
with Why.Atree.Treepr;      use Why.Atree.Treepr;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Ints;          use Why.Gen.Ints;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Conversions;       use Why.Conversions;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Locs;         use Gnat2Why.Locs;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

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
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

      N          : constant Node_Id := Unit (GNAT_Root);
      Unit_Name  : constant String :=
         Name_String (Chars (Defining_Entity (N)));
      FName      : constant String :=
         Get_Name_String (File_Name (Get_Source_File_Index (Sloc (N))));
      Base_Name : constant String :=
         File_Name_Without_Suffix (FName);

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

   begin
      --  Prevent use of formal proof on code with tasking altogether

      if Tasking_Used then
         raise Program_Error;
      end if;

      --  Authorize warnings now, since regular compiler warnings should
      --  already have been issued, e.g. to generate warnings related to
      --  misuse of ALFA specific pragmas.

      Warning_Mode := Normal;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  Compute the frame condition. This starts with identifying ALI files
      --  for the current unit and all dependent (with'ed) units. Then ALFA
      --  information is loaded from all these files. Finally the local ALFA
      --  information is propagated to get the frame condition.

      Initialize_ALI;
      Initialize_ALI_Source;

      --  Fill in table ALIs with all dependent units

      Read_Library_Info (Main_Lib_File, Text);
      Main_Lib_Id := Scan_ALI
        (F                => Main_Lib_File,
         T                => Text,
         Ignore_ED        => False,
         Err              => False,
         Ignore_Errors    => Debug_Flag_I,
         Directly_Scanned => True);
      Free (Text);
      Read_Withed_ALIs (Main_Lib_Id);

      --  Load ALFA information from ALIs for all dependent units

      for Index in ALIs.First .. ALIs.Last loop
         Load_ALFA (Name_String (Name_Id (ALIs.Table (Index).Afile)));
      end loop;

      --  Write Dependency file
      Open_Current_File (Base_Name & ".d");
      P (Current_File, Unit_Name & ".why: ");
      P (Current_File, FName);
      for Index in ALIs.First .. ALIs.Last loop
         P (Current_File, " ");
         P (Current_File, Name_String (Name_Id (ALIs.Table (Index).Afile)));
      end loop;
         NL (Current_File);
      Close_Current_File;

      --  Compute the frame condition from raw ALFA information

--        Put_Line ("");
--        Put_Line ("## Before propagation ##");
--        Put_Line ("");
--        Display_Maps;

      Propagate_Through_Call_Graph;

--        Put_Line ("");
--        Put_Line ("## After propagation ##");
--        Put_Line ("");
--        Display_Maps;

      Declare_All_Entities;

      --  Mark all compilation units with "in ALFA / not in ALFA" marks, in the
      --  same order that they were processed by the frontend. Bodies are not
      --  included, except for the main unit itself, which always comes last.

      Create_ALFA_Output_File (Unit_Name & ".alfa");
      Mark_Standard_Package;
      Mark_All_Compilation_Units;
      Close_ALFA_Output_File;

      if Compilation_Errors then
         return;
      end if;

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
      File      : constant W_File_Id := New_File;
      N         : constant Node_Id   := Unit (GNAT_Root);
      Unit_Name : constant String :=
         Name_String (Chars (Defining_Unit_Name (Specification (N))));

   begin
      Current_Why_Output_File := File;

      if Nkind (GNAT_Root) = N_Compilation_Unit then

         Translate_Context (File, Context_Items (GNAT_Root));

         if Nkind (N) = N_Subprogram_Body then
            Why_Decl_Of_Ada_Subprogram (File, N);
         else
            Translate_Package (File, N);
         end if;
         Open_Current_File (Unit_Name & ".why");
         Sprint_Why_Node (+File, Current_File);
         Close_Current_File;

         Open_Current_File (Unit_Name & ".loc");
         Print_Locations_Table (Current_File);
         Close_Current_File;

         Open_Current_File (Unit_Name & ".labels");
         Print_Label_List (Current_File);
         Close_Current_File;

         if Print_Generated_Code then
            wpg (+File);
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

            when N_Itype_Reference =>
               null;  --  Nothing to do

            --  The freeze point should be replaced by the declarations and
            --  and statements listed in Actions (Decl), if present.
            when N_Freeze_Entity =>
               null;

            --  The following declarations are ignored for now:
            when N_Pragma | N_Package_Declaration | N_Exception_Declaration
               | N_Exception_Renaming_Declaration =>
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

      procedure Add_Standard_Type (T : Entity_Id);
      --  Add declaration for type in Standard not declared in Standard

      procedure Add_Standard_Type (T : Entity_Id) is
      begin
         Why_Type_Decl_of_Full_Type_Decl
           (File, T, Type_Definition (Parent (T)));
      end Add_Standard_Type;

   begin
      Translate_Package (File, Standard_Package_Node);

      Add_Standard_Type (Standard_Integer_8);
      Add_Standard_Type (Standard_Integer_16);
      Add_Standard_Type (Standard_Integer_32);
      Add_Standard_Type (Standard_Integer_64);

      Open_Current_File ("standard.why");
      Declare_Boolean_Integer_Comparison (File);

      New_Parameter
         (File => File,
          Name => New_Ignore_Name,
          Value_Type =>
            New_Arrow_Type
              (Left => New_Generic_Formal_Type (Name => New_Identifier ("a")),
               Right => New_Type_Unit));

      New_Include_Declaration
        (File => File,
         Name => New_Identifier ("divisions"));
      New_Include_Declaration
        (File => File,
         Name => New_Identifier ("bool"));
      Sprint_Why_Node (+File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (+File);
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
