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

--  with Ada.Text_IO; use Ada.Text_IO; (debugging only)

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with ALI;                   use ALI;
with ALI.Util;              use ALI.Util;
with AA_Util;               use AA_Util;
with Atree;                 use Atree;
with Binderr;
with Debug;                 use Debug;
with Einfo;                 use Einfo;
with Errout;                use Errout;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Opt;                   use Opt;
with Osint;                 use Osint;
with Osint.C;               use Osint.C;
with Output;                use Output;
with Outputs;               use Outputs;
with Sem;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Stand;                 use Stand;
with Switch;                use Switch;
with String_Utils;          use String_Utils;

with Alfa;
with Alfa.Common;           use Alfa.Common;
with Alfa.Definition;       use Alfa.Definition;
with Alfa.Filter;           use Alfa.Filter;
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Why;                   use Why;
with Why.Conversions;       use Why.Conversions;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Sprint;      use Why.Atree.Sprint;
with Why.Atree.Treepr;      use Why.Atree.Treepr;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Ids;               use Why.Ids;
with Why.Sinfo;             use Why.Sinfo;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_List_Of_Abstract_Decls
     (File  : W_File_Sections;
      Decls : List_Of_Nodes.List);
   --  Take a list of entities and translate them to Why abstract entities

   procedure Translate_List_Of_Decls
     (File      : W_File_Sections;
      Decls     : List_Of_Nodes.List;
      As_Spec   : Boolean);
   --  Take a list of Ada declarations and translate them to Why declarations.
   --  Declarations output in File should not depend on those output in
   --  Prog_File, which gives the opportunity to issue logic declarations in
   --  File (like axioms) and program declaration in Prog_File, although this
   --  is not enforced right now.

   procedure Translate_Context (File : W_File_Sections; L : String_Lists.List);
   --  Translate the context of an Ada unit into Why includes

   procedure Translate_CUnit (Type_Vars_Pack, Subp_Pack : Why_Package);
   --  Translate an Ada unit into Why declarations

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

      N         : constant Node_Id := Unit (GNAT_Root);
      Base_Name : constant String := File_Name_Without_Suffix (Sloc (N));

      Detect_Or_Force_Mode : constant Boolean :=
                               Debug_Flag_Dot_KK or Debug_Flag_Dot_EE;
      --  Flag is true if gnatprove is called in mode 'detect' or 'force',
      --  which do not involve translation to Why, so that ALI files need not
      --  be available for all units, and Alfa detection is only approximate.

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

   begin
      --  All temporaries created for this unit should be different from
      --  temporaries created for other units. To that end, use the unit name
      --  as a suffix for creating temporary names.

      New_Temp_Identifier_Suffix :=
        To_Unbounded_String (Full_Name (Defining_Entity (N)));

      Mark_Standard_Package;

      --  Authorize warnings now, since regular compiler warnings should
      --  already have been issued, e.g. to generate warnings related to
      --  misuse of Alfa specific pragmas.

      Warning_Mode := Normal;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  Warn that formal proof is about sequential code

      if Tasking_Used then
         Error_Msg_N ("?tasking is ignored in formal verification", GNAT_Root);
      end if;

      if Detect_Or_Force_Mode then
         Alfa.Frame_Conditions.Set_Ignore_Errors (True);

      else
         --  Compute the frame condition. This starts with identifying ALI
         --  files for the current unit and all dependent (with'ed) units.
         --  Then Alfa information is loaded from all these files. Finally the
         --  local Alfa information is propagated to get the frame condition.

         Initialize_ALI;
         Initialize_ALI_Source;

         --  Fill in table ALIs with all dependent units

         Read_Library_Info (Main_Lib_File, Text);

         if Text = null then
            --  No such ALI file

            Write_Str ("error:" & Get_Name_String (Main_Lib_File) &
                         " does not exist");
            Write_Eol;

            raise Terminate_Program;
         end if;

         Main_Lib_Id := Scan_ALI
           (F                => Main_Lib_File,
            T                => Text,
            Ignore_ED        => False,
            Err              => False,
            Ignore_Errors    => Debug_Flag_I,
            Directly_Scanned => True);
         Free (Text);
         Read_Withed_ALIs (Main_Lib_Id, Ignore_Errors => False);

         --  Quit if some ALI files are missing

         if Binderr.Errors_Detected > 0 then
            raise Terminate_Program;
         end if;

         --  Load Alfa information from ALIs for all dependent units

         for Index in ALIs.First .. ALIs.Last loop
            Load_Alfa (Name_String (Name_Id
              (Full_Lib_File_Name (ALIs.Table (Index).Afile))));
         end loop;

         --  Write Dependency file
         Open_Current_File (Base_Name & ".d");
         P (Current_File, Base_Name & "__package.mlw: ");
         for Index in ALIs.First .. ALIs.Last loop
            P (Current_File, " ");
            P (Current_File,
                (Name_String (Name_Id (Full_Lib_File_Name
                   (ALIs.Table (Index).Afile)))));
         end loop;
         --  Write dependencies to all other units
         declare
            AR : constant ALIs_Record := ALIs.Table (Main_Lib_Id);
         begin
            for Id in AR.First_Sdep .. AR.Last_Sdep loop
               declare
                  S : constant Sdep_Record := Sdep.Table (Id);
               begin
                  if not S.Dummy_Entry then
                     declare
                        Name : constant String :=
                                Get_Name_String (Full_Source_Name (S.Sfile));
                     begin
                        if not Ends_With (Name, "system.ads") then
                           P (Current_File, " ");
                           P (Current_File, Name);
                        end if;
                     end;
                  end if;
               end;
            end loop;
         end;

         NL (Current_File);
         Close_Current_File;

         --  Compute the frame condition from raw Alfa information

         --        Put_Line ("");
         --        Put_Line ("## Before propagation ##");
         --        Put_Line ("");
         --        Display_Maps;

         Propagate_Through_Call_Graph (Ignore_Errors => False);

         --        Put_Line ("");
         --        Put_Line ("## After propagation ##");
         --        Put_Line ("");
         --        Display_Maps;
      end if;

      --  Mark all compilation units with "in Alfa / not in Alfa" marks, in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Create_Alfa_Output_File (Base_Name & ".alfa");
      Mark_All_Compilation_Units;
      Close_Alfa_Output_File;

      if Compilation_Errors or else Debug_Flag_Dot_KK then
         return;
      end if;

   --  Start the translation to Why

      Filter_Compilation_Unit (GNAT_Root);

      Translate_CUnit (Types_Vars_Spec,
                       Subp_Spec);
      Translate_CUnit (Types_Vars_Body,
                       Subp_Body);
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

      --  For now allow and ignore -g, -O, -m and -f switches

      case Switch (First) is
         when 'g' | 'O' | 'm' | 'f' =>
            return True;

         when others =>
            return False;
      end case;
   end Is_Back_End_Switch;

   -----------------------
   -- Translate_Context --
   -----------------------

   procedure Translate_Context (File : W_File_Sections; L : String_Lists.List)
   is
      use String_Lists;
      Cur : Cursor := First (L);
   begin
      while Has_Element (Cur) loop
         Emit
           (File (W_File_Header),
            New_Include_Declaration
             (Name => New_Identifier (Element (Cur))));
         Next (Cur);
      end loop;
   end Translate_Context;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit (Type_Vars_Pack, Subp_Pack : Why_Package) is
      Type_Vars_File : constant W_File_Sections := New_File_Sections;
      Subp_File      : constant W_File_Sections := New_File_Sections;
      File           : constant W_File_Sections := New_File_Sections;
      Full_File  : W_File_Id;

      use List_Of_Nodes;
   begin
      Current_Why_Output_File := File;

      Translate_Context (Type_Vars_File, Type_Vars_Pack.WP_Context);
      Translate_Context (Subp_File, Subp_Pack.WP_Context);

      --  Translate all declarations from Type_Vars_Pack and Subp_Pack in File

      Translate_List_Of_Abstract_Decls
        (File, Type_Vars_Pack.WP_Abstract_Types);
      Translate_List_Of_Decls
        (File, Type_Vars_Pack.WP_Types, As_Spec => False);
      Translate_List_Of_Abstract_Decls
        (File, Type_Vars_Pack.WP_Abstract_Obj);
      Translate_List_Of_Decls
        (File, Type_Vars_Pack.WP_Decls, As_Spec => False);

      Translate_List_Of_Decls
        (File, Subp_Pack.WP_Decls_As_Spec, As_Spec => True);
      Translate_List_Of_Decls
        (File, Subp_Pack.WP_Decls, As_Spec => False);

      --  Copy sections in relevant file. For examepl, append program
      --  declarations after logic declarations, so all necessary axioms are
      --  seen before the corresponding logic functions are used in programs.

      Copy_Section (File, Type_Vars_File, W_File_Logic_Type);
      Copy_Section (File, Type_Vars_File, W_File_Data);

      Copy_Section (File, Subp_File, W_File_Logic_Func);
      Copy_Section (File, Subp_File, W_File_Axiom);
      Copy_Section (File, Subp_File, W_File_Prog);

      --  Generate final files

      Full_File := Get_One_File (Type_Vars_File);
      Open_Current_File (Type_Vars_Pack.WP_Name.all & ".mlw");
      Sprint_Why_Node (+Full_File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpg (+Full_File);
      end if;

      Full_File := Get_One_File (Subp_File);
      Open_Current_File (Subp_Pack.WP_Name.all & ".mlw");
      Sprint_Why_Node (+Full_File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpg (+Full_File);
      end if;
   end Translate_CUnit;

   --------------------------------------
   -- Translate_List_Of_Abstract_Types --
   --------------------------------------

   procedure Translate_List_Of_Abstract_Decls
     (File  : W_File_Sections;
      Decls : List_Of_Nodes.List)
   is
      use List_Of_Nodes;
      Cu : Cursor := Decls.First;
   begin
      --  Workaround for K526-008 and K525-019
      --  (for N of Decls loop...)
      while Cu /= No_Element loop
         declare
            N : constant Node_Id := Element (Cu);
            E : Entity_Id := N;
         begin
            if Nkind (E) /= N_Defining_Identifier then
               E := Defining_Entity (E);
            end if;

            --  if the node is not an entity, get the corresponding entity

            case Ekind (E) is
               when Type_Kind =>
                  Emit (File (W_File_Logic_Type), New_Type (Full_Name (N)));

               when Object_Kind | Named_Kind =>
                  Why_Decl_Of_Ada_Object_Decl (File, E);

               when Subprogram_Kind | E_Subprogram_Body =>
                  Transform_Subprogram (File, N, As_Spec => True);

               when others =>
                  raise Program_Error;
            end case;
         end;
         Next (Cu);
      end loop;
   end Translate_List_Of_Abstract_Decls;

   -----------------------------
   -- Translate_List_Of_Decls --
   -----------------------------

   procedure Translate_List_Of_Decls
     (File      : W_File_Sections;
      Decls     : List_Of_Nodes.List;
      As_Spec   : Boolean)
   is
      use List_Of_Nodes;

      Cu : Cursor := Decls.First;
   begin
      --  Workaround for K526-008 and K525-019
      --  (for Decl of Decls loop...)

      while Cu /= No_Element loop
         case Nkind (Element (Cu)) is
            when N_Defining_Identifier =>
               --  This is a type declaration
               Why_Type_Decl_Of_Entity (File, Element (Cu));

            when N_Subprogram_Body        |
                 N_Subprogram_Declaration =>
               Transform_Subprogram (File, Element (Cu), As_Spec);

            when N_Object_Declaration
              | N_Number_Declaration =>
               Why_Decl_Of_Ada_Object_Decl
                 (File,
                  Defining_Identifier (Element (Cu)),
                  Expression (Element (Cu)));

            when N_Parameter_Specification =>
               Why_Decl_Of_Ada_Object_Decl
                 (File,
                  Defining_Identifier (Element (Cu)));

            when N_Itype_Reference =>
               null;  --  Nothing to do

            --  The freeze point should be replaced by the declarations and
            --  and statements listed in Actions (Element (Cu)), if present.
            when N_Freeze_Entity =>
               null;

            --  The following declarations are ignored for now:
            when N_Pragma | N_Package_Declaration | N_Exception_Declaration
               | N_Exception_Renaming_Declaration =>
               null;

            --  ??? intermediate code to ease transformation
            --  To be removed

            when N_Full_Type_Declaration | N_Subtype_Declaration =>
               Why_Type_Decl_Of_Entity
                  (File,
                   Defining_Identifier (Element (Cu)));

            when others =>
               raise Not_Implemented;
         end case;

         Next (Cu);
      end loop;
   end Translate_List_Of_Decls;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is
      File       : constant W_File_Sections := New_File_Sections;
      Full_File  : W_File_Id;

      procedure Add_Standard_Type (T : Entity_Id);
      --  Add declaration for type in Standard not declared in Standard

      procedure Add_Standard_Type (T : Entity_Id) is
      begin
         Why_Type_Decl_Of_Entity (File, T);
      end Add_Standard_Type;

   begin
      Mark_Standard_Package;

      --  Authorize warnings now, since regular compiler warnings should
      --  already have been issued, e.g. to generate warnings related to
      --  misuse of Alfa specific pragmas.

      Warning_Mode := Normal;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  Generate the inclusion of the GNATprove Why theory

      Emit
        (File (W_File_Header),
         New_Include_Declaration
           (Name => New_Identifier ("_gnatprove_standard")));

      Translate_List_Of_Abstract_Decls (File, Filter_Out_Standard_Package);
      Translate_List_Of_Decls
        (File, Filter_Standard_Package, As_Spec => False);

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere

      Add_Standard_Type (Standard_Integer_8);
      Add_Standard_Type (Standard_Integer_16);
      Add_Standard_Type (Standard_Integer_32);
      Add_Standard_Type (Standard_Integer_64);
      Add_Standard_Type (Universal_Integer);
      Add_Standard_Type (Universal_Real);

      --  Additionally, the following type does not even have a type
      --  definition. The type is not in Alfa anyway, so we just generate the
      --  correct abstract type in Why.

      Emit (File (W_File_Logic_Type), New_Type ("standard___renaming_type"));

      --  We also need to define the ASCII entities

      declare
         Cur : Node_Id := First_Entity (Standard_ASCII);
      begin
         while Present (Cur) loop
            Emit
              (File (W_File_Logic_Func),
               New_Function_Decl
                 (Domain => EW_Term,
                  Name   =>
                    New_Identifier (Name => Full_Name (Cur)),
                  Binders =>
                    (1 .. 0 => <>),
                  Return_Type =>
                    New_Base_Type
                      (Ada_Node  => Standard_Character,
                       Base_Type => EW_Abstract)));
            Next_Entity (Cur);
         end loop;
      end;

      Full_File := Get_One_File (File);

      Open_Current_File ("_standard.mlw");
      Sprint_Why_Node (+Full_File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (+Full_File);
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
