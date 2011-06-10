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
with Binderr;
with Debug;                 use Debug;
with Einfo;                 use Einfo;
with Errout;                use Errout;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Opt;                   use Opt;
with Osint;                 use Osint;
with Osint.C;               use Osint.C;
with Outputs;               use Outputs;
with Sem;
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
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Sprint;      use Why.Atree.Sprint;
with Why.Atree.Treepr;      use Why.Atree.Treepr;
with Why.Gen.Arrays;        use Why.Gen.Arrays;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Ints;          use Why.Gen.Ints;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Conversions;       use Why.Conversions;
with Why.Inter;             use Why.Inter;
with Why.Types;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Locs;         use Gnat2Why.Locs;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_List_Of_Abstract_Decls
     (File  : W_File_Id;
      Decls : List_Of_Nodes.List);
   --  Take a list of entities and translate them to Why abstract entities

   procedure Translate_List_Of_Decls
     (File    : W_File_Id;
      Decls   : List_Of_Nodes.List;
      As_Spec : Boolean);
   --  Take a list of Ada declarations and translate them to Why declarations

   procedure Translate_Context (File : W_File_Id; L : String_Lists.List);
   --  Translate the context of an Ada unit into Why includes

   procedure Translate_CUnit (Pack : Why_Package);
   --  Translate an Ada unit into Why declarations

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

      N          : constant Node_Id := Unit (GNAT_Root);
      Base_Name : constant String := File_Name_Without_Suffix (Sloc (N));

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

   begin
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

      --  Compute the frame condition. This starts with identifying ALI
      --  files for the current unit and all dependent (with'ed) units.
      --  Then Alfa information is loaded from all these files. Finally the
      --  local Alfa information is propagated to get the frame condition.

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

      --  Quit if some ALI files are missing

      if Binderr.Errors_Detected > 0 then
         raise Unrecoverable_Error;
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
         P (Current_File, Name_String (Name_Id (ALIs.Table (Index).Afile)));
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
                        Get_Name_String (Full_Source_Name ((S.Sfile)));
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

      Propagate_Through_Call_Graph;

--        Put_Line ("");
--        Put_Line ("## After propagation ##");
--        Put_Line ("");
--        Display_Maps;
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

      --  Workaround for K526-008 and K525-019

      --  for CU of Alfa_Compilation_Units loop
      --     Translate_CUnit (CU);
      --  end loop;
      declare
         use List_Of_Why_Packs;

         C : Cursor := Alfa_Compilation_Units.First;
      begin
         while C /= No_Element loop
            Translate_CUnit (Element (C));
            Next (C);
         end loop;
      end;

      Open_Current_File (Base_Name & "__package.loc");
      Print_Locations_Table (Current_File);
      Close_Current_File;
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

   procedure Translate_Context (File : W_File_Id; L : String_Lists.List) is
      use String_Lists;
      Cur : Cursor := First (L);
   begin
      while Has_Element (Cur) loop
         New_Include_Declaration
           (File,
            New_Identifier (Element (Cur) & ".mlw"));
         Next (Cur);
      end loop;
   end Translate_Context;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit (Pack : Why_Package)
   is
      File      : constant W_File_Id := New_File;
      Unit_Name : constant String := Pack.WP_Name.all;

      use List_Of_Nodes;
   begin
      Current_Why_Output_File := File;

      Translate_Context (File, Pack.WP_Context);
      Translate_List_Of_Abstract_Decls (File, Pack.WP_Abstract_Types);
      Translate_List_Of_Decls (File, Pack.WP_Types, As_Spec => False);
      Translate_List_Of_Abstract_Decls (File, Pack.WP_Abstract_Obj);
      Translate_List_Of_Decls (File, Pack.WP_Decls_As_Spec, As_Spec => True);
      Translate_List_Of_Decls (File, Pack.WP_Decls, As_Spec => False);

      Open_Current_File (Unit_Name & ".mlw");
      Sprint_Why_Node (+File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpg (+File);
      end if;
   end Translate_CUnit;

   --------------------------------------
   -- Translate_List_Of_Abstract_Types --
   --------------------------------------

   procedure Translate_List_Of_Abstract_Decls
     (File  : W_File_Id;
      Decls : List_Of_Nodes.List)
   is
      use List_Of_Nodes;

      Cu : Cursor := Decls.First;
   begin
      --  Workaround for K526-008 and K525-019
      --  (for N of Decls loop...)
      while Cu /= No_Element loop
         declare
            N    : constant Node_Id := Element (Cu);
            Name : constant String := Full_Name (N);
         begin
            case Ekind (N) is
               when Type_Kind =>
                  New_Abstract_Type (File, Name);

               when Object_Kind =>

                  --  Currently, do not generate a declaration for objects
                  --  whose type is defined in the standard library, as such a
                  --  type is not yet translated to Why. If such an object
                  --  appears in an effect, Why will reject the generated file.

                  if not Is_From_Standard_Library (Sloc (Etype (N))) then
                     New_Global_Ref_Declaration
                       (File     => File,
                        Name     => New_Identifier (Name),
                        Obj_Type => +Why_Logic_Type_Of_Ada_Obj (N));
                  end if;

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
     (File    : W_File_Id;
      Decls   : List_Of_Nodes.List;
      As_Spec : Boolean)
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
               Why_Decl_Of_Ada_Subprogram (File, Element (Cu), As_Spec);

            when N_Object_Declaration =>
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
      File : constant W_File_Id := New_File;

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

      Declare_Generic_Array_Type (File);

      Translate_List_Of_Abstract_Decls (File, Filter_Out_Standard_Package);
      Translate_List_Of_Decls
        (File, Filter_Standard_Package, As_Spec => False);

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere

      Add_Standard_Type (Standard_Integer_8);
      Add_Standard_Type (Standard_Integer_16);
      Add_Standard_Type (Standard_Integer_32);
      Add_Standard_Type (Standard_Integer_64);

      --  The special "HEAP" variable is defined specially

      New_Abstract_Type (File, "standard___heap_type");

      New_Global_Ref_Declaration
        (File     => File,
         Name     => New_Identifier (Alfa.Name_Of_Heap_Variable),
         Obj_Type =>
           New_Abstract_Type (Empty, New_Identifier ("standard___heap_type")));

      --  Additionally, the following type does not even have a type
      --  definition. The type is not in Alfa anyway, so we just generate the
      --  correct abstract type in Why.

      New_Abstract_Type (File, "standard___renaming_type");

      Declare_Boolean_Integer_Comparison (File);

      New_Logic
         (File => File,
          Name => New_Ignore_Name,
          Args =>
            (1 => New_Generic_Formal_Type (Name => New_Identifier ("a"))),
         Return_Type => New_Type_Unit);

      New_Include_Declaration
        (File => File,
         Name => New_Identifier ("divisions.why"));
      New_Include_Declaration
        (File => File,
         Name => New_Identifier ("bool.why"));

      --  Declare a global exception for returning from subprograms

      New_Exception
        (File,
         New_Result_Exc_Identifier,
         Why.Types.Why_Empty);

      Open_Current_File ("_standard.mlw");
      Sprint_Why_Node (+File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (+File);
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
