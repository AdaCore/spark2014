------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Why;                   use Why;
with Why.Conversions;       use Why.Conversions;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Sprint;      use Why.Atree.Sprint;
with Why.Atree.Treepr;      use Why.Atree.Treepr;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Inter;             use Why.Inter;
with Why.Sinfo;             use Why.Sinfo;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Driver is

   --   This is the main driver for the Ada-to-Why back-end

   procedure Translate_Entity
     (E              : Entity_Id;
      Types_File     : W_File_Id;
      Variables_File : W_File_Id;
      Context_File   : W_File_Id;
      Main_File      : W_File_Id);
   --  Take an Ada entity and translate it to Why. Depending on the entity and
   --  whether it is in Alfa or not, declarations may be issued in the
   --  different parameter files.

   procedure Translate_Context (File : Why_File);
   --  Translate the context of an Ada unit into Why includes

   procedure Translate_CUnit;
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

      Translate_CUnit;
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

   procedure Translate_Context (File : Why_File) is
   begin
      for Name of File.Context loop
         Emit
           (File.File,
            New_Include_Declaration (Name => New_Identifier (Name)));
      end loop;
   end Translate_Context;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is
      procedure Print_Why_File (File : Why_File);

      procedure Print_Why_File (File : Why_File) is
      begin
         Open_Current_File (File.Name.all & ".mlw");
         Sprint_Why_Node (+File.File, Current_File);
         Close_Current_File;
      end Print_Why_File;

   begin
      --  Generate inclusions between Why3 files

      Translate_Context (Types_In_Spec_File);
      Translate_Context (Types_In_Body_File);
      Translate_Context (Variables_File);
      Translate_Context (Context_In_Spec_File);
      Translate_Context (Context_In_Body_File);
      Translate_Context (Main_File);

      --  Translate Ada entities into Why3

      for E of Spec_Entities loop
         Translate_Entity (E, Types_In_Spec_File.File, Variables_File.File,
                           Context_In_Spec_File.File, Main_File.File);
      end loop;

      for E of Body_Entities loop
         Translate_Entity (E, Types_In_Body_File.File, Variables_File.File,
                           Context_In_Body_File.File, Main_File.File);
      end loop;

      --  Generate Why3 files

      Print_Why_File (Types_In_Spec_File);
      Print_Why_File (Types_In_Body_File);
      Print_Why_File (Variables_File);
      Print_Why_File (Context_In_Spec_File);
      Print_Why_File (Context_In_Body_File);
      Print_Why_File (Main_File);

      if Print_Generated_Code then
         wpg (+Types_In_Spec_File.File);
         wpg (+Types_In_Body_File.File);
         wpg (+Variables_File.File);
         wpg (+Context_In_Spec_File.File);
         wpg (+Context_In_Body_File.File);
         wpg (+Main_File.File);
      end if;
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity
     (E              : Entity_Id;
      Types_File     : W_File_Id;
      Variables_File : W_File_Id;
      Context_File   : W_File_Id;
      Main_File      : W_File_Id) is
   begin
      case Ekind (E) is
         when Type_Kind =>
            if Type_Is_In_Alfa (E) then
               Translate_Type (Types_File, E);
            else
               Emit (Types_File, New_Type (Full_Name (E)));
            end if;

         when Named_Kind =>
            if Object_Is_In_Alfa (Unique (E)) then
               Translate_Constant (Context_File, E);
            end if;

         when Object_Kind =>
            if not Is_Mutable (E) then
               if Object_Is_In_Alfa (Unique (E)) then
                  Translate_Constant (Context_File, E);
               end if;
            else
               Translate_Variable (Variables_File, E);
            end if;

         when Subprogram_Kind   |
              E_Subprogram_Body =>

            if Spec_Is_In_Alfa (Unique (E)) then
               Translate_Subprogram_Spec (Context_File, E);
               Generate_VCs_For_Subprogram_Spec (Main_File, E);
            end if;

            if Body_Is_In_Alfa (Unique (E))
              and then not Debug.Debug_Flag_Dot_GG
            then
               Generate_VCs_For_Subprogram_Body (Main_File, E);
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Translate_Entity;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is
      File : constant W_File_Id := New_File;

      procedure Add_Standard_Type (T : Entity_Id);
      --  Add declaration for type in Standard not declared in Standard

      procedure Add_Standard_Type (T : Entity_Id) is
      begin
         Translate_Entity (T, File, File, File, File);
      end Add_Standard_Type;

      Decl : Node_Id;

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
        (File,
         New_Include_Declaration
           (Name => New_Identifier ("_gnatprove_standard")));

      Decl :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Object_Declaration    =>
               Translate_Entity (Unique_Defining_Entity (Decl),
                                File, File, File, File);

            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

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

      Emit (File, New_Type ("standard___renaming_type"));

      --  We also need to define the ASCII entities

      declare
         Cur : Node_Id := First_Entity (Standard_ASCII);
      begin
         while Present (Cur) loop
            Emit
              (File,
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

      Open_Current_File ("_standard.mlw");
      Sprint_Why_Node (+File, Current_File);
      Close_Current_File;

      if Print_Generated_Code then
         wpn (+File);
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
