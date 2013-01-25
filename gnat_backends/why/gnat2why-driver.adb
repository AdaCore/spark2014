------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with GNAT.Source_Info;

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
with Sinput;                use Sinput;
with Stand;                 use Stand;
with Switch;                use Switch;

with Alfa.Definition;       use Alfa.Definition;
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;
with Alfa.Util;             use Alfa.Util;

with Why;                   use Why;
with Why.Atree.Sprint;      use Why.Atree.Sprint;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Ids;               use Why.Ids;
with Why.Inter;             use Why.Inter;
with Why.Types;             use Why.Types;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Nodes;        use Gnat2Why.Nodes;
with Gnat2Why.Subprograms;  use Gnat2Why.Subprograms;
with Gnat2Why.Types;        use Gnat2Why.Types;

pragma Warnings (Off, "unit ""Why.Atree.Treepr"" is not referenced");
with Why.Atree.Treepr;  --  To force the link of debug routines (wpn, wpt)
pragma Warnings (On,  "unit ""Why.Atree.Treepr"" is not referenced");

package body Gnat2Why.Driver is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Translate_CUnit;
   --  Translates the current compilation unit into Why

   procedure Translate_Entity (E : Entity_Id);
   --  Translates entity E into Why

   procedure Complete_Entity_Translation (E : Entity_Id);
   --  Complete the translation of entity E, after all entities from the same
   --  unit (spec or body) have been translated. This is used currently to
   --  generate a theory for expression functions that imports all necessary
   --  axioms from other expression functions.

   procedure Do_Generate_VCs (E : Entity_Id);
   --  Generates VCs for entity E. This is currently a noop if E is not a
   --  subprogram. This could be extended one day to generate VCs for the
   --  elaboration code of packages.

   procedure Print_Why_File (File : in out Why_File);
   --  Print the input Why3 file on disk

   ---------------------------------
   -- Complete_Entity_Translation --
   ---------------------------------

   procedure Complete_Entity_Translation (E : Entity_Id) is
      File : Why_File := Why_Files (Dispatch_Entity (E));

   begin
      case Ekind (E) is
         when Subprogram_Kind =>
            if In_Alfa (E) then
               --  Always generate a module for Alfa subprogram declarations,
               --  so that units which depend on this one can rely on the
               --  presence of the completion.

               Complete_Subprogram_Spec_Translation
                 (File, E, In_Body => In_Main_Unit_Body (E));
            end if;

         when others =>
            null;
      end case;
   end Complete_Entity_Translation;

   ---------------------
   -- Do_Generate_VCs --
   ---------------------

   procedure Do_Generate_VCs (E : Entity_Id) is
   begin
      --  Currently generate VCs only on subprograms in Alfa

      if not (Ekind (E) in Subprogram_Kind and then In_Alfa (E)) then
         return;
      end if;

      --  Generate Why3 code to check absence of run-time errors in
      --  preconditions.

      if Has_Precondition (E) then
         Generate_VCs_For_Subprogram_Spec (Why_Files (WF_Main), E);
      end if;

      --  In 'prove' mode, generate Why3 code to check absence of run-time
      --  errors in the body of a subprogram, and to check that a subprogram
      --  body implements its contract.

      if Body_In_Alfa (E) then
         Generate_VCs_For_Subprogram_Body (Why_Files (WF_Main), E);
      end if;
   end Do_Generate_VCs;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

      N         : constant Node_Id := Unit (GNAT_Root);
      Base_Name : constant String := File_Name_Without_Suffix (Sloc (N));

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

   begin

      --  We do not actually run the translation if we are in
      --  Frame_Condition_Mode (-gnatd.G). Back out.

      if In_Frame_Condition_Mode then
         return;
      end if;

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

      --  Compute the frame condition from raw Alfa information

      Propagate_Through_Call_Graph (Ignore_Errors => False);

      --  Mark all compilation units with "in Alfa / not in Alfa" marks, in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Before_Marking (Base_Name & ".alfa");
      Mark_All_Compilation_Units;
      After_Marking;

      if Compilation_Errors or else In_Detect_Mode_Only then
         return;
      end if;

      --  Start the translation to Why

      Init_Why_Files (File_Name_Without_Suffix (Sloc (N)));
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

   --------------------
   -- Print_Why_File --
   --------------------

   procedure Print_Why_File (File : in out Why_File) is
   begin
      Open_Current_File (File.Name.all & ".mlw");
      Sprint_Why_Node (Why_Node_Id (File.File), Current_File);
      Close_Current_File;
   end Print_Why_File;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is
   begin
      --  For all subprograms from other units, make their definition available
      --  for proofs by declaring a completion of their base theory. We only
      --  declare the "closure" theory as a completion, as it already includes
      --  the "axiom" theory if there is one (for expression functions). This
      --  does not distinguish definitions which are visible at this point from
      --  those that are not. (To be distinguished later ???)

      for E of All_Entities loop
         if Ekind (E) in E_Function | E_Procedure
           and then not Is_In_Current_Unit (E)
         then
            declare
               Base_Name : constant String := Full_Name (E);
               Name      : constant String :=
                 Base_Name & To_String (WNE_Expr_Fun_Closure);
            begin
               Add_Completion (Base_Name, Name, Dispatch_Entity (E));
            end;
         end if;
      end loop;

      --  Translate Ada entities into Why3

      for E of Spec_Entities loop
         Translate_Entity (E);
      end loop;

      for E of Spec_Entities loop
         Complete_Entity_Translation (E);
      end loop;

      for E of Body_Entities loop
         Translate_Entity (E);
      end loop;

      for E of Body_Entities loop
         Complete_Entity_Translation (E);
      end loop;

      --  Generate VCs for entities of unit. This must follow the generation of
      --  modules for entities, so that all completions for deferred constants
      --  and expression functions are defined.

      for E of Spec_Entities loop
         Do_Generate_VCs (E);
      end loop;

      for E of Body_Entities loop
         Do_Generate_VCs (E);
      end loop;

      --  Generate Why3 files

      for Kind in Why_File_Enum loop
         Print_Why_File (Why_Files (Kind));
      end loop;

      if Print_Generated_Code then
         for Kind in Why_File_Enum loop
            wpg (Why_Node_Id (Why_Files (Kind).File));
         end loop;
      end if;
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity (E : Entity_Id) is
      File : Why_File := Why_Files (Dispatch_Entity (E));

   begin
      case Ekind (E) is
         when Type_Kind =>

            --  Private types not translated in Why3

            if Ekind (E) in Private_Kind then
               null;

            elsif In_Alfa (E) then
               Translate_Type (File, E);

            else
               Open_Theory
                 (File,
                  Full_Name (E),
                  Comment =>
                    "Module for defining the private type (not in Alfa) "
                      & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                      & ", created in " & GNAT.Source_Info.Enclosing_Entity);
               Emit (File.Cur_Theory,
                     New_Type (Name => To_Why_Id (E, Local => True),
                               Args => 0));
               Close_Theory (File, Filter_Entity => E);
            end if;

         when Named_Kind =>
            if In_Alfa (E) then
               Translate_Constant (File, E);
            end if;

         when Object_Kind =>
            if not Is_Mutable_In_Why (E) then
               if In_Alfa (E) then
                  Translate_Constant (File, E);
               end if;
            else
               Translate_Variable (File, E);
            end if;

         when Subprogram_Kind =>
            if In_Alfa (E) then
               Translate_Subprogram_Spec (File, E);
            end if;

         --  An entity E_Subprogram_Body should be present only for expression
         --  functions. This allows a separate definition of theories in Why3
         --  for declaring the logic function, its axiom, and the closure of
         --  the necessary axioms. This is necessary so that they are defined
         --  with the proper visibility over previously defined entities.

         when E_Subprogram_Body =>
            declare
               Decl_E : constant Entity_Id := Unique_Entity (E);
            begin
               pragma Assert (Present (Get_Expression_Function (Decl_E)));

               --  Always generate a module, so that units which depend on this
               --  one can rely on the presence of the completion.

               Translate_Expression_Function_Body
                 (File, Decl_E, In_Body => In_Main_Unit_Body (E));
            end;

            --  Given to the handler for packages with an associated theory
         when E_Package =>
            if Dispatch_Entity (E) = WF_Context_In_Body then
               Translate_Container_Package (Why_Files (WF_Types_In_Body),
                                            File, E);
            else
               Translate_Container_Package (Why_Files (WF_Types_In_Spec),
                                            File, E);
            end if;

         when E_Loop =>
            Translate_Loop_Entity (File, E);

         when others =>
            raise Program_Error;
      end case;
   end Translate_Entity;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is
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

      Init_Why_Files (Standard_Why_Package_Name);

      Decl :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration |
                 N_Subtype_Declaration   |
                 N_Object_Declaration    =>
               Translate_Entity (Defining_Entity (Decl));
            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere

      Translate_Entity (Standard_Integer_8);
      Translate_Entity (Standard_Integer_16);
      Translate_Entity (Standard_Integer_32);
      Translate_Entity (Standard_Integer_64);
      Translate_Entity (Universal_Integer);
      Translate_Entity (Universal_Real);

      for Kind in Why_File_Enum loop
         Print_Why_File (Why_Files (Kind));
      end loop;

      if Print_Generated_Code then
         for Kind in Why_File_Enum loop
            wpg (Why_Node_Id (Why_Files (Kind).File));
         end loop;
      end if;
   end Translate_Standard_Package;

end Gnat2Why.Driver;
