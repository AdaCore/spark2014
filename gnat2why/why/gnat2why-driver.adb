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

with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;

with AA_Util;                use AA_Util;
with ALI.Util;               use ALI.Util;
with ALI;                    use ALI;
with Atree;                  use Atree;
with Binderr;
with Debug;                  use Debug;
with Einfo;                  use Einfo;
with Errout;                 use Errout;
with Flow;                   use Flow;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Opt;                    use Opt;
with Osint.C;                use Osint.C;
with Osint;                  use Osint;
with Output;                 use Output;
with Outputs;                use Outputs;
with Sem;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Stand;                  use Stand;
with Switch;                 use Switch;

with SPARK_Definition;       use SPARK_Definition;
with SPARK_Rewrite;          use SPARK_Rewrite;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Why;                    use Why;
with Why.Atree.Sprint;       use Why.Atree.Sprint;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Inter;              use Why.Inter;
with Why.Types;              use Why.Types;

with Gnat2Why.Decls;         use Gnat2Why.Decls;
with Gnat2Why.Nodes;         use Gnat2Why.Nodes;
with Gnat2Why_Args;
with Gnat2Why.Subprograms;   use Gnat2Why.Subprograms;
with Gnat2Why.Types;         use Gnat2Why.Types;
with Gnat2Why.Util;          use Gnat2Why.Util;

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

   procedure Touch_Main_File (Prefix : String);
   --  This procedure is used when there is nothing to do, but it should be
   --  signalled that everything went fine. This is done by creating the main
   --  output file of gnat2why, the main Why file.

   ---------------------------------
   -- Complete_Entity_Translation --
   ---------------------------------

   procedure Complete_Entity_Translation (E : Entity_Id) is
      File : Why_File := Why_Files (Dispatch_Entity_Completion (E));

   begin
      case Ekind (E) is
         --  Always generate a module for SPARK subprogram declarations, so
         --  that units which depend on this one can rely on the presence of
         --  the completion.

         when Subprogram_Kind =>
            if Entity_In_SPARK (E) then
               Complete_Subprogram_Spec_Translation (File, E);
            end if;

         --  Always generate a module for SPARK constant declarations, so
         --  that units which depend on this one can rely on the presence of
         --  the completion.

         when E_Constant =>
            if Entity_In_SPARK (E) and then not Is_Full_View (E) then
               Complete_Constant_Translation (File, E);
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
      --  Currently generate VCs only on subprograms in SPARK

      if not (Ekind (E) in Subprogram_Kind
               and then Entity_In_SPARK (E))
      then
         return;
      end if;

      --  Generate Why3 code to check absence of run-time errors in
      --  preconditions.

      if Has_Precondition (E)
        or else Present (Get_Subprogram_Contract_Cases (E))
      then
         Generate_VCs_For_Subprogram_Spec (Why_Files (WF_Main), E);
      end if;

      --  In 'prove' mode, generate Why3 code to check absence of run-time
      --  errors in the body of a subprogram, and to check that a subprogram
      --  body implements its contract.

      if Subprogram_Body_In_SPARK (E) then
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
      Base_Name : constant String := Body_File_Name_Without_Suffix (N);

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Rewrite_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Rewrite_Compilation_Unit);

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

   begin

      --  In global generation mode, gnat2why only generates ALI file with the
      --  suitable cross-reference section. Exit now.

      if Gnat2Why_Args.Global_Gen_Mode then
         return;
      end if;

      --  We do nothing for generic units currently. If this get revised at
      --  some point to provide proof of generics, then the special SPARK
      --  expansion in the frontend should be applied to generic units as well.

      --  We still need to create the Why files to indicate that everything
      --  went OK.

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         Touch_Main_File (Base_Name);
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
      --  misuse of SPARK specific pragmas.

      Warning_Mode := Normal;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;

      --  Warn that formal proof is about sequential code

      if Tasking_Used then
         Error_Msg_N ("?tasking is ignored in formal verification", GNAT_Root);
      end if;

      --  Compute the frame condition. This starts with identifying ALI files
      --  for the current unit and all dependent (with'ed) units. Then SPARK
      --  cross-reference information is loaded from all these files. Finally
      --  the local SPARK cross-reference information is propagated to get the
      --  frame condition.

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

      --  Load SPARK cross-reference information from ALIs for all dependent
      --  units.

      for Index in ALIs.First .. ALIs.Last loop
         Load_SPARK_Xrefs (Name_String (Name_Id
           (Full_Lib_File_Name (ALIs.Table (Index).Afile))));
      end loop;

      --  Compute the frame condition from raw SPARK cross-reference
      --  information.

      Propagate_Through_Call_Graph (Ignore_Errors => False);

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Mark all compilation units with "in SPARK / not in SPARK" marks, in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Before_Marking (Base_Name & ".alfa");
      Mark_All_Compilation_Units;
      After_Marking;

      if Compilation_Errors or else Gnat2Why_Args.Check_Mode then
         return;
      end if;

      --  Do some flow analysis

      if Gnat2Why_Args.Flow_Analysis_Mode then
         Flow_Analyse_CUnit;
      end if;

      if Compilation_Errors then
         return;
      end if;

      --  Start the translation to Why

      Init_Why_Files (GNAT_Root);
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
   -- Touch_Main_File --
   ---------------------

   procedure Touch_Main_File (Prefix : String) is
      Filename : constant String := Prefix & Why_File_Suffix (WF_Main);
   begin
      Open_Current_File (Filename & ".mlw");
      Close_Current_File;
   end Touch_Main_File;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is

      procedure Translate_List_Entities (List_Entities : List_Of_Nodes.List);
      --  Translate the list of entities from the spec or body, in batches, in
      --  order to ensure proper definition before use in Why files.

      -----------------------------
      -- Translate_List_Entities --
      -----------------------------

      procedure Translate_List_Entities (List_Entities : List_Of_Nodes.List) is
      begin
         --  Types are translated first, as the frontend generates mutually
         --  dependent definitions between constants and types, for dynamically
         --  generated types (e.g. the unconstrained array type for an input
         --  parameter).

         for E of List_Entities loop
            if Ekind (E) in Type_Kind then
               Translate_Entity (E);
            end if;
         end loop;

         --  Then all remaining entities are translated

         for E of List_Entities loop
            if Ekind (E) not in Type_Kind then
               Translate_Entity (E);
            end if;
         end loop;

         --  Finally, completions are added for entities that require one.
         --  Currently, this is done to provide a "closure" theory which
         --  includes the defining axioms for constants and expression
         --  functions. This completion is defined last to break possible
         --  mutually dependent or out-of-order definitions of constants and
         --  expression functions.

         for E of List_Entities loop
            Complete_Entity_Translation (E);
         end loop;
      end Translate_List_Entities;

   --  Start of Translate_CUnit

   begin
      for E of All_Entities loop
         if Entity_In_SPARK (E) and then not Is_In_Current_Unit (E) then
            case Ekind (E) is
               --  For all subprograms from other units, make their definition
               --  available for proofs by declaring a completion of their base
               --  theory. We only declare the "closure" theory as a
               --  completion, as it already includes the "axiom" theory if
               --  there is one (for expression functions). This does not
               --  distinguish definitions which are visible at this point
               --  from those that are not.

               when E_Function | E_Procedure =>
                  declare
                     Base_Name : constant String := Full_Name (E);
                     Name      : constant String :=
                       Base_Name & To_String (WNE_Expr_Fun_Closure);
                  begin
                     Add_Completion
                       (Base_Name, Name, Dispatch_Entity_Completion (E));
                  end;

               --  For all constants from other units, make their definition
               --  available for proofs by declaring a completion of their base
               --  theory. We only declare the "closure" theory as a
               --  completion, as it already includes the "axiom" theory if
               --  there is one.

               when E_Constant =>
                  if not Is_Full_View (E) then
                     declare
                        Base_Name : constant String := Full_Name (E);
                        Name      : constant String :=
                          Base_Name & To_String (WNE_Constant_Closure);
                     begin
                        Add_Completion
                          (Base_Name, Name, Dispatch_Entity_Completion (E));
                     end;
                  end if;

               when others =>
                  null;
            end case;
         end if;
      end loop;

      --  Translate Ada entities into Why3

      Translate_List_Entities (Spec_Entities);
      Translate_List_Entities (Body_Entities);

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
      File       : Why_File := Why_Files (Dispatch_Entity (E));
      Compl_File : Why_File := Why_Files (Dispatch_Entity_Completion (E));

   begin
      case Ekind (E) is
         when Type_Kind =>

            --  Private types not translated in Why3

            if Entity_In_SPARK (E)
              and then Ekind (E) not in Private_Kind
            then
               Translate_Type (File, E);
            end if;

         when Named_Kind =>
            if Entity_In_SPARK (E) then
               Translate_Constant (File, E);
               Translate_Constant_Value (Compl_File, E);
            end if;

         when Object_Kind =>
            if not Is_Mutable_In_Why (E) then
               if Entity_In_SPARK (E) then
                  if not Is_Full_View (E) then
                     Translate_Constant (File, E);
                  end if;
                  Translate_Constant_Value (Compl_File, E);
               end if;
            else
               Translate_Variable (File, E);
            end if;

         when Subprogram_Kind =>
            if Entity_In_SPARK (E) then
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

               Translate_Expression_Function_Body (File, Decl_E);
            end;

         --  Given to the handler for packages with an associated theory

         when E_Package =>
            if Package_Has_External_Axioms (E) or else
              Is_Instance_Of_External_Axioms (E) then
               Translate_Package_With_External_Axioms (E);
            else

               --  ??? We should deal with elaboration at this point
               --  See M618-019

               null;
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
      --  misuse of SPARK specific pragmas.

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
