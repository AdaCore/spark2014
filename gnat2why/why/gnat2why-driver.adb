------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
--                       Copyright (C) 2014-2017, Altran UK Limited         --
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

with Ada.Directories;
with Ada.Environment_Variables;
with Ada.Strings.Unbounded;           use Ada.Strings.Unbounded;
with Ada.Text_IO;
with ALI.Util;                        use ALI.Util;
with ALI;                             use ALI;
with Atree;                           use Atree;
with Binderr;
with Call;
with Common_Containers;               use Common_Containers;
with Debug;                           use Debug;
with Debug.Timing;                    use Debug.Timing;
with Einfo;                           use Einfo;
with Errout;                          use Errout;
with Flow;                            use Flow;
with Flow_Error_Messages;             use Flow_Error_Messages;
with Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                    use Flow_Utility;
with GNAT.Expect;
with GNAT.Source_Info;
with GNATCOLL.JSON;                   use GNATCOLL.JSON;
with Gnat2Why.Annotate;               use Gnat2Why.Annotate;
with Gnat2Why.Assumptions;            use Gnat2Why.Assumptions;
with Gnat2Why.Decls;                  use Gnat2Why.Decls;
with Gnat2Why.Error_Messages;         use Gnat2Why.Error_Messages;
with Gnat2Why.External_Axioms;        use Gnat2Why.External_Axioms;
with Gnat2Why.Subprograms;            use Gnat2Why.Subprograms;
with Gnat2Why.Tables;                 use Gnat2Why.Tables;
with Gnat2Why.Types;                  use Gnat2Why.Types;
with Gnat2Why.Util;                   use Gnat2Why.Util;
with Gnat2Why_Args;
with Lib;                             use Lib;
with Namet;                           use Namet;
with Nlists;                          use Nlists;
with Osint.C;                         use Osint.C;
with Osint;                           use Osint;
with Output;                          use Output;
with Outputs;                         use Outputs;
with Sem;
with Sem_Util;                        use Sem_Util;
with Sinfo;                           use Sinfo;
with Sinput;                          use Sinput;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Frame_Conditions;          use SPARK_Frame_Conditions;
with SPARK_Rewrite;                   use SPARK_Rewrite;
with SPARK_Register;                  use SPARK_Register;
with SPARK_Util;                      use SPARK_Util;
with SPARK_Util.External_Axioms;      use SPARK_Util.External_Axioms;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with Stand;                           use Stand;
with Switch;                          use Switch;
with Why;                             use Why;
with Why.Atree.Modules;               use Why.Atree.Modules;
with Why.Atree.Sprint;                use Why.Atree.Sprint;
with Why.Atree.Tables;
with Why.Inter;                       use Why.Inter;

pragma Warnings (Off, "unit ""Why.Atree.Treepr"" is not referenced");
with Why.Atree.Treepr;  --  To force the link of debug routines (wpn, wpt)
pragma Warnings (On,  "unit ""Why.Atree.Treepr"" is not referenced");

package body Gnat2Why.Driver is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Compute_Global_Effects (Current_Unit_Only : Boolean := False);
   --  Make the computed global effects information available for all
   --  subprograms.
   --
   --  If Current_Unit_Only is set then we do not pull in the ALIs of
   --  dependent units.

   procedure Complete_Declaration (E : Entity_Id);
   --  Generate completion for every subprogram or type entity in List_Entities

   function Is_Translated_Subprogram (E : Entity_Id) return Boolean
   with Pre => Entity_In_SPARK (E);
   --  @param E Subprogram entity
   --  @return True iff subprogram E needs to be translated into Why3

   procedure Translate_CUnit;
   --  Translates the current compilation unit into Why

   procedure Translate_Standard_Package;

   procedure Translate_Entity (E : Entity_Id)
   with Pre => (if Ekind (E) = E_Package
                then Entity_Spec_In_SPARK (E)
                else Entity_In_SPARK (E));
   --  Translates entity E into Why

   procedure Do_Generate_VCs (E : Entity_Id)
   with Pre => (if Ekind (E) = E_Package
                then Entity_Spec_In_SPARK (E)
                else Entity_In_SPARK (E));
   --  Generates VCs for entity E. This is currently a noop for E other than
   --  subprogram, entry, task or package.

   procedure Print_Why_File;
   --  Print the input Why3 file on disk

   procedure Touch_Main_File (Prefix : String);
   --  This procedure is used when there is nothing to do, but it should be
   --  signalled that everything went fine. This is done by creating the main
   --  output file of gnat2why, the main Why file.

   procedure Run_Gnatwhy3;
   --  After generating the Why file, run the proof tool

   procedure Create_JSON_File (Proof_Done : Boolean);
   --  At the very end, write the analysis results to disk

   procedure Generate_Assumptions;
   --  For all calls from a SPARK subprogram to another, register assumptions

   ----------------------
   -- Global Variables --
   ----------------------

   Timing : Time_Token;
   --  Timing of various gnat2why phases

   --------------------------
   -- Complete_Declaration --
   --------------------------

   procedure Complete_Declaration (E : Entity_Id) is
   begin
      case Ekind (E) is
         when E_Entry
            | E_Function
            | E_Procedure
         =>
            if Is_Translated_Subprogram (E) then
               declare
                  File : constant W_Section_Id :=
                    Dispatch_Entity_Completion (E);
               begin
                  if Ekind (E) = E_Function
                    and then Present (Get_Expression_Function (E))
                    and then Entity_Body_Compatible_With_SPARK (E)
                  then
                     Translate_Expression_Function_Body (File, E);
                  else
                     Generate_Subprogram_Completion (File, E);
                  end if;
               end;
            end if;

         when Type_Kind =>
            pragma Assert (Entity_In_SPARK (E));

            if Retysp (E) = E
              and then not Is_Standard_Boolean_Type (E)
              and then E /= Universal_Fixed
            then
               declare
                  File : constant W_Section_Id :=
                    Dispatch_Entity_Completion (E);
               begin
                  Generate_Type_Completion (File, E);
               end;
            end if;

         when others =>
            null;
      end case;
   end Complete_Declaration;

   ----------------------
   -- Create_JSON_File --
   ----------------------

   procedure Create_JSON_File (Proof_Done : Boolean) is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Unit_Name,
           Extension => "spark");
      Full : constant JSON_Value := Create_Object;
   begin
      Set_Field (Full, "spark", Create (Get_SPARK_JSON));
      Set_Field (Full, "flow", Create (Get_Flow_JSON));
      if Proof_Done then
         Set_Field (Full, "proof", Create (Get_Proof_JSON));
      end if;
      Set_Field (Full, "assumptions", Get_Assume_JSON);

      Set_Field (Full, "timings", Timing_History (Timing));

      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Create_JSON_File;

   ----------------------------
   -- Compute_Global_Effects --
   ----------------------------

   procedure Compute_Global_Effects (Current_Unit_Only : Boolean := False) is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

   begin

      --  Compute the frame condition. This starts with identifying ALI files
      --  for the current unit and all dependent (with'ed) units. Then SPARK
      --  cross-reference information is loaded from all these files. Finally
      --  the local SPARK cross-reference information is propagated to get
      --  the frame condition. Note that the failure to read an ALI file is
      --  ignored, as it can only correspond to the ALI file of an externally
      --  built unit, for which we use the declared Global contracts.

      Binderr.Initialize_Binderr;
      Initialize_ALI;
      Initialize_ALI_Source;

      --  Fill in table ALIs with all dependent units

      Read_Library_Info (Main_Lib_File, Text);

      if Text = null then
         --  No such ALI file

         Write_Line ("error:" & Get_Name_String (Main_Lib_File) &
                     " does not exist");

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

      --  If Current_Unit_Only is set then we do NOT load the with'ed
      --  ALI files.
      if Current_Unit_Only then
         Load_SPARK_Xrefs (Main_Lib_Id);

         --  Compute the frame condition from raw SPARK cross-reference
         --  information.

         Propagate_Through_Call_Graph;
      else
         Read_Withed_ALIs (Main_Lib_Id, Ignore_Errors => True);

         --  Load SPARK cross-reference information from ALIs for all
         --  dependent units.

         for Index in ALIs.First .. ALIs.Last loop
            Load_SPARK_Xrefs (Index);
         end loop;
      end if;

   end Compute_Global_Effects;

   ---------------------
   -- Do_Generate_VCs --
   ---------------------

   procedure Do_Generate_VCs (E : Entity_Id) is
   begin
      case Ekind (E) is
         when Entry_Kind
            | E_Function
            | E_Procedure
         =>
            if Entity_Spec_In_SPARK (E)

              --  Ignore invariant procedures and default initial conditions
              and then not Subprogram_Is_Ignored_For_Proof (E)
            then
               declare
                  LSP_Applies : constant Boolean :=
                    Is_Dispatching_Operation (E) and then
                    not Is_Invisible_Dispatching_Operation (E);
               begin
                  if LSP_Applies then
                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);
                     Update_Symbol_Table_For_Inherited_Contracts (E);
                  end if;

                  --  Generate Why3 code to check absence of run-time errors in
                  --  contracts and body.

                  Generate_VCs_For_Subprogram (WF_Main, E);

                  --  Generate Why3 code to check LSP for primitive of tagged
                  --  types.

                  if LSP_Applies then
                     Generate_VCs_For_LSP (WF_Main, E);
                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
                  end if;
               end;
            end if;

         when E_Package =>
            if not Entity_In_Ext_Axioms (E) then
               Generate_VCs_For_Package_Elaboration (WF_Main, E);
            end if;

         when Type_Kind =>
            if Entity_Spec_In_SPARK (Enclosing_Unit (E))
              and then Needs_Default_Checks_At_Decl (E)
            then
               Generate_VCs_For_Type (WF_Main, E);
            end if;

            if Ekind (E) in E_Protected_Type | E_Task_Type
              and then Entity_Spec_In_SPARK (E)
            then
               case Ekind (E) is
                  when E_Protected_Type =>
                     Generate_VCs_For_Protected_Type (WF_Main, E);

                  when E_Task_Type =>
                     Generate_VCs_For_Task_Type (WF_Main, E);

                  when others =>
                     raise Program_Error;
               end case;
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Do_Generate_VCs;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      E          : constant Entity_Id :=
        Unique_Defining_Entity (Unit (GNAT_Root));
      Base_Name  : constant String :=
        File_Name_Without_Suffix
          (Get_Name_String (Unit_File_Name (Main_Unit)));

      --  Note that this use of Sem.Walk_Library_Items to see units in an order
      --  which avoids forward references has caused problems in the past with
      --  the combination of generics and inlining, as well as child units
      --  referenced in parent units. To be checked.

      procedure Rewrite_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Rewrite_Compilation_Unit);

      procedure Register_All_Entities is new Sem.Walk_Library_Items
        (Action => Register_Compilation_Unit);

      procedure Mark_All_Compilation_Units is new Sem.Walk_Library_Items
        (Action => Mark_Compilation_Unit);

      --  This Boolean indicates whether proof have been attempted anywhere in
      --  the unit.
      Proof_Done : Boolean := False;

   begin
      Timing_Start (Timing);

      if Is_Generic_Unit (E) then

         --  We do nothing for generic units currently. If this get revised
         --  at some point to provide proof of generics, then the special
         --  SPARK expansion in the frontend should be applied to generic
         --  units as well. We still need to create the Why files to
         --  indicate that everything went OK. We also print a warning that
         --  nothing has been done, if the user has specifically requested
         --  analysis of this file.

         if not Gnat2Why_Args.Global_Gen_Mode then
            Touch_Main_File (Base_Name);
         end if;

         return;
      end if;

      Mark_Standard_Package;

      --  Allow the generation of new nodes and lists

      Atree.Unlock;
      Nlists.Unlock;
      Sem.Scope_Stack.Locked := False;
      Lib.Unlock;

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Then register mappings from entity names to entity ids
      Register_All_Entities;

      --  Mark all compilation units as "in SPARK / not in SPARK", in
      --  the same order that they were processed by the frontend. Bodies
      --  are not included, except for the main unit itself, which always
      --  comes last.

      Mark_All_Compilation_Units;
      Timing_Phase_Completed (Timing, "marking");

      --  Set up the flow tree utility package.

      Flow_Utility.Initialize;

      --  Finalize has to be called before we call Compilation_Errors.
      Finalize (Last_Call => False);

      if Compilation_Errors or else Gnat2Why_Args.Check_Mode then
         return;
      end if;

      --  Build hierarchical representation of scopes in the current
      --  compilation unit. This may require two traversals: for spec and body.
      declare
         Lib_Unit : constant Node_Id := Library_Unit (GNAT_Root);
      begin
         --  If both spec and body of the current compilation unit are present
         --  then traverse spec first.
         if Present (Lib_Unit) and then Lib_Unit /= GNAT_Root then
            Flow_Generated_Globals.Traversal.Build_Tree (Lib_Unit);
         end if;

         --  Then traverse body (or spec if no body is present)
         Flow_Generated_Globals.Traversal.Build_Tree (GNAT_Root);
      end;

      if Gnat2Why_Args.Global_Gen_Mode then

         --  Compute basic globals. These will be used for subprograms
         --  that are NOT in SPARK.
         Compute_Global_Effects (Current_Unit_Only => True);
         Timing_Phase_Completed (Timing, "globals (frontend)");

         Generate_Globals (GNAT_Root);
         Timing_Phase_Completed (Timing, "globals (partial)");

      else

         --  Compute basic globals
         if Gnat2Why_Args.Flow_Generate_Contracts then
            Compute_Global_Effects;
            Timing_Phase_Completed (Timing, "globals (basic)");
         end if;

         --  Read the generated globals from the ALI files
         GG_Read (GNAT_Root);
         Timing_Phase_Completed (Timing, "globals/properties (advanced)");

         --  Do some flow analysis

         Flow_Analyse_CUnit (GNAT_Root);
         Generate_Assumptions;
         Timing_Phase_Completed (Timing, "flow analysis");

         --  Start the translation to Why

         if not Gnat2Why_Args.Check_All_Mode
           and then not Gnat2Why_Args.Flow_Analysis_Mode
           and then Is_In_Analyzed_Files (E)
         then
            Proof_Done := True;
            Load_Codepeer_Results;
            Timing_Phase_Completed (Timing, "codepeer results");

            Why.Atree.Modules.Initialize;
            Init_Why_Sections;
            Timing_Phase_Completed (Timing, "init_why_sections");

            Translate_Standard_Package;
            Timing_Phase_Completed (Timing, "translation of standard");

            Translate_CUnit;
            Timing_Phase_Completed (Timing, "translation of compilation unit");

            if Has_Registered_VCs then
               Print_Why_File;

               --  After printing the .mlw file the memory consumed by the Why3
               --  AST is no longer needed; give it back to OS, so that provers
               --  can use it. When not printing the .mlw file just do nothing;
               --  there is almost nothing left to do and there is no point to
               --  waste time on manually releasing memory.
               Why.Atree.Tables.Free;

               Run_Gnatwhy3;
            end if;

            if Gnat2Why_Args.Limit_Line = Null_Unbounded_String then
               Generate_Useless_Pragma_Annotate_Warnings;
            end if;

            Timing_Phase_Completed (Timing, "proof");
         end if;
         Create_JSON_File (Proof_Done);
      end if;

      --  If gnat2why is compiled with support for profiling then separate
      --  profiling data for each phase. For file foo.ads two files will be
      --  generated in gnatprove directory: foo_phase1_gmon.out.${PID} and
      --  foo_phase2_gmon.out.${PID} (with different PIDs).
      --
      --  The target file is intentionally set at the very end of the gnat2why,
      --  to not affect other executables (e.g. provers, gnatwhy3, etc.).

      Ada.Environment_Variables.Set
        (Name  => "GMON_OUT_PREFIX",
         Value =>
           Ada.Directories.Compose
             (Name      => Unit_Name & (if Gnat2Why_Args.Global_Gen_Mode
                                        then "_phase1"
                                        else "_phase2") & "_gmon",
              Extension => "out"));

   end GNAT_To_Why;

   --------------------------
   -- Generate_Assumptions --
   --------------------------

   procedure Generate_Assumptions is
   begin
      for E of Entities_To_Translate loop
         case Ekind (E) is
            when Entry_Kind
               | E_Function
               | E_Procedure
               | E_Package
               | E_Task_Type
            =>
               --  Packages have always a "body" in the SPARK meaning, that is,
               --  some elaboration code will always be run even for packages
               --  without explicit elaboration code in the package body
               --  statements. So we always register assumptions for packages.

               if Analysis_Requested (E, With_Inlined => True)
                 and then Entity_Spec_In_SPARK (E)
                 and then (if Ekind (E) /= E_Package
                           then Entity_Body_In_SPARK (E))
               then
                  for C of Generated_Calls (E) loop
                     Register_Assumptions_For_Call (E, C);
                  end loop;
               end if;

            when others =>
               null;
         end case;
      end loop;
   end Generate_Assumptions;

   ------------------------
   -- Is_Back_End_Switch --
   ------------------------

   function Is_Back_End_Switch (Switch : String) return Boolean is
      First : constant Natural := Switch'First + 1;
      Last  : constant Natural := Switch_Last (Switch);

   begin
      --  For now we allow the -g/-O/-f/-m/-W/-w and -pipe switches, even
      --  though they will have no effect. This permits compatibility with
      --  existing scripts.

      return
        Is_Switch (Switch)
          and then (Switch (First) in 'f' | 'g' | 'm' | 'O' | 'W' | 'w'
                      or else Switch (First .. Last) = "pipe");
   end Is_Back_End_Switch;

   ------------------------------
   -- Is_Translated_Subprogram --
   ------------------------------

   function Is_Translated_Subprogram (E : Entity_Id) return Boolean is
     (
       --  Ignore inlined subprograms. Either these are not analyzed
       --  (when referenced and analysis was not specifically requested
       --  for them), in which case it's safer to skip a declaration
       --  which could be called. Or they are analyzed, but there is
       --  no call to them anyway, so skipping the declaration is safe.

       not Is_Local_Subprogram_Always_Inlined (E)

       --  Ignore invariant procedures and default initialization conditions

       and then not Subprogram_Is_Ignored_For_Proof (E)

       --  Subprograms entities of actual parameter of generic packages with
       --  external axioms are only needed for check of runtime errors.

       and then not (Ekind (E) in E_Function | E_Procedure
                     and then Is_Generic_Actual_Subprogram (E)
                     and then Entity_In_Ext_Axioms (E))

       --  Ignore simple shifts and rotates

       and then not Is_Simple_Shift_Or_Rotate (E));

   --------------------
   -- Print_Why_File --
   --------------------

   procedure Print_Why_File is
   begin
      Open_Current_File (Why_File_Name.all);
      for WF in W_Section_Id loop
         Print_Section (Why_Sections (WF), Current_File);
      end loop;
      Close_Current_File;
   end Print_Why_File;

   ------------------
   -- Run_Gnatwhy3 --
   ------------------

   procedure Run_Gnatwhy3 is
      use Ada.Directories;
      Status  : aliased Integer;
      Fn      : constant String :=
        Compose (Current_Directory, Why_File_Name.all);
      Old_Dir : constant String := Current_Directory;
      Command : constant String := Gnat2Why_Args.Why3_Args.First_Element;
   begin

      --  modifying the command line and printing it for debug purposes. We
      --  need to append the file first, then print the debug output, because
      --  this corresponds to the actual command line run, and finally remove
      --  the first argument, which is the executable name.

      Gnat2Why_Args.Why3_Args.Append (Fn);

      if Gnat2Why_Args.Debug_Mode then
         for Elt of Gnat2Why_Args.Why3_Args loop
            Ada.Text_IO.Put (Elt);
            Ada.Text_IO.Put (" ");
         end loop;
         Ada.Text_IO.New_Line;
      end if;

      Gnat2Why_Args.Why3_Args.Delete_First (1);

      Set_Directory (To_String (Gnat2Why_Args.Why3_Dir));

      Parse_Why3_Results
        (GNAT.Expect.Get_Command_Output
           (Command,
            Call.Argument_List_Of_String_List (Gnat2Why_Args.Why3_Args),
            Err_To_Out => False,
            Input      => "",
            Status     => Status'Access),
         Timing);
      Set_Directory (Old_Dir);
   end Run_Gnatwhy3;

   ---------------------
   -- Touch_Main_File --
   ---------------------

   procedure Touch_Main_File (Prefix : String) is
      Filename : constant String := Prefix & Why_File_Suffix;
   begin
      Open_Current_File (Filename);
      Close_Current_File;
   end Touch_Main_File;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id));
      --  Traversal procedure to process entities which need translation

      procedure Generate_VCs (E : Entity_Id);
      --  Check if E is in main unit and then generate VCs

      ----------------------
      -- For_All_Entities --
      ----------------------

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id))
      is
      begin
         for E of Entities_To_Translate loop
            Process (E);
         end loop;
      end For_All_Entities;

      ------------------
      -- Generate_VCs --
      ------------------

      procedure Generate_VCs (E : Entity_Id) is
      begin
         if Ekind (E) in Entry_Kind
                       | E_Function
                       | E_Package
                       | E_Procedure
                       | Type_Kind
             and then Analysis_Requested (E, With_Inlined => False)
         then
            Do_Generate_VCs (E);
         end if;
      end Generate_VCs;

   --  Start of processing for Translate_CUnit

   begin
      --  Store information for entities

      For_All_Entities (Store_Information_For_Entity'Access);

      --  Translate Ada entities into Why3

      For_All_Entities (Translate_Entity'Access);

      --  For all objects whose declaration is not visible (has not been
      --  translated to Why), we generate a dummy declaration. This must
      --  be done after translating above entities.

      For_All_External_Objects (Translate_External_Object'Access);

      --  For all state abstractions whose declaration is not visible (has not
      --  been translated to Why), we generate a dummy declaration.

      For_All_External_States (Translate_External_Object'Access);

      For_All_Entities (Complete_Declaration'Access);

      --  Generate VCs for entities of unit. This must follow the generation of
      --  modules for entities, so that all completions for deferred constants
      --  and expression functions are defined.

      For_All_Entities (Generate_VCs'Access);
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity (E : Entity_Id) is

      procedure Generate_Empty_Axiom_Theory
        (File : W_Section_Id;
         E    : Entity_Id);
      --  Generates an empty theory for the axiom related to E. This is done
      --  for every entity for which there is no axiom theory generated, so
      --  that modules for VC generation can consistently include the axiom
      --  theory of all they entities they use.

      ---------------------------------
      -- Generate_Empty_Axiom_Theory --
      ---------------------------------

      procedure Generate_Empty_Axiom_Theory
        (File : W_Section_Id;
         E    : Entity_Id) is
      begin
         Open_Theory
           (File, E_Axiom_Module (E),
            Comment =>
              "Module giving an empty axiom for the entity "
                & """" & Get_Name_String (Chars (E)) & """"
                & (if Sloc (E) > 0 then
                    " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in " & GNAT.Source_Info.Enclosing_Entity);
         Close_Theory (File,
                       Kind => Standalone_Theory);
      end Generate_Empty_Axiom_Theory;

      File       : constant W_Section_Id := Dispatch_Entity (E);
      Compl_File : constant W_Section_Id := Dispatch_Entity_Completion (E);
      New_Theory : Boolean;

   --  Start of processing for Translate_Entity

   begin
      case Ekind (E) is
         when Type_Kind =>

            --  For a type with partial and full view, both entities will be
            --  encountered here, but only one should be translated. We pick
            --  the one with the most information that's still in SPARK.

            if Retysp (E) = E then
               --  Partial views of private types should not be
               --  translated if the underlying type is not in SPARK,
               --  otherwise we end up with two definitions for the same
               --  private type.

               Translate_Type (File, E, New_Theory);
            end if;

         when Named_Kind => return;  --  Ignore named kind

         when Object_Kind =>

            --  Ignore discriminals, i.e. objects that occur for discriminants
            --  of protected types and task types.

            if Is_Discriminal (E)
                and then Ekind (Scope (E)) in E_Protected_Type | E_Task_Type
            then
               return;
            end if;

            --  Fill the set of translated object entities and do not generate
            --  a dummy declaration for those.

            Translated_Object_Entities.Include (To_Entity_Name (E));

            --  Variables that are part of a protected object are not
            --  translated separately.

            if Is_Protected_Component_Or_Discr_Or_Part_Of (E) then
               null;

            --  Constants and variables are translated differently

            elsif not Is_Mutable_In_Why (E) then
               if Ekind (E) = E_Constant then
                  if Is_Partial_View (E) then
                     Translate_Constant (File, E);
                     if not Entity_In_SPARK (Full_View (E)) then
                        Generate_Empty_Axiom_Theory (File, E);
                     end if;
                  elsif Is_Full_View (E) then
                     Translate_Constant_Value (Compl_File, E);
                  else
                     Translate_Constant (File, E);
                     Translate_Constant_Value (Compl_File, E);
                  end if;
               else
                  Translate_Constant (File, E);
                  Generate_Empty_Axiom_Theory (File, E);
               end if;

            else
               Translate_Variable (File, E);
               Generate_Empty_Axiom_Theory (File, E);
            end if;

         when E_Abstract_State =>
            Translate_Abstract_State (File, E);
            Generate_Empty_Axiom_Theory (File, E);

         --  Generate a logic function for Ada subprograms

         when E_Entry
            | E_Function
            | E_Procedure
         =>
            if Is_Translated_Subprogram (E) then
               Translate_Subprogram_Spec (File, E);
            end if;

         when E_Subprogram_Body =>
            null;

         --  Given to the handler for packages with an associated theory ???

         --  Ordinary packages are never referenced by other entities, so they
         --  don't need to be introduced like subprograms or objects. Only
         --  packages with external axiomatization needs some special work.

         when E_Package =>
            if Entity_In_Ext_Axioms (E) then
               Translate_Package_With_External_Axioms (E);
            end if;

         when E_Loop =>
            Translate_Loop_Entity (File, E);
            Generate_Empty_Axiom_Theory (File, E);

         when others =>
            raise Program_Error;
      end case;
   end Translate_Entity;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is

      procedure Translate_Standard_Entity (E : Entity_Id);
      --  Translate and complete declaration of entity E

      -------------------------------
      -- Translate_Standard_Entity --
      -------------------------------

      procedure Translate_Standard_Entity (E : Entity_Id) is
      begin
         Store_Information_For_Entity (E);
         Translate_Entity (E);
         Complete_Declaration (E);
      end Translate_Standard_Entity;

      Decl : Node_Id :=
        First (Visible_Declarations (Specification (Standard_Package_Node)));

   --  Start of processing for Translate_Standard_Package

   begin
      while Present (Decl) loop
         case Nkind (Decl) is
            when N_Full_Type_Declaration
               | N_Subtype_Declaration
               | N_Object_Declaration
            =>
               declare
                  E : constant Entity_Id := Defining_Entity (Decl);
               begin
                  if Entity_In_SPARK (E) then
                     Translate_Standard_Entity (E);
                  end if;
               end;

            when others =>
               null;
         end case;

         Next (Decl);
      end loop;

      --  The following types are not in the tree of the standard package, but
      --  still are referenced elsewhere.

      Translate_Standard_Entity (Standard_Integer_8);
      Translate_Standard_Entity (Standard_Integer_16);
      Translate_Standard_Entity (Standard_Integer_32);
      Translate_Standard_Entity (Standard_Integer_64);
      Translate_Standard_Entity (Universal_Integer);

   end Translate_Standard_Package;

end Gnat2Why.Driver;
