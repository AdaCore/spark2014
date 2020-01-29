------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                Copyright (C) 2014-2020, Altran UK Limited                --
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

with Ada.Containers.Hashed_Maps;
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
with Flow.Dynamic_Memory;
with Flow_Error_Messages;             use Flow_Error_Messages;
with Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Types;                      use Flow_Types;
with Flow_Utility;                    use Flow_Utility;
with Flow_Visibility;                 use Flow_Visibility;
with GNAT.OS_Lib;                     use GNAT.OS_Lib;
with GNAT.SHA1;
with GNAT.Source_Info;
with GNATCOLL.JSON;                   use GNATCOLL.JSON;
with Gnat2Why.Assumptions;            use Gnat2Why.Assumptions;
with Gnat2Why.Borrow_Checker;         use Gnat2Why.Borrow_Checker;
with Gnat2Why.Decls;                  use Gnat2Why.Decls;
with Gnat2Why.Error_Messages;         use Gnat2Why.Error_Messages;
with Gnat2Why.External_Axioms;        use Gnat2Why.External_Axioms;
with Gnat2Why.Subprograms;            use Gnat2Why.Subprograms;
with Gnat2Why.Tables;                 use Gnat2Why.Tables;
with Gnat2Why.Types;                  use Gnat2Why.Types;
with Gnat2Why.Util;                   use Gnat2Why.Util;
with Gnat2Why_Args;
with Hashing;                         use Hashing;
with Lib;                             use Lib;
with Namet;                           use Namet;
with Nlists;                          use Nlists;
with Osint.C;                         use Osint.C;
with Osint;                           use Osint;
with Outputs;                         use Outputs;
with Sem;
with Sem_Aux;                         use Sem_Aux;
with Sem_Util;                        use Sem_Util;
with Sinfo;                           use Sinfo;
with Sinput;                          use Sinput;
with SPARK_Annotate;                  use SPARK_Annotate;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Register;                  use SPARK_Register;
with SPARK_Rewrite;                   use SPARK_Rewrite;
with SPARK_Util;                      use SPARK_Util;
with SPARK_Util.External_Axioms;      use SPARK_Util.External_Axioms;
with SPARK_Util.Hardcoded;            use SPARK_Util.Hardcoded;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with SPARK_Xrefs;
with Stand;                           use Stand;
with String_Utils;                    use String_Utils;
with Switch;                          use Switch;
with Tempdir;                         use Tempdir;
with VC_Kinds;
with Why;                             use Why;
with Why.Atree.Modules;               use Why.Atree.Modules;
with Why.Atree.To_Json;               use Why.Atree.To_Json;
with Why.Atree.Tables;                use Why.Atree.Tables;
with Why.Gen.Binders;                 use Why.Gen.Binders;
with Why.Gen.Names;
with Why.Inter;                       use Why.Inter;
with Why.Types;                       use Why.Types;

pragma Warnings (Off, "unit ""Why.Atree.Treepr"" is not referenced");
with Why.Atree.Treepr;  --  To force the link of debug routines (wpn, wpt)
pragma Warnings (On,  "unit ""Why.Atree.Treepr"" is not referenced");

package body Gnat2Why.Driver is

   use type Ada.Containers.Count_Type;
   --  for comparison of map length

   Max_Subprocesses : constant := 63;
   --  The maximal number of gnatwhy3 processes spawned by a single gnat2why.
   --  This limits corresponds to MAXIMUM_WAIT_OBJECTS on Windows.

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Prescan_ALI_Files;
   --  Pre-scan ALI files, so they can be easily iterated

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

   procedure Translate_Hidden_Globals (E : Entity_Id);
   --  Translate "hidden" globals of E, e.g. declared in other compilation
   --  units (and thus only known by name), or not in SPARK (thus ignored by
   --  marking), or representing invisible constituents of abstract states.

   procedure Do_Generate_VCs (E : Entity_Id)
   with Pre => (if Ekind (E) = E_Package
                then Entity_Spec_In_SPARK (E)
                else Entity_In_SPARK (E));
   --  Generates VCs for entity E. This is currently a noop for E other than
   --  subprogram, entry, task or package.

   procedure Do_Ownership_Checking;
   --  Perform SPARK access legality checking

   procedure Print_Gnat_Json_File (Filename : String);
   --  Print the Gnat AST as Json on disk

   procedure Create_JSON_File (Proof_Done : Boolean);
   --  At the very end, write the analysis results to disk

   procedure Generate_Assumptions;
   --  For all calls from a SPARK subprogram to another, register assumptions

   ----------------------
   -- Global Variables --
   ----------------------

   Timing : Time_Token;
   --  Timing of various gnat2why phases

   Translated_Object_Names : Name_Sets.Set;
   --  Objects not in SPARK but still translated to Why; we get them from the
   --  Global contracts (where repetitions are fine) and keep track of them to
   --  translate each of them exactly once.

   function Process_Id_Hash (X : Process_Id) return Ada.Containers.Hash_Type
     is (Generic_Integer_Hash (Pid_To_Integer (X)));
   --  Hash function for process ids to be used in Hashed maps

   package Pid_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Process_Id,
      Element_Type    => Path_Name_Type,
      Hash            => Process_Id_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Output_File_Map : Pid_Maps.Map;
   --  Global map which stores the temp file names in which the various
   --  gnatwhy3 processes store their output, by process id.

   procedure Collect_One_Result
     with Pre => not Output_File_Map.Is_Empty;
   --  Wait for one gnatwhy3 process to finish and process its results. If a
   --  previously finished gnatwhy3 is already waiting to be collected, this
   --  procedure returns immediately.

   procedure Collect_Results
     with Post => Output_File_Map.Is_Empty;
   --  Wait until all child gnatwhy3 processes finish and collect their results

   procedure Run_Gnatwhy3 (Filename : String)
   with Pre => Output_File_Map.Length <= Max_Subprocesses;
   --  After generating the Why file, run the proof tool. Wait for existing
   --  gnatwhy3 processes to finish if Max_Subprocesses is already reached.

   Max_Why3_Filename_Length : constant := 104;
   --  On windows, a path can be no longer than 250 or so chars. We allow a
   --  maximum of 104 chars (100 chars + 4 four the file extension) for the
   --  why3 file so that users still have 150 chars or so for their own project
   --  structure.

   function Compute_Why3_File_Name
     (E : Entity_Id; Extension : String) return String with Post =>
       Compute_Why3_File_Name'Result'Length <= Max_Why3_Filename_Length;
   --  Compute the why3 file to be used. Guarantees to be no longer than
   --  Max_Why3_Filename_Length and makes some effort to still be unique.

   ------------------------
   -- Collect_One_Result --
   ------------------------

   procedure Collect_One_Result
   is
      Pid     : Process_Id;
      Success : Boolean;
      pragma Unreferenced (Success);
   begin
      Wait_Process (Pid, Success);
      pragma Assert (Pid /= Invalid_Pid);
      declare
         Fn : constant String := Get_Name_String (Output_File_Map (Pid));
      begin
         Parse_Why3_Results (Fn, Timing);
         Delete_File (Fn, Success);
         Output_File_Map.Delete (Pid);
      end;
   end Collect_One_Result;

   ---------------------
   -- Collect_Results --
   ---------------------

   procedure Collect_Results is
   begin
      while not Output_File_Map.Is_Empty loop
         Collect_One_Result;
      end loop;
   end Collect_Results;

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

   ----------------------------
   -- Compute_Why3_File_Name --
   ----------------------------

   function Compute_Why3_File_Name
     (E : Entity_Id; Extension : String)
     return String is
      S : constant String := Full_Name (E);
      Digest_Length : constant := 20;
      --  arbitrary number of digits that we take from the SHA1 digest to
      --  achieve uniqueness
   begin
      if S'Length > Max_Why3_Filename_Length - Extension'Length then
         --  the slice bound is computed as follows:
         --  take Max_Why3_Filename_Length - 1
         --  remove the file ending
         --  remove 1 for the dash
         --  remove Digest_Length for the digest
         return GNAT.SHA1.Digest (S) (1 .. Digest_Length) & "-" &
           S (S'Last - (Max_Why3_Filename_Length - 1 -
                          Extension'Length - 1 - Digest_Length)
              .. S'Last)
           & Extension;
      else
         return S & Extension;
      end if;
   end Compute_Why3_File_Name;

   ----------------------
   -- Create_JSON_File --
   ----------------------

   procedure Create_JSON_File (Proof_Done : Boolean) is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Unit_Name,
           Extension => VC_Kinds.SPARK_Suffix);
      Full : constant JSON_Value := Create_Object;
   begin
      Set_Field (Full, "spark", Create (Get_SPARK_JSON));
      Set_Field (Full, "flow", Create (Get_Flow_JSON));
      if Proof_Done then
         Set_Field (Full, "session_map", Get_Session_Map_JSON);
         Set_Field (Full, "proof", Create (Get_Proof_JSON));
      end if;
      Set_Field (Full, "assumptions", Get_Assume_JSON);

      Set_Field (Full, "timings", Timing_History (Timing));

      Ada.Text_IO.Create (FD, Ada.Text_IO.Out_File, File_Name);
      Ada.Text_IO.Put (FD, GNATCOLL.JSON.Write (Full, Compact => False));
      Ada.Text_IO.Close (FD);
   end Create_JSON_File;

   -----------------------
   -- Prescan_ALI_Files --
   -----------------------

   procedure Prescan_ALI_Files is
      Main_Lib_File : File_Name_Type;
      Text          : Text_Buffer_Ptr;
      Main_Lib_Id   : ALI_Id;

   begin
      --  Identify ALI files for the current unit and all dependent (with'ed)
      --  units. Then the "generated globals" information is loaded from all
      --  these files. Note that the failure to read an ALI file is ignored, as
      --  it can only correspond to the ALI file of an externally built unit,
      --  for which we use the declared Global contracts.

      Binderr.Initialize_Binderr;
      Initialize_ALI;
      Initialize_ALI_Source;

      --  Fill in table ALIs with all dependent units

      Read_Library_Info (Main_Lib_File, Text);

      pragma Assert (Text /= null);

      Main_Lib_Id := Scan_ALI
        (F             => Main_Lib_File,
         T             => Text,
         Ignore_ED     => False,
         Err           => False,
         Ignore_Errors => Debug_Flag_I);
      Free (Text);

      Read_Withed_ALIs (Main_Lib_Id);
   end Prescan_ALI_Files;

   ---------------------
   -- Do_Generate_VCs --
   ---------------------

   procedure Do_Generate_VCs (E : Entity_Id) is
      Old_Num : constant Natural := Num_Registered_VCs_In_Why3;
   begin

      --  Delete all theories in main so that we start this file with no other
      --  VCs.

      Why_Sections (WF_Main).Theories.Clear;

      case Ekind (E) is
         when Entry_Kind
            | E_Function
            | E_Procedure
         =>
            if Entity_Spec_In_SPARK (E)

              -- Ignore hardcoded subprograms
              and then not Is_Hardcoded_Entity (E)

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
              and then not Is_Derived_Type (E)
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
      if Num_Registered_VCs_In_Why3 > Old_Num then
         declare
            File_Name : constant String :=
              Compute_Why3_File_Name (E, ".gnat-json");
         begin
            Print_Gnat_Json_File (File_Name);
            Run_Gnatwhy3 (File_Name);
         end;
      end if;
   end Do_Generate_VCs;

   ---------------------------
   -- Do_Ownership_Checking --
   ---------------------------

   procedure Do_Ownership_Checking is
   begin
      for E of Entities_To_Translate loop
         --  Set error node so that bugbox information will be correct

         Current_Error_Node := E;
         Borrow_Checker.Check_Entity (E);
      end loop;

      --  If an error was found then print all errors/warnings and return
      --  with an error status.

      if Found_Permission_Error then
         Errout.Finalize (Last_Call => True);
         Errout.Output_Messages;
         Exit_Program (E_Errors);
      end if;
   end Do_Ownership_Checking;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
      E         : constant Entity_Id :=
        Unique_Defining_Entity (Unit (GNAT_Root));

      generic
         with procedure Action (N : Node_Id);
      procedure Process_All_Units;
      --  Call Action on all compilation units analyzed by the frontend. Units
      --  might be processed in an arbitrary order; in particular, it is not
      --  guaranteed that declarations are processed before uses.
      --
      --  Note: originally, we used Sem.Walk_Library_Items, but in complicated
      --  chains of generics and inlined calls it was both failing to find a
      --  suitable ordering of units and missing some units that were needed.

      generic
         with procedure Action (N : Node_Id);
      procedure Process_Current_Unit;
      --  Call Action on the spec of the current compilation unit and its body
      --  (if present).

      -----------------------
      -- Process_All_Units --
      -----------------------

      procedure Process_All_Units is
      begin
         --  Standard package is implicitly analysed
         Action (Standard_Package_Node);

         --  Iterate over all other units known to the frontend
         for U in Main_Unit .. Last_Unit loop

            --  Ignore non-compilation units (e.g. .adc configuration files)
            --  and units that were not analysed (e.g. system.ads when it is
            --  implicitly pulled by Ensure_System_Dependency).

            if Present (Cunit (U))
              and then Analyzed (Unit (Cunit (U)))
            then
               Action (Unit (Cunit (U)));
            end if;
         end loop;
      end Process_All_Units;

      --------------------------
      -- Process_Current_Unit --
      --------------------------

      procedure Process_Current_Unit is
         Lib_Unit : constant Node_Id := Library_Unit (GNAT_Root);
      begin
         --  If both spec and body of the current compilation unit are present
         --  then process spec first.
         if Present (Lib_Unit) and then Lib_Unit /= GNAT_Root then
            Action (Unit (Lib_Unit));
         end if;

         --  Then process body (or spec if no body is present)
         Action (Unit (GNAT_Root));
      end Process_Current_Unit;

      procedure Mark_Current_Unit is new Process_Current_Unit
        (Action => Mark_Compilation_Unit);

      procedure Build_Flow_Tree is new Process_Current_Unit
        (Action => Flow_Generated_Globals.Traversal.Build_Tree);

      procedure Rewrite_All_Compilation_Units is new Process_All_Units
        (Action => Rewrite_Compilation_Unit);

      procedure Register_All_Entities is new Process_All_Units
        (Action => Register_Compilation_Unit);

      procedure Register_All_Flow_Scopes is new Process_All_Units
        (Action => Register_Flow_Scopes);

      --  This Boolean indicates whether proof have been attempted anywhere in
      --  the unit.
      Proof_Done : Boolean := False;

   --  Start of processing for GNAT_To_Why

   begin
      Timing_Start (Timing);

      if Is_Generic_Unit (E) then

         --  We do nothing for generic units currently. If this get revised
         --  at some point to provide proof of generics, then the special
         --  SPARK expansion in the frontend should be applied to generic
         --  units as well.

         if not Gnat2Why_Args.Global_Gen_Mode then

            --  Issue warning if analyzing specific units with -u switch, but
            --  the main entity in the compilation unit is generic.

            if Gnat2Why_Args.Limit_Units then
               Error_Msg_N
                 ("?generic compilation unit is not analyzed",
                  GNAT_Root);
               Error_Msg_N
                 ("\?only instantiations of the generic will be analyzed",
                  GNAT_Root);
            end if;
         end if;

         return;
      end if;

      --  Allow the generation of new nodes and lists, which might happen when
      --  marking implicitly referenced entities, e.g. System.Priority.

      Atree.Unlock;
      Nlists.Unlock;
      Sem.Scope_Stack.Locked := False;
      Lib.Unlock;

      --  Create an implicit state for memory (de)allocation. It needs to be
      --  before rewriting, where we might refer to this abstract state.

      Flow.Dynamic_Memory.Create_Heap_State;

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Flow visibility info needs to be build before the GG traversal
      --  (which relies on visibility for deciding variable input in constant
      --  declarations) and marking (which relies on visibility for deciding
      --  the default initialization).

      Register_All_Flow_Scopes;
      Connect_Flow_Scopes;

      Mark_Standard_Package;

      --  Mark the current compilation unit as "in SPARK / not in SPARK".

      Mark_Current_Unit;

      Timing_Phase_Completed (Timing, "marking");

      --  Finalize has to be called before we call Compilation_Errors.
      Finalize (Last_Call => False);

      if Compilation_Errors
        or else Gnat2Why_Args.Check_Mode
      then
         return;
      end if;

      --  Build hierarchical representation of scopes in the current
      --  compilation unit. This may require two traversals: for spec and body.

      Build_Flow_Tree;

      if Gnat2Why_Args.Global_Gen_Mode then

         Generate_Globals (GNAT_Root);
         Timing_Phase_Completed (Timing, "globals (partial)");

      else
         --  Issue warning if analyzing specific units with -u switch, but the
         --  main entity in the compilation unit is not marked in SPARK. It may
         --  still be that an enclosed package/subprogram is marked in SPARK.
         --  Reflect that in the warning message.

         --  If both the spec and body units are available, then GNAT_Root is
         --  the entity for the body. We want to issue a warning if this entity
         --  is neither marked in SPARK nor out of SPARK.

         --  If only the spec unit is available, then GNAT_Root is the entity
         --  for the spec. We want to issue a warning if this entity is neither
         --  marked in SPARK nor out of SPARK.

         declare
            Root : constant Entity_Id := Defining_Entity (Unit (GNAT_Root));
         begin
            if Gnat2Why_Args.Limit_Units
              and then No (SPARK_Pragma (Root))
            then
               Error_Msg_N
                 ("?SPARK_Mode not applied to this compilation unit",
                  GNAT_Root);
               Error_Msg_N
                 ("\?only enclosed declarations with SPARK_Mode"
                  & " will be analyzed",
                  GNAT_Root);
            end if;
         end;

         --  Register mappings from entity names to entity ids
         Register_All_Entities;

         --  Populate a table with ALI files which is used in GG_Read
         --  (which needs to be called even if --no-global-generation switch
         --  is used to get non-global effects, like potentially blocking and
         --  termination statuses).
         --
         --  This functionality should be moved out of Compute_Global_Effects
         Prescan_ALI_Files;
         Timing_Phase_Completed (Timing, "globals (basic)");

         --  Read the generated globals from the ALI files
         GG_Read (GNAT_Root);
         Timing_Phase_Completed (Timing, "globals/properties (advanced)");

         --  Do some flow analysis

         Flow_Analyse_CUnit (GNAT_Root);
         Generate_Assumptions;
         Timing_Phase_Completed (Timing, "flow analysis");

         --  Perform the new SPARK checking rules for pointer aliasing. This is
         --  only activated on SPARK code. The debug flag -gnatdF is used to
         --  deactivate the new pointer rules.

         if not Debug_Flag_FF then
            Do_Ownership_Checking;
         end if;

         --  Start the translation to Why

         if not Gnat2Why_Args.Check_All_Mode
           and then not Gnat2Why_Args.Flow_Analysis_Mode
         then
            Proof_Done := True;
            Load_Codepeer_Results;
            Timing_Phase_Completed (Timing, "codepeer results");

            Why.Gen.Names.Initialize;
            Why.Atree.Modules.Initialize;
            Init_Why_Sections;
            Timing_Phase_Completed (Timing, "init_why_sections");

            Translate_Standard_Package;
            Timing_Phase_Completed (Timing, "translation of standard");

            Translate_CUnit;

            --  After printing the .mlw files the memory consumed by the
            --  Why3 AST is no longer needed; give it back to OS, so that
            --  provers can use it.

            Why.Atree.Tables.Free;

            Collect_Results;
            --  If the analysis is requested for a specific piece of code, we
            --  do not warn about useless pragma Annotate, because it's likely
            --  to be a false positive.

            if Gnat2Why_Args.Limit_Line = Null_Unbounded_String
              and then Gnat2Why_Args.Limit_Region = Null_Unbounded_String
              and then Gnat2Why_Args.Limit_Subp = Null_Unbounded_String
            then
               Generate_Useless_Pragma_Annotate_Warnings;
            end if;

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
      Ada.Environment_Variables.Set
        (Name  => "GNATCOV_TRACE_FILE",
         Value =>
           Ada.Directories.Compose
             (Name      => Unit_Name & (if Gnat2Why_Args.Global_Gen_Mode
                                        then "_phase1"
                                        else "_phase2"),
              Extension => "srctrace"));

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
      --  For now we allow the -g/-O/-f/-m/-W/-w, -nostdlib, -pipe and
      --  -save-temps/-save-temps=.. switches, even though they will have no
      --  effect. This permits compatibility with existing scripts.

      return
        Is_Switch (Switch)
          and then (Switch (First) in 'f' | 'g' | 'm' | 'O' | 'W' | 'w'
                    or else Switch (First .. Last) = "nostdlib"
                    or else Switch (First .. Last) = "pipe"
                    or else
                      (Switch'Length >= 10
                       and then Switch (First .. First + 9) = "save-temps"));
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

       and then not Is_Simple_Shift_Or_Rotate (E)

       --  Ignore hardcoded subprograms

       and then not Is_Hardcoded_Entity (E));

   ----------------------------
   --  Print_Gnat_Json_File  --
   ----------------------------

   procedure Print_Gnat_Json_File (Filename : String) is
      use Why_Node_Lists;
      Modules : constant Why_Node_Lists.List := Build_Printing_Plan;
      Json_File : constant JSON_Value := Create_Object;
      Json_Decls : JSON_Value;
      C : Why_Node_Lists.Cursor;
   begin

      if Modules.Is_Empty then
         --  Construct Json from theories
         Json_Decls := Create (Empty_Array);
         for WF in W_Section_Id loop
            --  If there was a procedure
            --    GNATCOLL.JSON.Append (Arr : in out JSON_Array;
            --                          Arr1 : JSON_Array);
            --  we could just do
            --    Append (Json, Why_Node_Lists_List_To_Json
            --                    (Why_Sections (WF).Theories));
            --  but helas!
            C := First (Why_Sections (WF).Theories);
            while Has_Element (C) loop
               Append (Json_Decls, Why_Node_To_Json (Get_Node (Element (C))));
               Next (C);
            end loop;
         end loop;
      else
         --  Construct Json from printing plan
         Json_Decls := Why_Node_Lists_List_To_Json (Modules);
      end if;

      Set_Field (Json_File, "theory_declarations", Json_Decls);

      --  Output to file
      Open_Current_File (Filename);
      P (Current_File, Write (Json_File, Compact => False));
      Close_Current_File;
   end Print_Gnat_Json_File;

   ------------------
   -- Run_Gnatwhy3 --
   ------------------

   procedure Run_Gnatwhy3 (Filename : String) is
      use Ada.Directories;
      use Ada.Containers;
      Fn        : constant String := Compose (Current_Directory, Filename);
      Old_Dir   : constant String := Current_Directory;
      Why3_Args : String_Lists.List := Gnat2Why_Args.Why3_Args;
      Command   : GNAT.OS_Lib.String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path (Why3_Args.First_Element);
   begin

      --  If the maximum is reached, we wait for one process to finish first

      if Output_File_Map.Length = Max_Subprocesses then
         Collect_One_Result;
      end if;

      --  modifying the command line and printing it for debug purposes. We
      --  need to append the file first, then print the debug output, because
      --  this corresponds to the actual command line run, and finally remove
      --  the first argument, which is the executable name.

      Why3_Args.Append (Fn);

      if Gnat2Why_Args.Debug_Mode then
         for Elt of Why3_Args loop
            Ada.Text_IO.Put (Elt);
            Ada.Text_IO.Put (" ");
         end loop;
         Ada.Text_IO.New_Line;
      end if;

      Why3_Args.Delete_First (1);

      Set_Directory (To_String (Gnat2Why_Args.Why3_Dir));

      --  We need to capture stderr of gnatwhy3 output in case of Out_Of_Memory
      --  messages.

      declare
         Fd   : File_Descriptor;
         Name : Path_Name_Type;
         Pid  : Process_Id;
      begin
         Create_Temp_File (Fd, Name);
         pragma Assert (Fd /= Invalid_FD);
         Pid :=
           GNAT.OS_Lib.Non_Blocking_Spawn
             (Program_Name           => Command.all,
              Args                   =>
                Call.Argument_List_Of_String_List (Why3_Args),
              Output_File_Descriptor => Fd,
              Err_To_Out             => True);
         pragma Assert (Pid /= Invalid_Pid);
         Output_File_Map.Insert (Pid, Name);
         Close (Fd);
      end;
      Set_Directory (Old_Dir);
      Free (Command);
   end Run_Gnatwhy3;

   ---------------------
   -- Translate_CUnit --
   ---------------------

   procedure Translate_CUnit is

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id));
      --  Traversal procedure to process entities which need translation

      procedure Generate_VCs (E : Entity_Id);
      --  Check if E is in main unit and then generate VCs

      procedure Register_Symbol (E : Entity_Id);
      --  Some entities are registered globally in the symbol table. We do this
      --  upfront, so that we do not depend too much on the order of the list
      --  of entities.

      ----------------------
      -- For_All_Entities --
      ----------------------

      procedure For_All_Entities
        (Process : not null access procedure (E : Entity_Id))
      is
      begin
         for E of Entities_To_Translate loop

            --  Set error node so that bugbox information will be correct

            Current_Error_Node := E;
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
         then
            case Analysis_Status'
              (Analysis_Requested (E, With_Inlined => False))
            is
               when Analyzed =>
                  Do_Generate_VCs (E);

               --  This subprogram is only analyzed contextually. In the case
               --  that it is referenced without being called (by taking its
               --  address for example) or if all calls are in non-SPARK code,
               --  the subprogram may not be analyzed at all. Warn the user if
               --  --info is set.

               when Contextually_Analyzed =>
                  if Debug.Debug_Flag_Underscore_F then
                     Error_Msg_NE
                       ("info: ?local subprogram &" &
                          " only analyzed in the context of calls", E, E);
                     Error_Msg_N
                       ("\add a contract to" &
                          " analyze it separately from calling contexts", E);
                  end if;

               when Not_In_Analyzed_Files
                  | Not_The_Analyzed_Subprogram
               =>
                  null;
            end case;
         end if;
      end Generate_VCs;

      ---------------------
      -- Register_Symbol --
      ---------------------

      procedure Register_Symbol (E : Entity_Id) is
      begin
         case Ekind (E) is
            when E_Entry
               | E_Function
               | E_Procedure =>
               if Is_Translated_Subprogram (E) then
                  if Ekind (E) in E_Function | E_Procedure then
                     Ada_Ent_To_Why.Insert
                       (Symbol_Table, E, Mk_Item_Of_Entity (E));
                  else
                     Insert_Entity (E, To_Why_Id (E, Typ => Why_Empty));
                  end if;
               end if;
            when Object_Kind =>

               if Is_Discriminal (E)
                 or else Is_Protected_Component_Or_Discr_Or_Part_Of (E)
               then
                  return;
               end if;

               if not Is_Mutable_In_Why (E) then
                  Insert_Entity (E,
                                 To_Why_Id (E, No_Comp => True,
                                            Typ => Type_Of_Node (Etype (E))));
               else
                  Insert_Item (E, Mk_Item_Of_Entity (E));
               end if;

            when others =>
               null;
         end case;
      end Register_Symbol;

   --  Start of processing for Translate_CUnit

   begin
      --  Translation of the __HEAP is hardcoded into the
      --  _gnatprove_standard.Main module.
      Translated_Object_Names.Insert
        (To_Entity_Name (SPARK_Xrefs.Name_Of_Heap_Variable));

      --  Store information for entities

      For_All_Entities (Store_Information_For_Entity'Access);

      For_All_Entities (Register_Symbol'Access);

      --  Translate Ada entities into Why3

      For_All_Entities (Translate_Entity'Access);

      --  For all objects whose declaration is not visible (has not been
      --  translated to Why), we generate a dummy declaration. This must
      --  be done after translating above entities.

      For_All_Entities (Translate_Hidden_Globals'Access);

      For_All_Entities (Complete_Declaration'Access);

      --  Generate VCs for entities of unit. This must follow the generation of
      --  modules for entities, so that all completions for deferred constants
      --  and expression functions are defined.

      For_All_Entities (Generate_VCs'Access);

      --  Clear global data that is no longer be needed to leave more memory
      --  for solvers.
      Translated_Object_Names.Clear;
      Translated_Object_Names.Reserve_Capacity (0);
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

               Translate_Type (File, E);
            end if;

         when Object_Kind =>

            --  Ignore discriminals, i.e. objects that occur for discriminants
            --  of record types, protected types, and task types.

            if Is_Discriminal (E) then
               return;
            end if;

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

            --  We translate private constants of access type in the partial
            --  declaration. This should avoid translating them twice (in the
            --  partial and full view). The following case represents these
            --  objects because they are considered as mutable while they are
            --  constants and may have a partial and full view. We chose the
            --  partial view bacause the full view may not be in SPARK.

            elsif Is_Full_View (E) then
               pragma Assert (Ekind (E) = E_Constant);

            else
               Translate_Variable (File, E);
               Generate_Empty_Axiom_Theory (File, E);
            end if;

         --  Generate a logic function for Ada subprograms

         when E_Entry
            | E_Function
            | E_Procedure
         =>
            if Is_Translated_Subprogram (E) then
               Translate_Subprogram_Spec (File, E);
            end if;

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

   ------------------------------
   -- Translate_Hidden_Globals --
   ------------------------------

   procedure Translate_Hidden_Globals (E : Entity_Id) is
      Unused_Node : Node_Sets.Cursor;
      Unused_Name : Name_Sets.Cursor;
      Inserted    : Boolean;

   begin
      if (case Ekind (E) is
          when Entry_Kind | E_Task_Type => True,
          when E_Function | E_Procedure => Is_Translated_Subprogram (E),
          when others                   => False
      --  For packages we don't translate objects from the RHS of their
      --  (generated) Initializes contract, because such objects are either
      --  visible (and thus translated anyway) or are pulled by subprograms
      --  called from the Initial_Condition (and thus already translated).
      )
      then
         declare
            Reads  : Flow_Types.Flow_Id_Sets.Set;
            Writes : Flow_Types.Flow_Id_Sets.Set;
         begin
            --  Collect global variables potentially read and written
            Flow_Utility.Get_Proof_Globals (Subprogram      => E,
                                            Reads           => Reads,
                                            Writes          => Writes,
                                            Erase_Constants => True);

            Reads.Union (Writes);

            for G of Reads loop
               if G.Kind = Magic_String then
                  pragma Assert (Is_Opaque_For_Proof (G));

                  Translated_Object_Names.Insert
                    (New_Item => G.Name,
                     Position => Unused_Name,
                     Inserted => Inserted);

                  if Inserted then
                     Translate_External_Object (G.Name);
                  end if;
               end if;
            end loop;
         end;
      end if;
   end Translate_Hidden_Globals;

   --------------------------------
   -- Translate_Standard_Package --
   --------------------------------

   procedure Translate_Standard_Package is

      procedure Translate_Standard_Entity (E : Entity_Id)
      with Pre => Is_Type (E);
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

   --  Start of processing for Translate_Standard_Package

   begin
      for S_Type in S_Types loop
         declare
            E : constant Entity_Id := Standard_Entity (S_Type);

         begin
            if Entity_In_SPARK (E) then
               Translate_Standard_Entity (E);
            end if;
         end;
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
