------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
--              Copyright (C) 2014-2023, Capgemini Engineering              --
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
with Ada.Text_IO;                     use Ada.Text_IO;
with ALI.Util;                        use ALI.Util;
with ALI;                             use ALI;
with Assumption_Types;                use Assumption_Types;
with Atree;                           use Atree;
with Binderr;
with Call;                            use Call;
with CE_RAC;                          use CE_RAC;
with Common_Containers;               use Common_Containers;
with Debug;                           use Debug;
with Debug.Timing;                    use Debug.Timing;
with Einfo.Entities;                  use Einfo.Entities;
with Einfo.Utils;                     use Einfo.Utils;
with Errout;                          use Errout;
with Flow;                            use Flow;
with Flow.Analysis.Assumptions;       use Flow.Analysis.Assumptions;
with Flow_Error_Messages;             use Flow_Error_Messages;
with Flow_Generated_Globals.Phase_1;
with Flow_Generated_Globals.Traversal;
with Flow_Generated_Globals.Phase_2;  use Flow_Generated_Globals.Phase_2;
with Flow_Types;                      use Flow_Types;
with Flow_Utility;                    use Flow_Utility;
with Flow_Visibility;                 use Flow_Visibility;
with GNAT.OS_Lib;                     use GNAT.OS_Lib;
with GNAT.SHA1;
with GNAT.Source_Info;
with GNATCOLL.JSON;                   use GNATCOLL.JSON;
with GNATCOLL.Utils;
with Gnat2Why.Assumptions;            use Gnat2Why.Assumptions;
with Gnat2Why.Borrow_Checker;         use Gnat2Why.Borrow_Checker;
with Gnat2Why.Data_Decomposition;     use Gnat2Why.Data_Decomposition;
with Gnat2Why.Decls;                  use Gnat2Why.Decls;
with Gnat2Why.Error_Messages;         use Gnat2Why.Error_Messages;
with Gnat2Why_Opts;                   use Gnat2Why_Opts;
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
with Sinfo.Nodes;                     use Sinfo.Nodes;
with Sinput;                          use Sinput;
with SPARK_Definition.Annotate;       use SPARK_Definition.Annotate;
with SPARK_Definition;                use SPARK_Definition;
with SPARK_Register;                  use SPARK_Register;
with SPARK_Rewrite;                   use SPARK_Rewrite;
with SPARK_Util;                      use SPARK_Util;
with SPARK_Util.Hardcoded;            use SPARK_Util.Hardcoded;
with SPARK_Util.Subprograms;          use SPARK_Util.Subprograms;
with SPARK_Util.Types;                use SPARK_Util.Types;
with SPARK_Xrefs;
with Stand;                           use Stand;
with String_Utils;                    use String_Utils;
with Switch;                          use Switch;
with Tempdir;                         use Tempdir;
with VC_Kinds;                        use VC_Kinds;
with Why;                             use Why;
with Why.Atree.Modules;               use Why.Atree.Modules;
with Why.Atree.To_Json;               use Why.Atree.To_Json;
with Why.Atree.Tables;                use Why.Atree.Tables;
with Why.Gen.Binders;                 use Why.Gen.Binders;
with Why.Gen.Expr;                    use Why.Gen.Expr;
with Why.Gen.Names;
with Why.Inter;                       use Why.Inter;
with Why.Images;                      use Why.Images;

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

   procedure Do_Ownership_Checking (Error_Found : out Boolean);
   --  Perform SPARK access legality checking

   procedure Print_GNAT_Json_File (Filename : String);
   --  Print the GNAT AST as Json into file

   procedure Create_JSON_File (Progress    : Analysis_Progress;
                               Stop_Reason : Stop_Reason_Type);
   --  At the very end, write the analysis results into file. Progress
   --  describes the last analysis done. Stop_Reason indicates why the
   --  analysis did not progress to the next phase.

   function Get_Skip_Proof_JSON return JSON_Array;
   --  Return a list of entities for which proof was skipped.

   function Get_Skip_Flow_And_Proof_JSON return JSON_Array;
   --  Return a list of entities for which flow and proof was skipped.

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

   procedure Run_Gnatwhy3 (E : Entity_Id; Filename : String)
   with Pre => Output_File_Map.Length <= Max_Subprocesses and then Present (E);
   --  After generating the Why file, run the proof tool. Wait for existing
   --  gnatwhy3 processes to finish if Max_Subprocesses is already reached.

   Max_Why3_Filename_Length : constant := 64;
   --  On windows, a path can be no longer than 250 or so chars. We allow a
   --  maximum of 64 (60 chars + 4 four the file extension) for the
   --  why3 file to maximize the number of chars users have for their own
   --  project structure.

   function Compute_Why3_File_Name
     (E         : Entity_Id;
      Extension : String)
      return String
   with
     Post => Compute_Why3_File_Name'Result'Length <= Max_Why3_Filename_Length;
   --  Compute the why3 file to be used. Guarantees to be no longer than
   --  Max_Why3_Filename_Length and makes some effort to still be unique.

   ------------------------
   -- Collect_One_Result --
   ------------------------

   procedure Collect_One_Result
   is
      Pid     : Process_Id;
      Success : Boolean;
      pragma Warnings (Off, Success); --  modified but then not referenced
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
               if Is_Expression_Function_Or_Completion (E)
                 and then Entity_Body_Compatible_With_SPARK (E)
               then
                  Translate_Expression_Function_Body (E);
               else
                  Generate_Subprogram_Completion (E);
               end if;
            end if;

         when Type_Kind =>
            pragma Assert (Entity_In_SPARK (E));

            if Retysp (E) = E
              and then not Is_Standard_Boolean_Type (E)
              and then E /= Universal_Fixed
            then
               Generate_Type_Completion (E);
            end if;

         when others =>
            null;
      end case;
   end Complete_Declaration;

   ----------------------------
   -- Compute_Why3_File_Name --
   ----------------------------

   function Compute_Why3_File_Name
     (E         : Entity_Id;
      Extension : String)
      return String
   is
      S : constant String := Full_Name (E);
      Digest_Length : constant := 20;
      --  Arbitrary number of digits that we take from the SHA1 digest to
      --  achieve uniqueness.
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

   procedure Create_JSON_File (Progress    : Analysis_Progress;
                               Stop_Reason : Stop_Reason_Type) is
      FD : Ada.Text_IO.File_Type;
      File_Name : constant String :=
        Ada.Directories.Compose
          (Name      => Unit_Name,
           Extension => VC_Kinds.SPARK_Suffix);
      Full : constant JSON_Value := Create_Object;
   begin
      Set_Field (Full, "spark", Get_SPARK_JSON);
      Set_Field (Full, "skip_flow_proof", Get_Skip_Flow_And_Proof_JSON);
      Set_Field (Full, "skip_proof", Get_Skip_Proof_JSON);
      Set_Field
        (Full, "progress", Create (Analysis_Progress'Image (Progress)));
      Set_Field
        (Full, "stop_reason", Create (Stop_Reason_Type'Image (Stop_Reason)));
      if Progress >= Progress_Flow then
         Set_Field (Full, "flow", Create (Get_Flow_JSON));
      end if;
      if Progress >= Progress_Proof then
         Set_Field (Full, "pragma_assume", Create (Get_Pragma_Assume_JSON));
         Set_Field (Full, "session_map", Get_Session_Map_JSON);
         Set_Field (Full, "proof", Create (Get_Proof_JSON));
      end if;
      Set_Field (Full, "assumptions", Get_Assume_JSON);

      Set_Field (Full, "timings", Timing_History (Timing));
      Set_Field (Full, "entities", Entity_Table);

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
      --  Check that the global variables are cleared before and after this
      --  routine; this is an assertion rather than a pre/post condition,
      --  because the caller shouldn't really care about it.

      pragma Assert (No (Current_Subp));

      --  Delete all theories in main so that we start this file with no other
      --  VCs.

      Why_Sections (WF_Main).Clear;

      if Has_Skip_Proof_Annotation (E) then
         Skipped_Proof.Insert (E);
         return;
      end if;

      case Ekind (E) is
         when Entry_Kind
            | E_Function
            | E_Procedure
         =>
            if Entity_Spec_In_SPARK (E)

              --  Ignore hardcoded subprograms
              and then not Is_Hardcoded_Entity (E)

              --  Ignore invariant procedures and default initial conditions
              and then not Subprogram_Is_Ignored_For_Proof (E)
            then
               declare
                  LSP_Applies : constant Boolean :=
                    Is_Dispatching_Operation (E) and then
                    Present (Find_Dispatching_Type (E));
               begin
                  if LSP_Applies then
                     Ada_Ent_To_Why.Push_Scope (Symbol_Table);
                     Update_Symbol_Table_For_Inherited_Contracts (E);
                  end if;

                  --  Generate Why3 code to check absence of run-time errors in
                  --  contracts and body.

                  Generate_VCs_For_Subprogram (E);

                  --  Generate Why3 code to check LSP for primitive of tagged
                  --  types.

                  if LSP_Applies then
                     Generate_VCs_For_LSP (E);
                     Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
                  end if;
               end;
            end if;
            Timing_Phase_Completed (Timing,
                                    Entity_To_Subp_Assumption (E),
                                    "gnat2why.vc_generation");

         when E_Package =>
            Generate_VCs_For_Package_Elaboration (E);

         when Type_Kind =>

            if Ekind (E) in E_Protected_Type | E_Task_Type
              and then Entity_Spec_In_SPARK (E)
              and then not Is_Derived_Type (E)
            then
               case Ekind (E) is
                  when E_Protected_Type =>
                     Generate_VCs_For_Protected_Type (E);

                  when E_Task_Type =>
                     Generate_VCs_For_Task_Type (E);

                  when others =>
                     raise Program_Error;
               end case;
            elsif Entity_Spec_In_SPARK (Enclosing_Unit (E))
              and then E = Retysp (E)
            then
               Generate_VCs_For_Type (E);
            end if;

         when others =>
            raise Program_Error;
      end case;
      if Num_Registered_VCs_In_Why3 > Old_Num then
         declare
            File_Name : constant String :=
              Compute_Why3_File_Name (E, ".gnat-json");
         begin
            Print_GNAT_Json_File (File_Name);
            Run_Gnatwhy3 (E, File_Name);
         end;
      end if;

      Current_Subp := Empty;
   end Do_Generate_VCs;

   ---------------------------
   -- Do_Ownership_Checking --
   ---------------------------

   procedure Do_Ownership_Checking (Error_Found : out Boolean) is
   begin
      for E of Entities_To_Translate loop
         --  Set error node so that bugbox information will be correct

         Current_Error_Node := E;
         Borrow_Checker.Check_Entity (E);
      end loop;

      --  If an error was found then print all errors/warnings and return
      --  with an error status.

      Error_Found := Found_Permission_Error;
   end Do_Ownership_Checking;

   -----------------
   -- GNAT_To_Why --
   -----------------

   procedure GNAT_To_Why (GNAT_Root : Node_Id) is
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

      --  Local variables

      E : constant Entity_Id := Unique_Defining_Entity (Unit (GNAT_Root));
      --  Unique entity of the current compilation unit

      Progress : Analysis_Progress := Progress_None;
      --  Indicates whether proof have been attempted anywhere in the unit

      Stop_Reason : Stop_Reason_Type := Stop_Reason_None;

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

         --  Generate dummy GG section in the ALI file, because GPRbuild
         --  machinery uses it to detect corrupted dependencies.

         if Gnat2Why_Args.Global_Gen_Mode then
            Flow_Generated_Globals.Phase_1.GG_Write_Initialize (GNAT_Root);
            Flow_Generated_Globals.Phase_1.GG_Write_Finalize;
         end if;

         Stop_Reason := Stop_Reason_Generic_Unit;
         goto Leave_With_JSON;
      end if;

      --  Allow the generation of new nodes and lists, which might happen when
      --  marking implicitly referenced entities, e.g. System.Priority.

      Atree.Unlock;
      Nlists.Unlock;
      Sem.Scope_Stack.Locked := False;
      Lib.Unlock;

      --  Initialize and check statically (in ghost code) tabled values for the
      --  nth roots of the modulus of machine integers.

      Why.Gen.Expr.Initialize_Tables_Nth_Roots;

      --  Before any analysis takes place, perform some rewritings of the tree
      --  that facilitates analysis.

      Rewrite_All_Compilation_Units;

      --  Flow visibility info needs to be build before the GG traversal
      --  (which relies on visibility for deciding variable input in constant
      --  declarations) and marking (which relies on visibility for deciding
      --  the default initialization).

      Register_All_Flow_Scopes;
      Connect_Flow_Scopes;

      --  The remaining steps depend on phase. In particular, in phase 1
      --  marking is done before flow, while in phase 2 it is done after flow.
      --  Common steps are intentionally duplicated to keep the sequence clear.

      if Gnat2Why_Args.Global_Gen_Mode then

         --  Mark the current compilation unit as "in SPARK / not in SPARK"
         Mark_Standard_Package;
         Mark_Current_Unit;

         Timing_Phase_Completed (Timing, Null_Subp, "marking");

         --  Finalize has to be called before we call Compilation_Errors
         Finalize (Last_Call => False);

         if Compilation_Errors
           or else Gnat2Why_Args.Mode = GPM_Check
         then
            goto Leave;
         end if;

         --  Build hierarchical representation of scopes in the current
         --  compilation unit.
         --
         --  Also, pick constants with variable inputs. This is affected by the
         --  SPARK status of expressions in their initial values, so must be
         --  done after marking.

         Build_Flow_Tree;

         Generate_Globals (GNAT_Root);
         Timing_Phase_Completed (Timing, Null_Subp, "globals (partial)");

      else
         --  Issue warning if analyzing specific units with -u switch, but the
         --  main entity in the compilation unit is not marked in SPARK. It may
         --  still be that an enclosed package/subprogram is marked in SPARK.
         --  Reflect that in the warning message.

         --  If both the spec and body units are available, then GNAT_Root is
         --  the entity for the body. We want to issue a warning if this entity
         --  is neither marked in SPARK nor out of SPARK.

         --  If only the spec unit is available, then GNAT_Root is the entity
         --  for the spec. We want to issue an info message if this entity is
         --  neither marked in SPARK nor out of SPARK.

         declare
            Root : constant Entity_Id := Defining_Entity (Unit (GNAT_Root));
         begin
            if Gnat2Why_Args.Limit_Units
              and then No (SPARK_Pragma (Root))
            then
               Error_Msg_N
                 ("info: ?SPARK_Mode not applied to this compilation unit",
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
         Timing_Phase_Completed (Timing, Null_Subp, "globals (basic)");

         --  Build hierarchical representation of scopes in the current
         --  compilation unit.

         Build_Flow_Tree;

         --  Read the generated globals from the ALI files

         GG_Resolve;
         Timing_Phase_Completed (Timing, Null_Subp, "globals (advanced)");

         --  Read data decomposition info from the JSON file created by calling
         --  the compiler with -gnatR2js, when the compiler for the selected
         --  Target and Runtime is available.
         Read_Data_Decomposition_JSON_File;

         --  Mark the current compilation unit as "in SPARK / not in SPARK"
         Mark_Standard_Package;
         Mark_Current_Unit;

         Timing_Phase_Completed (Timing, Null_Subp, "marking");
         Progress := Progress_Marking;

         --  Finalize has to be called before we call Compilation_Errors
         Finalize (Last_Call => False);

         if Compilation_Errors
           or else Gnat2Why_Args.Mode = GPM_Check
         then
            Stop_Reason :=
              (if Compilation_Errors then Stop_Reason_Error_Marking
               else Stop_Reason_Check_Mode);
            goto Leave_With_JSON;
         end if;

         GG_Complete (GNAT_Root);
         Timing_Phase_Completed (Timing, Null_Subp, "properties (advanced)");

         --  Do some flow analysis

         declare
            Errors : Boolean;
         begin
            Flow_Analyse_CUnit (GNAT_Root, Errors);
            Progress := Progress_Flow;
            if Errors then
               Stop_Reason := Stop_Reason_Error_Flow;
               goto Leave_With_JSON;
            end if;
         end;

         Generate_Assumptions;
         Timing_Phase_Completed (Timing, Null_Subp, "flow analysis");

         --  Check SPARK rules for pointer aliasing. This is only activated on
         --  SPARK code.

         declare
            Errors : Boolean;
         begin
            Do_Ownership_Checking (Errors);

            --  In case of an error in borrow checking, we downgrade the
            --  progress to borrow. From a user point of view, borrow-checking
            --  is more fundamental than flow analysis, even though the tool
            --  does flow analysis first.

            if Errors then
               Progress := Progress_Borrow;
               Stop_Reason := Stop_Reason_Error_Borrow;
               goto Leave_With_JSON;
            end if;
         end;

         if Gnat2Why_Args.Debug_Exec_RAC then

            --  Store information for entities

            for E of Entities_To_Translate loop

               --  Set error node so that bugbox information will be correct

               Current_Error_Node := E;
               Store_Information_For_Entity (E);
            end loop;

            declare

               function Assertion (VC : VC_Kind) return String is
                 (case VC is
                     when VC_Assert => "ADA.ASSERTIONS.ASSERTION_ERROR",
                     when others    => VC_Kind'Image (VC));
               --  Return the name of the assertion that is triggered for at
               --  the given VC.

               Res : constant Result := CE_RAC.RAC_Execute
                 (Unique_Main_Unit_Entity,
                  VC_Kinds.Cntexample_File_Maps.Empty,
                  Do_Sideeffects => True);
            begin
               case Res.Res_Kind is
                  when Res_Normal =>
                     null;
                  when Res_Failure =>
                     Put_Line (Standard_Error, "");
                     Put_Line
                       (Standard_Error,
                        "raised " & Assertion (Res.Res_VC_Kind) &
                          " : " & File_Name (Sloc (Res.Res_Node)) &
                          ":" & GNATCOLL.Utils.Image
                          (Integer (Get_Logical_Line_Number
                           (Sloc (Res.Res_Node))), 0));
                  when Res_Incomplete =>
                     Put_Line
                       (Standard_Error,
                        "RAC incomplete: " & To_String (Res.Res_Reason));
                  when Res_Stuck | Res_Not_Executed =>
                     pragma Assert (False);
               end case;
            end;
            return;
         end if;

         --  Start the translation to Why

         if Gnat2Why_Args.Mode not in GPM_Check_All | GPM_Flow then
            Why.Gen.Names.Initialize;
            Why.Atree.Modules.Initialize;
            Init_Why_Sections;
            Timing_Phase_Completed (Timing, Null_Subp, "init_why_sections");

            Translate_Standard_Package;
            Timing_Phase_Completed (Timing, Null_Subp,
                                    "translation of standard");

            Translate_CUnit;

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

            Progress := Progress_Proof;

         else
            Stop_Reason := (if Gnat2Why_Args.Mode = GPM_Check_All
                            then Stop_Reason_Check_Mode
                            else Stop_Reason_Flow_Mode);
         end if;
      end if;

      <<Leave_With_JSON>>

      --  Flow analysis is run during check all mode, but we should not mark it
      --  as complete. So we downgrade the progress here in this case.

      if not Gnat2Why_Args.Global_Gen_Mode then
         if Gnat2Why_Args.Mode = GPM_Check_All
           and then Progress = Progress_Flow
         then
            Progress := Progress_Marking;
         end if;
         Create_JSON_File (Progress, Stop_Reason);
      end if;

      <<Leave>>

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

   -------------------
   -- Get_Skip_JSON --
   -------------------

   function Get_Skip_Flow_And_Proof_JSON return JSON_Array is
      Result : JSON_Array := Empty_Array;
   begin
      for Elt of Skipped_Flow_And_Proof loop
         Append (Result, To_JSON (Entity_To_Subp_Assumption (Elt)));
      end loop;
      return Result;
   end Get_Skip_Flow_And_Proof_JSON;

   -------------------
   -- Get_Skip_JSON --
   -------------------

   function Get_Skip_Proof_JSON return JSON_Array is
      Result : JSON_Array := Empty_Array;
   begin
      for Elt of Skipped_Proof loop
         Append (Result, To_JSON (Entity_To_Subp_Assumption (Elt)));
      end loop;
      return Result;
   end Get_Skip_Proof_JSON;

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

       --  Ignore simple shifts and rotates

       and then Is_Simple_Shift_Or_Rotate (E) not in N_Op_Shift

       --  Ignore hardcoded subprograms

       and then not Is_Hardcoded_Entity (E));

   --------------------------
   -- Print_GNAT_Json_File --
   --------------------------

   procedure Print_GNAT_Json_File (Filename : String) is
      Modules    : constant Why_Node_Lists.List := Build_Printing_Plan;
      Json_File  : constant JSON_Value := Create_Object;
      Json_Decls : constant JSON_Value :=
        Why_Node_Lists_List_To_Json (Modules);
   begin
      Set_Field (Json_File, "theory_declarations", Json_Decls);

      --  Output to file
      Open_Current_File (Filename);
      P (Current_File, Write (Json_File, Compact => True));
      Close_Current_File;
   end Print_GNAT_Json_File;

   ------------------
   -- Run_Gnatwhy3 --
   ------------------

   procedure Run_Gnatwhy3 (E : Entity_Id; Filename : String) is
      use Ada.Directories;
      use Ada.Containers;
      Fn        : constant String := Compose (Current_Directory, Filename);
      Old_Dir   : constant String := Current_Directory;
      Why3_Args : String_Lists.List := Gnat2Why_Args.Why3_Args;
      Command   : GNAT.OS_Lib.String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path (Why3_Args.First_Element);
   begin
      --  If the maximum is reached, or we are not allowed to run gnatwhy3 in
      --  parallel, we wait for one process to finish first.

      if Output_File_Map.Length = Max_Subprocesses
        or else (not Output_File_Map.Is_Empty
                 and then not Gnat2Why_Args.Parallel_Why3)
      then
         Collect_One_Result;
      end if;

      Why3_Args.Append ("--entity");
      Why3_Args.Append (Img (E));
      --  Modifying the command line and printing it for debug purposes. We
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
         Args : Argument_List :=
           Call.Argument_List_Of_String_List (Why3_Args);
         Fd   : File_Descriptor;
         Name : Path_Name_Type;
         Pid  : Process_Id;

      begin
         Create_Temp_File (Fd, Name);
         pragma Assert (Fd /= Invalid_FD);
         Pid :=
           GNAT.OS_Lib.Non_Blocking_Spawn
             (Program_Name           => Command.all,
              Args                   => Args,
              Output_File_Descriptor => Fd,
              Err_To_Out             => True);

         --  If spawning fails, for whatever reason, then simply crash

         if Pid = Invalid_Pid then
            raise Program_Error with "can't spawn gnatwhy3";
         end if;

         Output_File_Map.Insert (Pid, Name);
         Close (Fd);

         for Arg of Args loop
            Free (Arg);
         end loop;
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
                  Ada_Ent_To_Why.Insert
                    (Symbol_Table, E, Mk_Item_Of_Entity (E));
               end if;
            when Object_Kind =>

               if Is_Discriminal (E)
                 or else Is_Protected_Component_Or_Discr_Or_Part_Of (E)
                 or else (Ekind (E) = E_Constant
                          and then Is_Partial_View (E)
                          and then Entity_In_SPARK (Full_View (E)))
               then
                  return;
               end if;

               Insert_Item (E, Mk_Item_Of_Entity (E));

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

      --  Declare distinct constants for all Ada exceptions

      Translate_Exceptions;

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
      Check_Safe_Guard_Cycles;

      --  Clear global data that is no longer be needed to leave more memory
      --  for solvers.
      Translated_Object_Names.Clear;
      Translated_Object_Names.Reserve_Capacity (0);

      Why.Gen.Names.Free;
      Why.Atree.Tables.Free;
   end Translate_CUnit;

   ----------------------
   -- Translate_Entity --
   ----------------------

   procedure Translate_Entity (E : Entity_Id) is

      procedure Generate_Empty_Axiom_Theory (E : Entity_Id);
      --  Generates an empty theory for the axiom related to E. This is done
      --  for every entity for which there is no axiom theory generated, so
      --  that modules for VC generation can consistently include the axiom
      --  theory of all they entities they use.

      ---------------------------------
      -- Generate_Empty_Axiom_Theory --
      ---------------------------------

      procedure Generate_Empty_Axiom_Theory (E : Entity_Id)
      is
         Th : Theory_UC;
      begin
         Th := Open_Theory
           (WF_Context, E_Axiom_Module (E),
            Comment =>
              "Module giving an empty axiom for the entity "
            & """" & Get_Name_String (Chars (E)) & """"
            & (if Sloc (E) > 0 then
                 " defined at " & Build_Location_String (Sloc (E))
              else "")
            & ", created in " & GNAT.Source_Info.Enclosing_Entity);
         Close_Theory (Th,
                       Kind => Standalone_Theory);
      end Generate_Empty_Axiom_Theory;

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

               Translate_Type (E);
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
                     Translate_Constant (E);
                     if not Entity_In_SPARK (Full_View (E)) then
                        Generate_Empty_Axiom_Theory (E);
                     end if;
                  elsif Is_Full_View (E) then
                     Translate_Constant_Value (E);
                  else
                     Translate_Constant (E);
                     Translate_Constant_Value (E);
                  end if;
               else
                  Translate_Constant (E);
                  Generate_Empty_Axiom_Theory (E);
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
               Translate_Variable (E);
               Generate_Empty_Axiom_Theory (E);
            end if;

         --  Generate a logic function for Ada subprograms

         when E_Entry
            | E_Function
            | E_Procedure
         =>
            if Is_Translated_Subprogram (E) then
               Translate_Subprogram_Spec (E);
            end if;

         when E_Loop =>
            Translate_Loop_Entity (E);
            Generate_Empty_Axiom_Theory (E);

         when E_Package =>
            null;

         when others =>
            raise Program_Error;
      end case;
   end Translate_Entity;

   ------------------------------
   -- Translate_Hidden_Globals --
   ------------------------------

   procedure Translate_Hidden_Globals (E : Entity_Id) is
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
            Reads       : Flow_Types.Flow_Id_Sets.Set;
            Writes      : Flow_Types.Flow_Id_Sets.Set;
            Unused_Name : Name_Sets.Cursor;
            Inserted    : Boolean;
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
