------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Containers;        use Ada.Containers;
with Ada.IO_Exceptions;
with Ada.Strings.Fixed;     use Ada.Strings.Fixed;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Unchecked_Deallocation;
with GNATCOLL.Opt_Parse;
with GNATCOLL.Strings;
with GNATCOLL.Tribooleans;
with GNATCOLL.VFS;          use GNATCOLL.VFS;
with GNAT.Command_Line;     use GNAT.Command_Line;
with GNAT.Directory_Operations;
with GNAT.Expect;
with GNAT.OS_Lib;
with GNAT.Regpat;           use GNAT.Regpat;
with GNAT.Strings;          use GNAT.Strings;
with GPR2.Build.Source;
with GPR2.Build.View_Db;
with GPR2.Log;
with GPR2.Message;
with GPR2.Options;
with GPR2.Options.Opt_Parse;
with GPR2.Project.Attribute;
with GPR2.Project.Attribute_Index;
with GPR2.Project.Registry.Attribute;
with GPR2.Project.Registry.Attribute.Description;
with GPR2.Project.Registry.Exchange;
with GPR2.Project.Registry.Pack;
with GPR2.Project.Registry.Pack.Description;
with GPR2.Reporter.Console;

with Platform;     use Platform;
with Proof_Options;
with SPARK2014VSN; use SPARK2014VSN;
with System.Multiprocessors;
with TOML;
with TOML.File_IO;

package body Configuration is

   use type Gnat2Why_Opts.Writing.Gnat2Why_Phase;

   Invalid_Level   : constant := -1;
   Invalid_Steps   : constant := -1;
   Invalid_Timeout : constant := -1;

   Usage_Message : constant String := "-Pproj [switches] [-cargs switches]";
   --  Used to print part of the help message for gnatprove

   package Manifest_Maps is new
     Ada.Containers.Indefinite_Hashed_Maps
       (Key_Type        => String,
        Element_Type    => Manifest_Subprogram_Vectors.Vector,
        Hash            => Ada.Strings.Hash,
        Equivalent_Keys => "=",
        "="             => Manifest_Subprogram_Vectors."=");

   --  Private global state to replace public state from CL_Switches
   Debug_Save_VCs      : Boolean := False;
   Debug_Prover_Errors : Boolean := False;
   File_List           : String_Lists.List;
   Replay              : Boolean := False;
   Proof_Manifest_Path : GNAT.Strings.String_Access;
   Proof_Manifest_Maps : Manifest_Maps.Map;
   Why3_Conf           : GNAT.Strings.String_Access;
   Why3_Debug          : GNAT.Strings.String_Access;
   Why3_Logging        : Boolean := False;
   Z3_Counterexample   : Boolean := False;

   type Spark_Reporter is new GPR2.Reporter.Console.Object with null record;

   overriding
   procedure Internal_Report
     (Self : in out Spark_Reporter; Message : GPR2.Message.Object);

   procedure Abort_Msg (Msg : String; With_Help : Boolean)
   with No_Return;
   --  Stop the program, output the message and the help message when
   --  requested, then exit.

   procedure Clean_Up (Tree : Project.Tree.Object);
   --  Deletes generated "gnatprove" sub-directories in all object directories
   --  of the project.

   function Compute_Socket_Dir (Tree : Project.Tree.Object) return String;
   --  Returns the directory where the socket file will be created. On
   --  Windows, this is irrelevant, so the function returns the empty string.
   --  On Unix, the following rules are applied:
   --  - if TMPDIR is set, exists and is writable, use that
   --  - if /tmp exists and is writable, use that
   --  - otherwise return the object directory.

   procedure Handle_Warning_Switches (Switch, Value : String);
   --  Handle the "-W", "-A", "-D" switches (related to warnings) as well as
   --  the "--pedantic" switch. The first three switches are always followed by
   --  a warning tag name (parameter "Value"). This function checks if "Value"
   --  is a valid tag name if the switch is one of those three.
   --  Meaning of the switches:
   --  - "-W" means the warning corresponding to the tag should be
   --    issued/enabled (W for "warn")
   --  - "-A" means the corresponding warning should be disabled
   --    (A for "allow")
   --  - "-D" means the corresponding warning should be an error (D for "deny")
   --  - --pedantic is equivalent to "-W" for the warnings that belong to the
   --    "pedantic" subkind. See vc_kinds.ads.
   --  The intention for "--pedantic" is to issue warnings on features that
   --  could cause portability issues with other compilers than GNAT. For
   --  example, issue a warning when the Ada RM allows reassociation of
   --  operators in an expression (something GNAT never does), which could
   --  lead to different overflows, e.g. on
   --    A + B + C
   --  which is parsed as
   --    (A + B) + C
   --  but could be reassociated by another compiler as
   --    A + (B + C)

   function No_Project_File_Mode return String;
   --  This function is supposed to be called when no project file was given.
   --  It searches for project files in the current directory:
   --  - If there is no such file, a default project is created and the name of
   --    that project is returned.
   --  - If there is exactly one, it returns the name of this project file.
   --  - If there is more than one, it aborts with an error.

   procedure Load_Proof_Manifest;
   --  Parse the proof manifest directory designated by --proof-manifest-dir,
   --  if any.

   function Manifest_Unit_Name (File : String) return String;
   --  Unit name represented by File when used as a manifest or source file

   function Proof_Manifest_For_Unit
     (Unit_Name : String) return Manifest_Subprogram_Vectors.Vector;
   --  Return the proof-manifest entries relevant to Unit_Name

   procedure Prepare_Prover_Lib (Obj_Dir : String);
   --  Deal with the why3 libraries manual provers might need.
   --  Copies needed sources into gnatprove and builds the library.
   --  For the moment, only Coq is handled.

   procedure Sanitize_File_List (Tree : Project.Tree.Object);
   --  Apply the following rules to each name in [File_List]:
   --    if the name refers to a valid unit, replace with the file name of the
   --      body (or spec if there is no body)
   --    if the file is a body, do nothing;
   --    if the file is a spec, and a body exists, replace by filename of body
   --    if the file is a separate, replace with filename of body
   --  This is required to avoid calling gnat2why on a separate body (will
   --  crash) or on a spec when there is a body (gnat2why will incorrectly
   --  assume that there is no body).
   --  At the same time we check if the unit/file name is unique in the case of
   --  an aggregate project. If it is not, an error is issued.

   procedure Sanity_Check_SARIF_Base_URI (Tree : Project.Tree.Object);
   --  Validate each entry in CL_Switches.SARIF_Base_URIs (must have the form
   --  <id>:<path>). If no entry provides the %SRCROOT% identifier, append a
   --  default one rooted at the project's root directory.

   procedure Produce_Version_Output;
   --  Print the version of gnatprove, why3 and shipped provers

   procedure Produce_List_Categories_Output;
   --  List information for all messages issued by the tool

   procedure Produce_Explain_Output (Explain_Code : String);
   --  Print the explanation for the requested error/warning code

   procedure Produce_List_Explain_Codes_Output;
   --  List all explain codes with their one-line descriptions on standard
   --  output, derived from the Explain_Code_Kind enumeration. Internal switch
   --  (exercised by the explain codes test), not advertised to users.

   function Check_gnateT_Switch (View : Project.View.Object) return String;
   --  Try to compute the gnateT switch to be used for gnat2why. If there is
   --  a target and runtime set, but we can't compute the switch, a warning
   --  is issued.

   procedure Check_File_Part_Of_Project
     (View : Project.View.Object; Fn : String);
   --  Raise an error if the file FN is not part of the project

   procedure Check_Duplicate_Bodies (Msg : GPR2.Message.Object);
   --  Raise an error if the message is about duplicate bodies.

   --  There are more than one "command lines" in gnatprove. For example, the
   --  project file defines switches that act as if they were appended to the
   --  command line, and can also define switches for each file. Therefore,
   --  there are several passes of command line parsing. The Parsing_Modes
   --  type and the Parse_Switches procedure define the allowed switches in
   --  each of these passes.
   --  Overall there are these passes:
   --    - the "real" command line is scanned to find the project file (-P) and
   --      other switches that change project file loading (this happens in
   --      mode Project_Parsing below);
   --    - the "global" command line (that is the real command line plus the
   --      switches defined in the project file) is parsed (mode All_Switches
   --      below);
   --    - the command line for each file is parsed (also mode All_Switches);
   --    - the switches attributes in the project file are checked for switches
   --      that are not allowed in this context (modes Global_Switches_Only,
   --      File_Specific_Only).

   type Parsing_Modes is
     (All_Switches,
      --  accepts all switches

      Global_Switches_Only,
      --  Global_Switches_Only only accepts switches that can be put in the
      --  'for Switches' or 'for Proof_Switches ("Ada")' section of the project
      --  file (for example, not switches that may impact project parsing).

      File_Specific_Only
      --  File_Specific_Only - only accept switches that can be put in the
      --  'for Proof_Switches ("file")' section of the project file. This
      --  excludes most switches except --timeout, --steps, etc.
     );

   --  Switch ids are deliberately ordered by their future semantic layer.
   --  Keep invocation-level switches and file-specific switches contiguous so
   --  that later parser storage can use array subtypes over these ranges.
   type Switch_Id is
     (Sw_Assumptions,
      Sw_Benchmark,
      Sw_Checks_As_Errors,
      Sw_CWE,
      Sw_D,
      Sw_Debug_Disable_Prover_Feedback,
      Sw_Debug_No_Cache_Output,
      Sw_Debug_Save_VCs,
      Sw_Dbg_No_Sem,
      Sw_Debug_Prover_Errors,
      Sw_Exclude_Line,
      Sw_Flow_Debug,
      Sw_Flow_Show_GG,
      Sw_F,
      Sw_IDE_Progress_Bar,
      Sw_J,
      Sw_K,
      Sw_Limit_Line,
      Sw_Limit_Lines,
      Sw_Limit_Name,
      Sw_Limit_Region,
      Sw_Limit_Subp,
      Sw_Memcached_Server,
      Sw_M,
      Sw_No_Axiom_Guard,
      Sw_Function_Sandboxing,
      Sw_No_Global_Generation,
      Sw_No_Subprojects,
      Sw_Output,
      Sw_Output_Header,
      Sw_Output_Msg_Only,
      Sw_Q,
      Sw_Replay,
      Sw_Report,
      Sw_U,
      Sw_UU,
      Sw_V,
      Sw_Warnings,
      Sw_Why3_Conf,
      Sw_Why3_Debug,
      Sw_Why3_Logging,
      Sw_Why3_Server,
      Sw_SARIF_Base_URI,
      Sw_Z3_Counterexample,
      Sw_Gnattest_Values,
      Sw_Debug_Exec_RAC,
      Sw_Proof_Manifest,

      Sw_Level,
      Sw_Memlimit,
      Sw_Counterexamples,
      Sw_Check_Counterexamples,
      Sw_Mode,
      Sw_No_Counterexample,
      Sw_No_Inlining,
      Sw_No_Loop_Unrolling,
      Sw_Proof,
      Sw_Proof_Warnings,
      Sw_Proof_Warn_Timeout,
      Sw_Prover,
      Sw_Steps,
      Sw_CE_Steps,
      Sw_Timeout,
      Sw_Info,
      Sw_Pedantic,
      Sw_Warn_Enable,
      Sw_Warn_Disable,
      Sw_Warn_Error);

   subtype Invocation_Switch_Id is
     Switch_Id range Sw_Assumptions .. Sw_Proof_Manifest;
   subtype File_Specific_Switch_Id is
     Switch_Id range Sw_Level .. Sw_Warn_Error;

   type Switch_Layer is (Invocation_Layer, File_Specific_Layer);

   type Switch_Value_Kind is
     (Flag_Value, Integer_Value, String_Value, String_List_Value);

   type String_Ref is access constant String;

   type Switch_Metadata is record
      Short      : String_Ref := null;
      Long       : String_Ref := null;
      Value_Kind : Switch_Value_Kind;
      Layer      : Switch_Layer;
   end record;

   function Make_Switch_Metadata
     (Value_Kind : Switch_Value_Kind;
      Layer      : Switch_Layer;
      Short      : String_Ref := null;
      Long       : String_Ref := null) return Switch_Metadata
   is ((Short      => Short,
        Long       => Long,
        Value_Kind => Value_Kind,
        Layer      => Layer));
   --  Defining this function with default arguments allows us to drop "others"
   --  field in the below aggregate definition.

   Switch_Definitions : constant array (Switch_Id) of Switch_Metadata :=
     [Sw_Assumptions                   =>
        Make_Switch_Metadata
          (Long       => new String'("--assumptions"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Benchmark                     =>
        --  Undocumented switch for fake prover binaries in benchmarks
        Make_Switch_Metadata
          (Long       => new String'("--benchmark"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Checks_As_Errors              =>
        Make_Switch_Metadata
          (Long       => new String'("--checks-as-errors"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_CWE                           =>
        Make_Switch_Metadata
          (Long       => new String'("--cwe"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_D                             =>
        Make_Switch_Metadata
          (Short      => new String'("-d"),
           Long       => new String'("--debug"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Debug_Disable_Prover_Feedback =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-disable-prover-feedback"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Debug_No_Cache_Output         =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-no-cache-output"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Debug_Save_VCs                =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-save-vcs"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Dbg_No_Sem                    =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-no-semaphore"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Debug_Prover_Errors           =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-prover-errors"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Exclude_Line                  =>
        Make_Switch_Metadata
          (Long       => new String'("--exclude-line"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Flow_Debug                    =>
        Make_Switch_Metadata
          (Long       => new String'("--flow-debug"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Flow_Show_GG                  =>
        Make_Switch_Metadata
          (Long       => new String'("--flow-show-gg"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_F                             =>
        Make_Switch_Metadata
          (Short      => new String'("-f"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_IDE_Progress_Bar              =>
        Make_Switch_Metadata
          (Long       => new String'("--ide-progress-bar"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_J                             =>
        Make_Switch_Metadata
          (Short      => new String'("-j"),
           Value_Kind => Integer_Value,
           Layer      => Invocation_Layer),
      Sw_K                             =>
        Make_Switch_Metadata
          (Short      => new String'("-k"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Limit_Line                    =>
        Make_Switch_Metadata
          (Long       => new String'("--limit-line"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Limit_Lines                   =>
        Make_Switch_Metadata
          (Long       => new String'("--limit-lines"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Limit_Name                    =>
        Make_Switch_Metadata
          (Long       => new String'("--limit-name"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Limit_Region                  =>
        Make_Switch_Metadata
          (Long       => new String'("--limit-region"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Limit_Subp                    =>
        Make_Switch_Metadata
          (Long       => new String'("--limit-subp"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Memcached_Server              =>
        Make_Switch_Metadata
          (Long       => new String'("--memcached-server"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_M                             =>
        Make_Switch_Metadata
          (Short      => new String'("-m"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_No_Axiom_Guard                =>
        Make_Switch_Metadata
          (Long       => new String'("--no-axiom-guard"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Function_Sandboxing           =>
        Make_Switch_Metadata
          (Long       => new String'("--function-sandboxing"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_No_Global_Generation          =>
        Make_Switch_Metadata
          (Long       => new String'("--no-global-generation"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_No_Subprojects                =>
        Make_Switch_Metadata
          (Long       => new String'("--no-subprojects"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Output                        =>
        Make_Switch_Metadata
          (Long       => new String'("--output"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Output_Header                 =>
        Make_Switch_Metadata
          (Long       => new String'("--output-header"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Output_Msg_Only               =>
        Make_Switch_Metadata
          (Long       => new String'("--output-msg-only"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Q                             =>
        Make_Switch_Metadata
          (Short      => new String'("-q"),
           Long       => new String'("--quiet"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Replay                        =>
        Make_Switch_Metadata
          (Long       => new String'("--replay"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Report                        =>
        Make_Switch_Metadata
          (Long       => new String'("--report"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_U                             =>
        Make_Switch_Metadata
          (Short      => new String'("-u"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_UU                            =>
        Make_Switch_Metadata
          (Short      => new String'("-U"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_V                             =>
        Make_Switch_Metadata
          (Short      => new String'("-v"),
           Long       => new String'("--verbose"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Warnings                      =>
        Make_Switch_Metadata
          (Long       => new String'("--warnings"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Why3_Conf                     =>
        Make_Switch_Metadata
          (Long       => new String'("--why3-conf"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Why3_Debug                    =>
        Make_Switch_Metadata
          (Long       => new String'("--why3-debug"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Why3_Logging                  =>
        Make_Switch_Metadata
          (Long       => new String'("--why3-logging"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Why3_Server                   =>
        Make_Switch_Metadata
          (Long       => new String'("--why3-server"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_SARIF_Base_URI                =>
        Make_Switch_Metadata
          (Long       => new String'("--sarif-base-uri"),
           Value_Kind => String_List_Value,
           Layer      => Invocation_Layer),
      Sw_Z3_Counterexample             =>
        Make_Switch_Metadata
          (Long       => new String'("--z3-counterexample"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Gnattest_Values               =>
        Make_Switch_Metadata
          (Long       => new String'("--gnattest-values"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Debug_Exec_RAC                =>
        Make_Switch_Metadata
          (Long       => new String'("--debug-exec-rac"),
           Value_Kind => Flag_Value,
           Layer      => Invocation_Layer),
      Sw_Proof_Manifest                =>
        Make_Switch_Metadata
          (Long       => new String'("--proof-manifest-dir"),
           Value_Kind => String_Value,
           Layer      => Invocation_Layer),
      Sw_Level                         =>
        Make_Switch_Metadata
          (Long       => new String'("--level"),
           Value_Kind => Integer_Value,
           Layer      => File_Specific_Layer),
      Sw_Memlimit                      =>
        Make_Switch_Metadata
          (Long       => new String'("--memlimit"),
           Value_Kind => Integer_Value,
           Layer      => File_Specific_Layer),
      Sw_Counterexamples               =>
        Make_Switch_Metadata
          (Long       => new String'("--counterexamples"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Check_Counterexamples         =>
        Make_Switch_Metadata
          (Long       => new String'("--check-counterexamples"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Mode                          =>
        Make_Switch_Metadata
          (Long       => new String'("--mode"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_No_Counterexample             =>
        Make_Switch_Metadata
          (Long       => new String'("--no-counterexample"),
           Value_Kind => Flag_Value,
           Layer      => File_Specific_Layer),
      Sw_No_Inlining                   =>
        Make_Switch_Metadata
          (Long       => new String'("--no-inlining"),
           Value_Kind => Flag_Value,
           Layer      => File_Specific_Layer),
      Sw_No_Loop_Unrolling             =>
        Make_Switch_Metadata
          (Long       => new String'("--no-loop-unrolling"),
           Value_Kind => Flag_Value,
           Layer      => File_Specific_Layer),
      Sw_Proof                         =>
        Make_Switch_Metadata
          (Long       => new String'("--proof"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Proof_Warnings                =>
        Make_Switch_Metadata
          (Long       => new String'("--proof-warnings"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Proof_Warn_Timeout            =>
        Make_Switch_Metadata
          (Long       => new String'("--proof-warnings-timeout"),
           Value_Kind => Integer_Value,
           Layer      => File_Specific_Layer),
      Sw_Prover                        =>
        Make_Switch_Metadata
          (Long       => new String'("--prover"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Steps                         =>
        Make_Switch_Metadata
          (Long       => new String'("--steps"),
           Value_Kind => Integer_Value,
           Layer      => File_Specific_Layer),
      Sw_CE_Steps                      =>
        Make_Switch_Metadata
          (Long       => new String'("--ce-steps"),
           Value_Kind => Integer_Value,
           Layer      => File_Specific_Layer),
      Sw_Timeout                       =>
        Make_Switch_Metadata
          (Long       => new String'("--timeout"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Info                          =>
        Make_Switch_Metadata
          (Long       => new String'("--info"),
           Value_Kind => Flag_Value,
           Layer      => File_Specific_Layer),
      Sw_Pedantic                      =>
        Make_Switch_Metadata
          (Long       => new String'("--pedantic"),
           Value_Kind => Flag_Value,
           Layer      => File_Specific_Layer),
      Sw_Warn_Enable                   =>
        Make_Switch_Metadata
          (Short      => new String'("-W"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Warn_Disable                  =>
        Make_Switch_Metadata
          (Short      => new String'("-A"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer),
      Sw_Warn_Error                    =>
        Make_Switch_Metadata
          (Short      => new String'("-D"),
           Value_Kind => String_Value,
           Layer      => File_Specific_Layer)];

   pragma
     Assert
       ((for all Switch in Invocation_Switch_Id =>
           Switch_Definitions (Switch).Layer = Invocation_Layer));
   pragma
     Assert
       ((for all Switch in File_Specific_Switch_Id =>
           Switch_Definitions (Switch).Layer = File_Specific_Layer));

   type Switch_Value (Kind : Switch_Value_Kind := Flag_Value) is record
      case Kind is
         when Flag_Value =>
            Boolean_Val : Boolean := False;

         when Integer_Value =>
            Integer_Val : Integer := 0;

         when String_Value =>
            String_Val : GNAT.Strings.String_Access := null;

         when String_List_Value =>
            String_List_Val : String_Lists.List;
      end case;
   end record;
   --  Record holding the value for a switch.

   type Switch_Value_Array is array (Switch_Id) of Switch_Value
   with
     Predicate =>
       (for all Id in Switch_Id =>
          Switch_Definitions (Id).Value_Kind = Switch_Value_Array (Id).Kind);

   type Switch_Presence_Array is array (Switch_Id) of Boolean;

   function Initial_Switch_Value (Switch : Switch_Id) return Switch_Value;
   --  Return a default value for all Switches

   function Switch_Values_Have_Expected_Kinds
     (Values : Switch_Value_Array) return Boolean
   is ((for all Switch in Switch_Id =>
          Values (Switch).Kind = Switch_Definitions (Switch).Value_Kind));
   --  Check that switch definitions and the value array have compatible types

   type Parsed_Switches is record
      Values         : Switch_Value_Array :=
        [for Switch in Switch_Id => Initial_Switch_Value (Switch)];
      Present        : Switch_Presence_Array := [others => False];
      File_List      : String_Lists.List;
      Warning_Status : Opt_Warning_Status_Array := [others => WS_None];
   end record;

   type Parsed_Switches_Access is access all Parsed_Switches;
   --  GNAT.Command_Line Handle_Switch callback doesn't allow extra user data,
   --  so we need to use a global access value.

   Current_Parsed_Switches : Parsed_Switches_Access := null;
   --  Temporary target for GNAT.Command_Line callbacks during Parse_Switches

   procedure Copy_To_CL_Switches (Parsed : in out Parsed_Switches);
   --  Copy parsed switch values into CL_Switches for existing consumers

   procedure Merge_Parsed_Switches
     (Base : in out Parsed_Switches; Over : Parsed_Switches);
   --  Merge Over onto Base using command-line precedence semantics

   procedure Handle_Switch
     (Switch : String; Parameter : String; Section : String);
   --  Deal with switches that are not automatic

   function Find_Switch
     (Spelling : String; Switch : out Switch_Id) return Boolean;
   --  Return the switch id with Short or Long spelling equal to Spelling

   function Parse_Switches_Internal
     (Mode : Parsing_Modes; Com_Lin : String_List) return Parsed_Switches;
   --  Parse the command line switches according to the provided mode into
   --  internal storage.

   type Project_Parsing_Result is record
      Opt                : GPR2.Options.Object;
      Version            : Boolean := False;
      Help               : Boolean := False;
      List_Categories    : Boolean := False;
      Gpr_Registry       : Boolean := False;
      Clean              : Boolean := False;
      Explain            : Unbounded_String := Null_Unbounded_String;
      List_Explain_Codes : Boolean := False;
      Verbosity          : Verbosity_Choice := Normal_Level;
      Cargs              : String_List_Access := null;
      Remaining_Args     : String_List_Access := null;
   end record;

   function Parse_Switches_Before_Project_Parsing
     (Com_Lin : String_List) return Project_Parsing_Result;
   --  Parse the command line, but only for switches that are relevant before
   --  loading the project. This includes switches that influence project
   --  loading, as well as switches that trigger an immediate output and exit,
   --  such as --version.

   procedure Set_Project_Attributes;
   --  Inform GPR API about gnatprove-specific project attributes

   procedure Display_Help;

   subtype String_Access is GNAT.OS_Lib.String_Access;

   ---------------
   -- Abort_Msg --
   ---------------

   procedure Abort_Msg (Msg : String; With_Help : Boolean) is
   begin
      if Msg /= "" then
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      end if;
      if With_Help then
         Display_Help;
      else
         Ada.Text_IO.Put_Line
           ("Try ""gnatprove --help"" for more information.");
      end if;
      Fail ("");
   end Abort_Msg;

   ------------------
   -- Artifact_Dir --
   ------------------

   function Artifact_Dir
     (Tree : GPR2.Project.Tree.Object) return Path_Name.Object is
   begin
      if Tree.Root_Project.Kind in GPR2.With_Object_Dir_Kind then
         --  we don't need to add "gnatprove" here as we configured the project
         --  with the correct subdir option.
         return Tree.Root_Project.Object_Directory;
      else
         return
           Path_Name.Compose
             (Tree.Root_Project.Dir_Name, "gnatprove", Directory => True);
      end if;
   end Artifact_Dir;

   ----------------------
   -- Source_Full_Path --
   ----------------------

   function Source_Full_Path
     (Tree : GPR2.Project.Tree.Object; Simple : String) return String is
   begin
      for NRP of Tree.Namespace_Root_Projects loop
         if NRP.Kind in GPR2.With_Object_Dir_Kind then
            declare
               View_DB   : constant GPR2.Build.View_Db.Object :=
                 Tree.Artifacts_Database (NRP);
               Ambiguous : Boolean;
            begin
               if View_DB.Source_Option > GPR2.No_Source then
                  declare
                     Src : constant GPR2.Build.Source.Object :=
                       View_DB.Visible_Source
                         (GPR2.Simple_Name (Simple), Ambiguous);
                  begin
                     if Src.Is_Defined then
                        return Src.Path_Name.String_Value;
                     end if;
                  end;
               end if;
            end;
         end if;
      end loop;
      return "";
   end Source_Full_Path;

   -----------------------
   -- File_Specific_Key --
   -----------------------

   function File_Specific_Key
     (Unit : GPR2.Build.Compilation_Unit.Object) return String is
   begin
      return Unit.Main_Part.Source.String_Value;
   end File_Specific_Key;

   ------------------------
   -- Manifest_Unit_Name --
   ------------------------

   function Manifest_Unit_Name (File : String) return String is
      Name   : constant String :=
        Ada.Characters.Handling.To_Lower (Ada.Directories.Base_Name (File));
      Result : String := Name;
   begin
      for C of Result loop
         if C = '-' then
            C := '.';
         end if;
      end loop;

      return Result;
   end Manifest_Unit_Name;

   ----------------------------
   -- Check_Duplicate_Bodies --
   ----------------------------

   procedure Check_Duplicate_Bodies (Msg : GPR2.Message.Object) is
      use type GPR2.Message.Level_Value;
   begin
      if Msg.Level = GPR2.Message.Warning
        and then Contains (Msg.Message, "does not match source name")
      then
         Abort_Msg
           ("Stopping analysis due incorrectly named source files",
            With_Help => False);
      end if;
   end Check_Duplicate_Bodies;

   ---------------------
   -- Internal_Report --
   ---------------------

   overriding
   procedure Internal_Report
     (Self : in out Spark_Reporter; Message : GPR2.Message.Object) is
   begin
      GPR2.Reporter.Console.Object (Self).Internal_Report (Message);
      Check_Duplicate_Bodies (Message);
   end Internal_Report;

   --------------------------------
   -- Check_File_Part_Of_Project --
   --------------------------------

   procedure Check_File_Part_Of_Project
     (View : Project.View.Object; Fn : String) is
   begin
      if not View.Has_Source (GPR2.Simple_Name (Fn)) then
         Abort_Msg
           ("file "
            & Fn
            & " of attribute Proof_Switches "
            & "is not part of the project",
            With_Help => False);
      end if;
   end Check_File_Part_Of_Project;

   -------------------------
   -- Check_gnateT_Switch --
   -------------------------

   function Check_gnateT_Switch (View : Project.View.Object) return String is
   begin
      --  Check first if the target is not the native one, which is available
      --  as Project.Tree.Target_Name, that we have to normalize first. There
      --  is nothing to check for the native target.

      if View.Tree.Is_Cross_Target then
         --  User has already set the attribute, don't try anything smart
         if Has_gnateT_Switch (View) then
            return "";
         end if;

         if View.Tree.Runtime (Ada_Language) /= "" then
            declare
               RT_Attr : constant Project.Attribute.Object :=
                 View.Attribute
                   (Project.Registry.Attribute.Runtime_Dir,
                    Index =>
                      GPR2.Project.Attribute_Index.Create (GPR2.Ada_Language));
            begin
               if RT_Attr.Is_Defined then
                  declare
                     Targ_Prop_File : constant String :=
                       Ada.Directories.Compose
                         (RT_Attr.Value.Text, "ada_target_properties");
                  begin
                     if Ada.Directories.Exists (Targ_Prop_File) then
                        return "-gnateT=" & Targ_Prop_File;
                     end if;
                  end;
               end if;
            end;
         end if;

         --  If we reached here, there *should* be a target properties
         --  file, but we can't find it and the user didn't add one. Print
         --  a warning.

         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "warning: attribute ""Target"" of your project file is "
            & "only used to determine runtime library");
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "warning: to specify target properties, specify option "
            & """-gnateT"" using ""Builder.Global_Compilation_Switches""");
      end if;
      return "";
   end Check_gnateT_Switch;

   --------------
   -- Clean_Up --
   --------------

   procedure Clean_Up (Tree : Project.Tree.Object) is

      procedure Clean_Up_One_Directory (Dir : Virtual_File);
      --  Remove a generated "gnatprove" sub-directory

      ----------------------------
      -- Clean_Up_One_Directory --
      ----------------------------

      procedure Clean_Up_One_Directory (Dir : Virtual_File) is
         Name_Dir : constant String := +Base_Dir_Name (Dir);
         Rm_Dir   : constant String := Dir.Display_Full_Name;

      begin
         --  Directory might not exist, for example if there are no source
         --  files and no explicit object directory is specified. Do nothing
         --  in that case.

         if Dir /= GNATCOLL.VFS.No_File then
            pragma Assert (Name_Dir = Gnat2Why_Opts.Writing.Name_GNATprove);
            if GNAT.OS_Lib.Is_Directory (Rm_Dir) then
               if Verbosity = Verbose_Level then
                  Ada.Text_IO.Put ("Deleting directory " & Rm_Dir & "...");
               end if;
               GNAT.Directory_Operations.Remove_Dir
                 (Rm_Dir, Recursive => True);
               if Verbosity = Verbose_Level then
                  Ada.Text_IO.Put_Line (" done");
               end if;
            end if;
         end if;
      exception
         when GNAT.Directory_Operations.Directory_Error =>
            if Verbosity = Verbose_Level then
               Ada.Text_IO.Put_Line (" failed, please delete manually");
            end if;
      end Clean_Up_One_Directory;

   begin
      for Cursor in
        Tree.Iterate
          (Kind   =>
             [Project.I_Project       => True,
              Project.I_Runtime       => False,
              Project.I_Configuration => False,
              Project.I_Recursive     => True,
              others                  => False],
           Status =>
             [GPR2.Project.S_Externally_Built => GNATCOLL.Tribooleans.False])
      loop
         declare
            View : constant Project.View.Object :=
              Project.Tree.Element (Cursor);
         begin
            if View.Kind in With_Object_Dir_Kind then
               Clean_Up_One_Directory (View.Object_Directory.Virtual_File);
            end if;
            if View.Is_Library then
               Clean_Up_One_Directory (View.Library_Directory.Virtual_File);
               --  ??? This folder does not include the subdir apparently
               Clean_Up_One_Directory
                 (View.Library_Ali_Directory.Virtual_File);
            end if;
         end;
      end loop;
   end Clean_Up;

   ------------------------
   -- Compute_Socket_Dir --
   ------------------------

   function Compute_Socket_Dir (Tree : Project.Tree.Object) return String is

      TMPDIR_Envvar : constant String := "TMPDIR";
      --  It's OK to use a forward slash here, this will be used on Unix only

      TMP_Dir : constant String := "/tmp";

      function Exists_And_Is_Writable (Dir : String) return Boolean;
      --  Check whether the argument is a directory that exists and is writable

      ----------------------------
      -- Exists_And_Is_Writable --
      ----------------------------

      function Exists_And_Is_Writable (Dir : String) return Boolean is
      begin
         return
           Ada.Directories.Exists (Dir)
           and then GNAT.OS_Lib.Is_Write_Accessible_File (Dir);
      end Exists_And_Is_Writable;

   begin
      if Get_OS_Flavor in X86_Windows | X86_64_Windows then
         return "";
      end if;
      if Ada.Environment_Variables.Exists (TMPDIR_Envvar)
        and then
          Exists_And_Is_Writable
            (Ada.Environment_Variables.Value (TMPDIR_Envvar))
      then
         return Ada.Environment_Variables.Value (TMPDIR_Envvar);
      elsif Exists_And_Is_Writable (TMP_Dir) then
         return TMP_Dir;
      else
         return Artifact_Dir (Tree).String_Value;
      end if;
   end Compute_Socket_Dir;

   ---------------------------
   -- Merge_Parsed_Switches --
   ---------------------------

   procedure Merge_Parsed_Switches
     (Base : in out Parsed_Switches; Over : Parsed_Switches)
   is
      procedure Append_List
        (Source : String_Lists.List; Target : in out String_Lists.List);
      --  Append Source to Target

      procedure Copy_String
        (Source : GNAT.Strings.String_Access;
         Target : in out GNAT.Strings.String_Access);
      --  Replace Target with a copy of Source

      -----------------
      -- Append_List --
      -----------------

      procedure Append_List
        (Source : String_Lists.List; Target : in out String_Lists.List) is
      begin
         for Element of Source loop
            Target.Append (Element);
         end loop;
      end Append_List;

      -----------------
      -- Copy_String --
      -----------------

      procedure Copy_String
        (Source : GNAT.Strings.String_Access;
         Target : in out GNAT.Strings.String_Access) is
      begin
         if Target /= null then
            Free (Target);
         end if;

         if Source = null then
            Target := null;
         else
            Target := new String'(Source.all);
         end if;
      end Copy_String;

   begin
      for Switch in Switch_Id loop
         case Switch_Definitions (Switch).Value_Kind is
            when Flag_Value        =>
               Base.Values (Switch).Boolean_Val :=
                 Base.Values (Switch).Boolean_Val
                 or else Over.Values (Switch).Boolean_Val;
               Base.Present (Switch) :=
                 Base.Present (Switch) or else Over.Present (Switch);

            when Integer_Value     =>
               if Over.Present (Switch) then
                  Base.Values (Switch).Integer_Val :=
                    Over.Values (Switch).Integer_Val;
                  Base.Present (Switch) := True;
               end if;

            when String_Value      =>
               if Over.Present (Switch) then
                  Copy_String
                    (Over.Values (Switch).String_Val,
                     Base.Values (Switch).String_Val);
                  Base.Present (Switch) := True;
               end if;

            when String_List_Value =>
               if Over.Present (Switch) then
                  Append_List
                    (Over.Values (Switch).String_List_Val,
                     Base.Values (Switch).String_List_Val);
                  Base.Present (Switch) := True;
               end if;
         end case;
      end loop;

      for WK in Misc_Warning_Kind loop
         if Over.Warning_Status (WK) /= WS_None then
            Base.Warning_Status (WK) := Over.Warning_Status (WK);
         end if;
      end loop;

      Append_List (Over.File_List, Base.File_List);
   end Merge_Parsed_Switches;

   ---------------------------
   -- Copy_To_CL_Switches --
   ---------------------------

   procedure Copy_To_CL_Switches (Parsed : in out Parsed_Switches) is
      procedure Copy_List
        (Source : String_Lists.List; Target : in out String_Lists.List);
      --  Replace Target with Source

      procedure Move_String
        (Source : GNAT.Strings.String_Access;
         Target : in out GNAT.Strings.String_Access);
      --  Move Source into Target, using an empty string for absent values

      ---------------
      -- Copy_List --
      ---------------

      procedure Copy_List
        (Source : String_Lists.List; Target : in out String_Lists.List) is
      begin
         Target.Clear;
         for Element of Source loop
            Target.Append (Element);
         end loop;
      end Copy_List;

      -----------------
      -- Move_String --
      -----------------

      procedure Move_String
        (Source : GNAT.Strings.String_Access;
         Target : in out GNAT.Strings.String_Access) is
      begin
         if Target /= null then
            Free (Target);
         end if;

         if Source = null then
            Target := new String'("");
         else
            Target := new String'(Source.all);
         end if;
      end Move_String;

   begin
      --  package-internal global state
      Debug_Save_VCs := Parsed.Values (Sw_Debug_Save_VCs).Boolean_Val;
      Debug_Prover_Errors :=
        Parsed.Values (Sw_Debug_Prover_Errors).Boolean_Val;
      Copy_List (Parsed.File_List, File_List);
      Replay := Parsed.Values (Sw_Replay).Boolean_Val;
      Move_String (Parsed.Values (Sw_Why3_Conf).String_Val, Why3_Conf);
      Move_String (Parsed.Values (Sw_Why3_Debug).String_Val, Why3_Debug);
      Z3_Counterexample := Parsed.Values (Sw_Z3_Counterexample).Boolean_Val;

      --  public global state
      Flow_Extra_Debug := Parsed.Values (Sw_Flow_Debug).Boolean_Val;
      IDE_Mode := Parsed.Values (Sw_IDE_Progress_Bar).Boolean_Val;
      All_Projects := Parsed.Values (Sw_UU).Boolean_Val;
      Continue_On_Error := Parsed.Values (Sw_K).Boolean_Val;
      Force := Parsed.Values (Sw_F).Boolean_Val;

      --  CL_Switches state that's still used
      CL_Switches.Assumptions := Parsed.Values (Sw_Assumptions).Boolean_Val;
      CL_Switches.Benchmark := Parsed.Values (Sw_Benchmark).Boolean_Val;
      CL_Switches.CWE := Parsed.Values (Sw_CWE).Boolean_Val;
      CL_Switches.Debug_Disable_Prover_Feedback :=
        Parsed.Values (Sw_Debug_Disable_Prover_Feedback).Boolean_Val;
      CL_Switches.Debug_No_Cache_Output :=
        Parsed.Values (Sw_Debug_No_Cache_Output).Boolean_Val;
      Move_String
        (Parsed.Values (Sw_Exclude_Line).String_Val, CL_Switches.Exclude_Line);
      CL_Switches.Flow_Show_GG := Parsed.Values (Sw_Flow_Show_GG).Boolean_Val;
      Move_String
        (Parsed.Values (Sw_Limit_Line).String_Val, CL_Switches.Limit_Line);
      Move_String
        (Parsed.Values (Sw_Limit_Lines).String_Val, CL_Switches.Limit_Lines);
      Move_String
        (Parsed.Values (Sw_Limit_Name).String_Val, CL_Switches.Limit_Name);
      Move_String
        (Parsed.Values (Sw_Limit_Region).String_Val, CL_Switches.Limit_Region);
      Move_String
        (Parsed.Values (Sw_Limit_Subp).String_Val, CL_Switches.Limit_Subp);
      Move_String
        (Parsed.Values (Sw_Memcached_Server).String_Val,
         CL_Switches.Memcached_Server);
      Move_String
        (Parsed.Values (Sw_Function_Sandboxing).String_Val,
         CL_Switches.Function_Sandboxing);
      CL_Switches.No_Global_Generation :=
        Parsed.Values (Sw_No_Global_Generation).Boolean_Val;
      CL_Switches.No_Subprojects :=
        Parsed.Values (Sw_No_Subprojects).Boolean_Val;
      CL_Switches.Output_Header :=
        Parsed.Values (Sw_Output_Header).Boolean_Val;
      CL_Switches.U := Parsed.Values (Sw_U).Boolean_Val;
      Why3_Logging := Parsed.Values (Sw_Why3_Logging).Boolean_Val;
      Move_String
        (Parsed.Values (Sw_Why3_Server).String_Val, CL_Switches.Why3_Server);
      Copy_List
        (Parsed.Values (Sw_SARIF_Base_URI).String_List_Val,
         CL_Switches.SARIF_Base_URIs);
      Move_String
        (Parsed.Values (Sw_Gnattest_Values).String_Val,
         CL_Switches.Gnattest_Values);
      Move_String
        (Parsed.Values (Sw_Proof_Manifest).String_Val, Proof_Manifest_Path);

      for WK in Misc_Warning_Kind loop
         Configuration.Warning_Status (WK) :=
           (if Parsed.Warning_Status (WK) /= WS_None
            then Parsed.Warning_Status (WK)
            else VC_Kinds.Warning_Status (WK));
      end loop;
   end Copy_To_CL_Switches;

   ----------------------------
   -- Create_Dir_And_Parents --
   ----------------------------

   procedure Create_Dir_And_Parents (Dir : Path_Name.Object) is
   begin
      if Dir.Exists then
         return;
      end if;
      if not Dir.Is_Root_Dir then
         Create_Dir_And_Parents (Dir.Containing_Directory);
      end if;
      Create_Directory_Or_Exit (Dir.String_Value);
   end Create_Dir_And_Parents;

   ------------------------------
   -- Create_Directory_Or_Exit --
   ------------------------------

   procedure Create_Directory_Or_Exit (New_Directory : String) is
   begin
      Ada.Directories.Create_Directory (New_Directory);
   exception
      when others =>
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "when creating directory "
            & New_Directory
            & ": "
            & GNAT.OS_Lib.Errno_Message);
         GNAT.OS_Lib.OS_Exit (1);
   end Create_Directory_Or_Exit;

   -------------------------
   -- Create_File_Or_Exit --
   -------------------------

   procedure Create_File_Or_Exit
     (File : in out Ada.Text_IO.File_Type;
      Mode : Ada.Text_IO.File_Mode := Ada.Text_IO.Out_File;
      Name : String := "";
      Form : String := "") is
   begin
      Ada.Text_IO.Create (File, Mode, Name, Form);
   exception
      when others =>
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "when creating file " & Name & ": " & GNAT.OS_Lib.Errno_Message);
         GNAT.OS_Lib.OS_Exit (1);
   end Create_File_Or_Exit;

   -------------------------
   -- Create_Path_Or_Exit --
   -------------------------

   procedure Create_Path_Or_Exit (New_Directory : String) is
   begin
      Ada.Directories.Create_Path (New_Directory);
   exception
      when others =>
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "when creating directory "
            & New_Directory
            & ": "
            & GNAT.OS_Lib.Errno_Message);
         GNAT.OS_Lib.OS_Exit (1);
   end Create_Path_Or_Exit;

   ------------------
   -- Display_Help --
   ------------------

   procedure Display_Help is
   begin
      Ada.Text_IO.Put_Line ("Usage: gnatprove " & Usage_Message);
      Ada.Text_IO.Put_Line (SPARK_Install.Help_Message);
   end Display_Help;

   ----------
   -- Fail --
   ----------

   procedure Fail (Msg : String) is
   begin
      raise GNATprove_Failure with Msg;
   end Fail;

   ---------------------------------
   -- Get_Or_Create_Unit_Opt_File --
   ---------------------------------

   function Extra_Args_File_For_Unit
     (Unit     : GPR2.Build.Compilation_Unit.Object;
      Phase    : Gnat2Why_Opts.Writing.Gnat2Why_Phase;
      Obj_Dir  : String;
      Why3_Dir : String) return String
   is
      Opt_File : constant String :=
        Gnat2Why_Opts.Writing.Pass_Extra_Options_To_Gnat2why
          (Phase          => Phase,
           Obj_Dir        => Obj_Dir,
           Why3_Dir       => Why3_Dir,
           Unit_Name      => File_Specific_Key (Unit),
           Proof_Manifest =>
             Proof_Manifest_For_Unit (File_Specific_Key (Unit)));
   begin
      Opt_File_Set.Include (Opt_File);
      return Opt_File;
   end Extra_Args_File_For_Unit;

   -----------------------------------
   -- Extra_Args_File_Name_For_Unit --
   -----------------------------------

   function Extra_Args_File_Name_For_Unit
     (Unit  : GPR2.Build.Compilation_Unit.Object;
      Phase : Gnat2Why_Opts.Writing.Gnat2Why_Phase) return String
   is
      Unit_Name : constant String := File_Specific_Key (Unit);
      Obj_Dir   : constant String :=
        String (Unit.Owning_View.Object_Directory.Value);
      Why3_Dir  : constant String :=
        (if Phase = Gnat2Why_Opts.Writing.Translation then Obj_Dir else "");
   begin
      return
        Gnat2Why_Opts.Writing.Opt_File_Name
          (Phase          => Phase,
           Obj_Dir        => Obj_Dir,
           Why3_Dir       => Why3_Dir,
           Unit_Name      => Unit_Name,
           Proof_Manifest => Proof_Manifest_For_Unit (Unit_Name));
   end Extra_Args_File_Name_For_Unit;

   -----------------
   -- Find_Switch --
   -----------------

   function Find_Switch
     (Spelling : String; Switch : out Switch_Id) return Boolean is
   begin
      for Candidate in Switch_Id loop
         declare
            Definition : Switch_Metadata renames
              Switch_Definitions (Candidate);
         begin
            if (Definition.Short /= null
                and then Definition.Short.all = Spelling)
              or else
                (Definition.Long /= null
                 and then Definition.Long.all = Spelling)
            then
               Switch := Candidate;
               return True;
            end if;
         end;
      end loop;

      return False;
   end Find_Switch;

   -------------------
   -- Handle_Switch --
   -------------------

   procedure Handle_Switch
     (Switch : String; Parameter : String; Section : String)
   is
      Id    : Switch_Id;
      Found : Boolean;
   begin
      pragma Unreferenced (Section);
      pragma Assert (Current_Parsed_Switches /= null);

      if Switch (Switch'First) /= '-' then

         --  We assume that the "switch" is actually an argument and put it in
         --  the file list

         Current_Parsed_Switches.File_List.Append (Switch);

      else
         Found := Find_Switch (Switch, Id);

         if not Found then
            raise Invalid_Switch;
         end if;

         Current_Parsed_Switches.Present (Id) := True;

         case Switch_Definitions (Id).Value_Kind is
            when Flag_Value        =>
               Current_Parsed_Switches.Values (Id).Boolean_Val := True;

            when Integer_Value     =>
               begin
                  Current_Parsed_Switches.Values (Id).Integer_Val :=
                    Integer'Value (Parameter);
               exception
                  when Constraint_Error =>
                     raise Invalid_Parameter;
               end;

            when String_Value      =>
               if Current_Parsed_Switches.Values (Id).String_Val /= null then
                  Free (Current_Parsed_Switches.Values (Id).String_Val);
               end if;

               Current_Parsed_Switches.Values (Id).String_Val :=
                 new String'(Parameter);

            when String_List_Value =>
               Current_Parsed_Switches.Values (Id).String_List_Val.Append
                 (Parameter);
         end case;
      end if;
   end Handle_Switch;

   -----------------------------
   -- Handle_Warning_Switches --
   -----------------------------

   procedure Handle_Warning_Switches (Switch, Value : String) is
      Tag    : Misc_Warning_Kind;
      Status : Warning_Enabled_Status;

      procedure Set_Warning_Status
        (Warning : Misc_Warning_Kind; Status : Warning_Enabled_Status);
      --  Record the warning status in the current parsed switch storage

      ------------------------
      -- Set_Warning_Status --
      ------------------------

      procedure Set_Warning_Status
        (Warning : Misc_Warning_Kind; Status : Warning_Enabled_Status) is
      begin
         pragma Assert (Current_Parsed_Switches /= null);

         Current_Parsed_Switches.Warning_Status (Warning) := Status;
      end Set_Warning_Status;
   begin

      --  Handling of pedantic and info

      if Switch = "--pedantic" then
         for WK in Pedantic_Warning_Kind loop
            Set_Warning_Status (WK, VC_Kinds.WS_Enabled);
         end loop;
         return;
      end if;
      if Switch = "--info" then
         for WK in Info_Warning_Kind loop
            Set_Warning_Status (WK, VC_Kinds.WS_Enabled);
         end loop;
         return;
      end if;
      pragma
        Assert (Switch = "-W" or else Switch = "-A" or else Switch = "-D");

      Status :=
        (if Switch = "-W"
         then VC_Kinds.WS_Enabled
         elsif Switch = "-A"
         then VC_Kinds.WS_Disabled
         else VC_Kinds.WS_Error);

      --  Handling of "all"

      if Value = "all" then
         for WK in Misc_Warning_Kind loop
            Set_Warning_Status (WK, Status);
         end loop;
         return;
      end if;

      --  Remaining cases

      begin
         Tag := From_Tag (Value);
      exception
         when Constraint_Error =>
            Abort_Msg
              (""""
               & Value
               & """ is not a valid warning name, use "
               & """--list-categories"" to obtain a list of all warning "
               & "names",
               With_Help => False);
      end;

      Set_Warning_Status (Tag, Status);
   end Handle_Warning_Switches;

   -----------------------
   -- Has_gnateT_Switch --
   -----------------------

   function Has_gnateT_Switch (View : Project.View.Object) return Boolean is
      Attr : GPR2.Project.Attribute.Object;
   begin
      if View.Check_Attribute
           (Project.Registry.Attribute.Builder.Global_Compilation_Switches,
            Index  => GPR2.Project.Attribute_Index.Create ("Ada"),
            Result => Attr)
      then
         return
           (for some Switch of Attr.Values =>
              GNATCOLL.Utils.Starts_With (String (Switch.Text), "-gnateT="));
      else
         return False;
      end if;
   end Has_gnateT_Switch;

   --------------------------
   -- Initial_Switch_Value --
   --------------------------

   function Initial_Switch_Value (Switch : Switch_Id) return Switch_Value is
   begin
      case Switch_Definitions (Switch).Value_Kind is
         when Flag_Value        =>
            return (Kind => Flag_Value, Boolean_Val => False);

         when Integer_Value     =>
            return
              (Kind        => Integer_Value,
               Integer_Val =>
                 (case Switch is
                    when Sw_J                   => 1,
                    when Sw_Level               => Invalid_Level,
                    when Sw_Steps | Sw_CE_Steps => Invalid_Steps,
                    when Sw_Proof_Warn_Timeout  => Invalid_Timeout,
                    when others                 => 0));

         when String_Value      =>
            return (Kind => String_Value, String_Val => null);

         when String_List_Value =>
            return
              (Kind            => String_List_Value,
               String_List_Val => String_Lists.Empty);
      end case;
   end Initial_Switch_Value;

   -------------------------
   -- Load_Proof_Manifest --
   -------------------------

   procedure Load_Proof_Manifest is
      use type TOML.Any_Integer;
      use type TOML.Any_Value_Kind;
      use type Ada.Directories.File_Kind;

      Manifest_Path : constant String := Proof_Manifest_Path.all;
      Current_File  : Unbounded_String;
      All_Policies  : Manifest_Subprogram_Vectors.Vector;
      --  All policies loaded so far, across all manifest files. Only used to
      --  detect duplicate entries.

      package Unit_File_Maps is new
        Ada.Containers.Indefinite_Hashed_Maps
          (Key_Type        => String,
           Element_Type    => String,
           Hash            => Ada.Strings.Hash,
           Equivalent_Keys => "=");

      Unit_Files : Unit_File_Maps.Map;
      --  Maps each unit name to the manifest file it was derived from. Used
      --  to detect distinct manifest files that correspond to the same unit,
      --  for example "main.toml" and "Main.toml" on a case-sensitive
      --  filesystem.

      function Kind_Image (Kind : TOML.Any_Value_Kind) return String;
      procedure Manifest_Error (Value : TOML.TOML_Value; Msg : String)
      with No_Return;
      procedure Check_Allowed_Keys
        (Table : TOML.TOML_Value; Allowed : String_Lists.List);
      --  Check that only the allowed fields are present in the rule
      --  entries. Raise an error using Manifest_Error function if unknown
      --  keys are found.

      procedure Check_Version (Table : TOML.TOML_Value);
      --  Raise an error if the file specifies no version or an unknown version

      function Get_Required_String
        (Table : TOML.TOML_Value; Key : String) return Unbounded_String;
      --  Helper function to access a value for a key that must be present in
      --  the file. Raise an error if absent, or ill-typed.

      function Get_Optional_String
        (Table : TOML.TOML_Value; Key : String) return Unbounded_String;
      --  Same as Get_Required_String, but returns empty string if the key is
      --  missing. Still raises an error in case of type mismatch.

      function Get_Optional_Boolean
        (Table : TOML.TOML_Value; Key : String; Default : Boolean)
         return Boolean;
      --  Similar to Get_Optional_String, but for Boolean

      function Get_Optional_Natural
        (Table : TOML.TOML_Value; Key : String; Default : Integer)
         return Integer;
      --  Similar to Get_Optional_String, but for Integer

      procedure Read_Optional_Provers
        (Table : TOML.TOML_Value; Policy : in out Manifest_Subprogram);
      --  Read the provers entry if present

      procedure Check_Unit_Prefix
        (Unit_Name : String; Value : TOML.TOML_Value; Path : String);
      --  Check that each entry is for the unit whose file it is in

      procedure Check_Path_Syntax (Value : TOML.TOML_Value; Path : String);
      --  Check that the "path" field has a meaningful syntax for this field

      procedure Check_Proof_Option_Present (Table : TOML.TOML_Value);
      --  Raise an error if an entry has no option set at all

      procedure Check_Policy
        (Table : TOML.TOML_Value; Policy : Manifest_Subprogram);
      --  Sanity checking of an entry:
      --  - kind is among valid options
      --  - if profile is present, must be a function/procedure
      --  - no duplicate entries

      function Read_Subprogram
        (Table : TOML.TOML_Value; Unit_Name : String)
         return Manifest_Subprogram;
      --  Read a single subprogram entry

      function Manifest_Less
        (Left, Right : Manifest_Subprogram) return Boolean;
      --  Ordering used to normalize the manifest before passing it to
      --  gnat2why.

      procedure Set_Manifest_Location
        (Policy : in out Manifest_Subprogram; Value : TOML.TOML_Value);
      --  Save the manifest source location used by gnat2why diagnostics

      procedure Load_Manifest_File (File : String);
      --  Read a manifest file

      ------------------------
      -- Check_Allowed_Keys --
      ------------------------

      procedure Check_Allowed_Keys
        (Table : TOML.TOML_Value; Allowed : String_Lists.List) is
      begin
         for Elt of Table.Iterate_On_Table loop
            declare
               Key : constant String := To_String (Elt.Key);
            begin
               if not Allowed.Contains (Key) then
                  Manifest_Error (Elt.Value, "unknown field """ & Key & """");
               end if;
            end;
         end loop;
      end Check_Allowed_Keys;

      -----------------------
      -- Check_Path_Syntax --
      -----------------------

      procedure Check_Path_Syntax (Value : TOML.TOML_Value; Path : String) is
         function Is_Alpha (C : Character) return Boolean
         is ((C in 'a' .. 'z') or else (C in 'A' .. 'Z'));

         function Is_Alnum (C : Character) return Boolean
         is (Is_Alpha (C) or else C in '0' .. '9');

         At_Start : Boolean := True;
      begin
         for C of Path loop
            if At_Start then
               if not Is_Alpha (C) then
                  Manifest_Error
                    (Value, "field ""path"" must be a dot-separated Ada name");
               end if;

               At_Start := False;

            elsif C = '.' then
               At_Start := True;

            elsif not (Is_Alnum (C) or else C = '_') then
               Manifest_Error
                 (Value, "field ""path"" must be a dot-separated Ada name");
            end if;
         end loop;

         if At_Start then
            Manifest_Error
              (Value, "field ""path"" must be a dot-separated Ada name");
         end if;
      end Check_Path_Syntax;

      --------------------------------
      -- Check_Proof_Option_Present --
      --------------------------------

      procedure Check_Proof_Option_Present (Table : TOML.TOML_Value) is
      begin
         if not (Table.Get_Or_Null ("level").Is_Present
                 or else Table.Get_Or_Null ("memlimit").Is_Present
                 or else Table.Get_Or_Null ("provers").Is_Present
                 or else Table.Get_Or_Null ("steps").Is_Present
                 or else Table.Get_Or_Null ("timeout").Is_Present)
         then
            Manifest_Error (Table, "missing proof option");
         end if;
      end Check_Proof_Option_Present;

      ------------------
      -- Check_Policy --
      ------------------

      procedure Check_Policy
        (Table : TOML.TOML_Value; Policy : Manifest_Subprogram)
      is
         Kind_Value  : constant String :=
           Ada.Characters.Handling.To_Lower (To_String (Policy.Kind));
         Has_Kind    : constant Boolean := Length (Policy.Kind) > 0;
         Has_Profile : constant Boolean := Length (Policy.Profile) > 0;
         Kind        : constant TOML.TOML_Value := Table.Get_Or_Null ("kind");
         Profile     : constant TOML.TOML_Value :=
           Table.Get_Or_Null ("profile");
      begin
         if Has_Kind
           and then
             Kind_Value not in "entry" | "function" | "package" | "procedure"
         then
            Manifest_Error
              (Kind,
               "field ""kind"" must be one of ""entry"", ""package"","
               & " ""procedure"" or ""function""");
         end if;

         if Has_Profile
           and then
             (not Has_Kind
              or else Kind_Value not in "entry" | "function" | "procedure")
         then
            Manifest_Error
              (Profile,
               "field ""profile"" requires kind ""entry"", ""procedure"""
               & " or ""function""");
         end if;

         for Existing of All_Policies loop
            if Ada.Characters.Handling.To_Lower (To_String (Existing.Path))
              = Ada.Characters.Handling.To_Lower (To_String (Policy.Path))
              and then
                Ada.Characters.Handling.To_Lower (To_String (Existing.Kind))
                = Kind_Value
              and then
                To_String (Existing.Profile) = To_String (Policy.Profile)
              and then Existing.Hierarchical = Policy.Hierarchical
            then
               Manifest_Error (Table, "duplicate manifest entry");
            end if;
         end loop;
      end Check_Policy;

      -----------------------
      -- Check_Unit_Prefix --
      -----------------------

      procedure Check_Unit_Prefix
        (Unit_Name : String; Value : TOML.TOML_Value; Path : String)
      is
         Lower_Path : constant String :=
           Ada.Characters.Handling.To_Lower (Path);
      begin
         if Lower_Path /= Unit_Name
           and then
             (Lower_Path'Length <= Unit_Name'Length
              or else
                Lower_Path
                  (Lower_Path'First .. Lower_Path'First + Unit_Name'Length - 1)
                /= Unit_Name
              or else Lower_Path (Lower_Path'First + Unit_Name'Length) /= '.')
         then
            Manifest_Error
              (Value,
               "path """
               & Path
               & """ does not belong to manifest unit """
               & Unit_Name
               & """");
         end if;
      end Check_Unit_Prefix;

      -------------------
      -- Check_Version --
      -------------------

      procedure Check_Version (Table : TOML.TOML_Value) is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null ("version");
      begin
         if not Value.Is_Present then
            Manifest_Error (Table, "missing required field ""version""");
         elsif Value.Kind /= TOML.TOML_Integer then
            Manifest_Error (Value, "field ""version"" must be an integer");
         elsif Value.As_Integer /= 1 then
            Manifest_Error (Value, "unsupported version, expected 1");
         end if;
      end Check_Version;

      --------------------------
      -- Get_Optional_Boolean --
      --------------------------

      function Get_Optional_Boolean
        (Table : TOML.TOML_Value; Key : String; Default : Boolean)
         return Boolean
      is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null (Key);
      begin
         if not Value.Is_Present then
            return Default;
         elsif Value.Kind /= TOML.TOML_Boolean then
            Manifest_Error (Value, "field """ & Key & """ must be a boolean");
         else
            return Value.As_Boolean;
         end if;
      end Get_Optional_Boolean;

      --------------------------
      -- Get_Optional_Natural --
      --------------------------

      function Get_Optional_Natural
        (Table : TOML.TOML_Value; Key : String; Default : Integer)
         return Integer
      is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null (Key);
      begin
         if not Value.Is_Present then
            return Default;
         elsif Value.Kind /= TOML.TOML_Integer then
            Manifest_Error (Value, "field """ & Key & """ must be an integer");
         elsif Value.As_Integer < 0 then
            Manifest_Error
              (Value, "field """ & Key & """ must be non-negative");
         elsif Value.As_Integer > TOML.Any_Integer (Natural'Last) then
            Manifest_Error (Value, "field """ & Key & """ is too large");
         else
            return Integer (Value.As_Integer);
         end if;
      end Get_Optional_Natural;

      -------------------------
      -- Get_Optional_String --
      -------------------------

      function Get_Optional_String
        (Table : TOML.TOML_Value; Key : String) return Unbounded_String
      is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null (Key);
      begin
         if not Value.Is_Present then
            return Null_Unbounded_String;
         elsif Value.Kind /= TOML.TOML_String then
            Manifest_Error (Value, "field """ & Key & """ must be a string");
         elsif Value.As_String = "" then
            Manifest_Error (Value, "field """ & Key & """ must not be empty");
         else
            return Value.As_Unbounded_String;
         end if;
      end Get_Optional_String;

      -------------------------
      -- Get_Required_String --
      -------------------------

      function Get_Required_String
        (Table : TOML.TOML_Value; Key : String) return Unbounded_String
      is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null (Key);
      begin
         if not Value.Is_Present then
            Manifest_Error (Table, "missing required field """ & Key & """");
         elsif Value.Kind /= TOML.TOML_String then
            Manifest_Error (Value, "field """ & Key & """ must be a string");
         elsif Value.As_String = "" then
            Manifest_Error (Value, "field """ & Key & """ must not be empty");
         else
            return Value.As_Unbounded_String;
         end if;
      end Get_Required_String;

      ----------------
      -- Kind_Image --
      ----------------

      function Kind_Image (Kind : TOML.Any_Value_Kind) return String is
         Image : constant String := TOML.Any_Value_Kind'Image (Kind);
      begin
         return
           Ada.Characters.Handling.To_Lower
             (Image (Image'First + 5 .. Image'Last));
      end Kind_Image;

      --------------------
      -- Manifest_Error --
      --------------------

      procedure Manifest_Error (Value : TOML.TOML_Value; Msg : String) is
         Loc : constant String := TOML.Format_Location (Value.Location);
      begin
         Abort_Msg
           ("error: invalid proof manifest "
            & To_String (Current_File)
            & (if Loc = "" then "" else ":" & Loc)
            & ": "
            & Msg,
            With_Help => False);
      end Manifest_Error;

      -------------------
      -- Manifest_Less --
      -------------------

      function Manifest_Less (Left, Right : Manifest_Subprogram) return Boolean
      is
         Left_Path  : constant String :=
           Ada.Characters.Handling.To_Lower (To_String (Left.Path));
         Right_Path : constant String :=
           Ada.Characters.Handling.To_Lower (To_String (Right.Path));
         Left_Kind  : constant String :=
           Ada.Characters.Handling.To_Lower (To_String (Left.Kind));
         Right_Kind : constant String :=
           Ada.Characters.Handling.To_Lower (To_String (Right.Kind));
      begin
         if Left_Path /= Right_Path then
            return Left_Path < Right_Path;
         elsif To_String (Left.Path) /= To_String (Right.Path) then
            return To_String (Left.Path) < To_String (Right.Path);
         elsif Left_Kind /= Right_Kind then
            return Left_Kind < Right_Kind;
         elsif To_String (Left.Kind) /= To_String (Right.Kind) then
            return To_String (Left.Kind) < To_String (Right.Kind);
         else
            return To_String (Left.Profile) < To_String (Right.Profile);
         end if;
      end Manifest_Less;

      ---------------------------
      -- Set_Manifest_Location --
      ---------------------------

      procedure Set_Manifest_Location
        (Policy : in out Manifest_Subprogram; Value : TOML.TOML_Value)
      is
         Loc : constant String := TOML.Format_Location (Value.Location);
         Sep : constant Natural := Index (Loc, ":");
      begin
         Policy.File := Current_File;

         if Sep > 0 then
            Policy.Line := Positive'Value (Loc (Loc'First .. Sep - 1));
            Policy.Column := Positive'Value (Loc (Sep + 1 .. Loc'Last));
         end if;
      exception
         when Constraint_Error =>
            Policy.Line := 1;
            Policy.Column := 1;
      end Set_Manifest_Location;

      ---------------------------
      -- Read_Optional_Provers --
      ---------------------------

      procedure Read_Optional_Provers
        (Table : TOML.TOML_Value; Policy : in out Manifest_Subprogram)
      is
         Value : constant TOML.TOML_Value := Table.Get_Or_Null ("provers");
         Seen  : String_Lists.List;
      begin
         if not Value.Is_Present then
            return;
         elsif Value.Kind /= TOML.TOML_Array then
            Manifest_Error (Value, "field ""provers"" must be an array");
         elsif Value.Length = 0 then
            Manifest_Error (Value, "field ""provers"" must not be empty");
         end if;

         for I in 1 .. Value.Length loop
            declare
               Prover : constant TOML.TOML_Value := Value.Item (I);
            begin
               if Prover.Kind /= TOML.TOML_String then
                  Manifest_Error
                    (Prover, "items of field ""provers"" must be strings");
               elsif Prover.As_String = "" then
                  Manifest_Error
                    (Prover, "items of field ""provers"" must not be empty");
               elsif Seen.Contains (Prover.As_String) then
                  Manifest_Error
                    (Prover, "duplicate prover """ & Prover.As_String & """");
               else
                  Seen.Append (Prover.As_String);
                  Policy.Provers.Append (Prover.As_String);
               end if;
            end;
         end loop;
      end Read_Optional_Provers;

      ---------------------
      -- Read_Subprogram --
      ---------------------

      function Read_Subprogram
        (Table : TOML.TOML_Value; Unit_Name : String)
         return Manifest_Subprogram
      is
         Policy  : Manifest_Subprogram;
         Allowed : String_Lists.List;
         Path    : Unbounded_String;
      begin
         if Table.Kind /= TOML.TOML_Table then
            Manifest_Error (Table, "items of field ""rule"" must be tables");
         end if;

         Allowed.Append ("path");
         Allowed.Append ("kind");
         Allowed.Append ("profile");
         Allowed.Append ("hierarchical");
         Allowed.Append ("timeout");
         Allowed.Append ("steps");
         Allowed.Append ("memlimit");
         Allowed.Append ("level");
         Allowed.Append ("provers");
         Check_Allowed_Keys (Table, Allowed);
         Check_Proof_Option_Present (Table);

         Path := Get_Required_String (Table, "path");
         Check_Path_Syntax (Table.Get_Or_Null ("path"), To_String (Path));
         Check_Unit_Prefix
           (Unit_Name, Table.Get_Or_Null ("path"), To_String (Path));
         Policy.Path := Path;
         Set_Manifest_Location (Policy, Table.Get_Or_Null ("path"));
         Policy.Kind := Get_Optional_String (Table, "kind");
         Policy.Profile := Get_Optional_String (Table, "profile");
         Policy.Hierarchical :=
           Get_Optional_Boolean (Table, "hierarchical", True);
         Policy.Timeout :=
           Get_Optional_Natural (Table, "timeout", Invalid_Manifest_Timeout);
         Policy.Steps :=
           Get_Optional_Natural (Table, "steps", Invalid_Manifest_Steps);
         Policy.Memlimit :=
           Get_Optional_Natural (Table, "memlimit", Invalid_Manifest_Memlimit);
         Policy.Level :=
           Get_Optional_Natural (Table, "level", Invalid_Manifest_Level);
         if Policy.Level /= Invalid_Manifest_Level
           and then Policy.Level not in 0 .. 4
         then
            Manifest_Error
              (Table.Get_Or_Null ("level"),
               "field ""level"" must be between 0 and 4");
         end if;
         Read_Optional_Provers (Table, Policy);
         Check_Policy (Table, Policy);

         return Policy;
      end Read_Subprogram;

      ------------------------
      -- Load_Manifest_File --
      ------------------------

      procedure Load_Manifest_File (File : String) is
         Root      : TOML.TOML_Value;
         Subs      : TOML.TOML_Value;
         Allowed   : String_Lists.List;
         Unit_Name : constant String := Manifest_Unit_Name (File);
         Policies  : Manifest_Subprogram_Vectors.Vector;
      begin
         Current_File := To_Unbounded_String (File);

         declare
            Position : Unit_File_Maps.Cursor;
            Inserted : Boolean;
         begin
            Unit_Files.Insert (Unit_Name, File, Position, Inserted);

            if not Inserted then
               Abort_Msg
                 ("error: invalid proof manifest "
                  & File
                  & ": file corresponds to the same unit """
                  & Unit_Name
                  & """ as "
                  & Unit_File_Maps.Element (Position),
                  With_Help => False);
            end if;
         end;

         declare
            Result : constant TOML.Read_Result :=
              TOML.File_IO.Load_File (File);
         begin
            if not Result.Success then
               Abort_Msg
                 ("error: cannot parse proof manifest "
                  & File
                  & ": "
                  & TOML.Format_Error (Result),
                  With_Help => False);
            end if;

            Root := Result.Value;
         end;

         if Root.Kind /= TOML.TOML_Table then
            Manifest_Error
              (Root,
               "top-level value must be a table, got "
               & Kind_Image (Root.Kind));
         end if;

         Allowed.Append ("version");
         Allowed.Append ("rule");
         Check_Allowed_Keys (Root, Allowed);
         Check_Version (Root);
         Subs := Root.Get_Or_Null ("rule");

         if not Subs.Is_Present then
            return;
         elsif Subs.Kind /= TOML.TOML_Array then
            Manifest_Error (Subs, "field ""rule"" must be an array");
         end if;

         for I in 1 .. Subs.Length loop
            declare
               Policy : constant Manifest_Subprogram :=
                 Read_Subprogram (Subs.Item (I), Unit_Name);
            begin
               All_Policies.Append (Policy);
               Policies.Append (Policy);
            end;
         end loop;

         declare
            package Manifest_Sorting is new
              Manifest_Subprogram_Vectors.Generic_Sorting
                ("<" => Manifest_Less);
         begin
            Manifest_Sorting.Sort (Policies);

            --  Files mapping to an already seen unit were rejected above, so
            --  the unit cannot be in the map yet.

            Proof_Manifest_Maps.Insert (Unit_Name, Policies);
         end;
      end Load_Manifest_File;

   begin
      Proof_Manifest_Maps.Clear;

      if Manifest_Path = "" then
         return;
      elsif not Ada.Directories.Exists (Manifest_Path) then
         Abort_Msg
           ("error: proof manifest folder """
            & Manifest_Path
            & """ does not exist",
            With_Help => False);
      elsif Ada.Directories.Kind (Manifest_Path) /= Ada.Directories.Directory
      then
         Abort_Msg
           ("error: proof manifest """ & Manifest_Path & """ is not a folder",
            With_Help => False);
      end if;

      declare
         S     : Ada.Directories.Search_Type;
         D     : Ada.Directories.Directory_Entry_Type;
         Files : String_Lists.List;
         package File_Sorting is new String_Lists.Generic_Sorting;
      begin
         Ada.Directories.Start_Search
           (S,
            Manifest_Path,
            "*.toml",
            [Ada.Directories.Ordinary_File => True, others => False]);

         while Ada.Directories.More_Entries (S) loop
            Ada.Directories.Get_Next_Entry (S, D);
            Files.Append
              (Ada.Directories.Compose
                 (Manifest_Path, Ada.Directories.Simple_Name (D)));
         end loop;

         --  Process files in sorted order so that errors are reported
         --  deterministically, independently of the order of directory
         --  traversal.

         File_Sorting.Sort (Files);

         for File of Files loop
            Load_Manifest_File (File);
         end loop;
      end;
   end Load_Proof_Manifest;

   -----------------------------
   -- Proof_Manifest_For_Unit --
   -----------------------------

   function Proof_Manifest_For_Unit
     (Unit_Name : String) return Manifest_Subprogram_Vectors.Vector
   is
      Position : constant Manifest_Maps.Cursor :=
        Proof_Manifest_Maps.Find (Manifest_Unit_Name (Unit_Name));
   begin
      if Manifest_Maps.Has_Element (Position) then
         return Manifest_Maps.Element (Position);
      else
         return Manifest_Subprogram_Vectors.Empty_Vector;
      end if;
   end Proof_Manifest_For_Unit;

   --------------------------
   -- No_Project_File_Mode --
   --------------------------

   function No_Project_File_Mode return String is

      function Create_Default_Project_File return String;
      --  Create a project file with name default.gpr and default contents.
      --  Return the name of the project file (default.gpr).

      function Find_Project_File_In_CWD return String;
      --  If the current directory contains exactly one .gpr file, return it,
      --  otherwise return the empty string.

      ---------------------------------
      -- Create_Default_Project_File --
      ---------------------------------

      function Create_Default_Project_File return String is
         F    : Ada.Text_IO.File_Type;
         Name : constant String := "default.gpr";
      begin
         Create_File_Or_Exit (F, Ada.Text_IO.Out_File, Name);
         Ada.Text_IO.Put_Line (F, "project default is");
         Ada.Text_IO.Put_Line (F, "end default;");
         Ada.Text_IO.Flush (F);
         Ada.Text_IO.Close (F);
         return Name;
      end Create_Default_Project_File;

      ------------------------------
      -- Find_Project_File_In_CWD --
      ------------------------------

      function Find_Project_File_In_CWD return String is
         S : Ada.Directories.Search_Type;
         D : Ada.Directories.Directory_Entry_Type;
      begin
         Ada.Directories.Start_Search
           (S,
            ".",
            "*.gpr",
            [Ada.Directories.Ordinary_File => True, others => False]);
         if not Ada.Directories.More_Entries (S) then
            return "";
         end if;
         Ada.Directories.Get_Next_Entry (S, D);
         if Ada.Directories.More_Entries (S) then
            Abort_With_Message
              ("No project file given, and current directory contains more "
               & "than one project file. Please specify a project file.");
         end if;
         return Ada.Directories.Simple_Name (D);
      end Find_Project_File_In_CWD;

      Result : constant String := Find_Project_File_In_CWD;

   begin
      if Result /= "" then
         Ada.Text_IO.Put_Line ("No project file given, using " & Result);
         return Result;
      else
         declare
            Name : constant String := Create_Default_Project_File;
         begin
            Ada.Text_IO.Put_Line ("No project file given, creating " & Name);
            return Name;
         end;
      end if;
   end No_Project_File_Mode;

   --------------------
   -----------------------------
   -- Parse_Switches_Internal --
   -----------------------------

   function Parse_Switches_Internal
     (Mode : Parsing_Modes; Com_Lin : String_List) return Parsed_Switches
   is

      procedure Free_Topmost is new
        Ada.Unchecked_Deallocation
          (Object => String_List,
           Name   => String_List_Access);

      Config         : Command_Line_Configuration;
      Parser         : Opt_Parser;
      Com_Lin_Access : String_List_Access := new String_List'(Com_Lin);
      Parsed         : aliased Parsed_Switches;

      function Option_Image (Ref : String_Ref) return String
      is (if Ref = null then "" else Ref.all);

      function Short_Name (Switch : Switch_Id) return String
      is (Option_Image (Switch_Definitions (Switch).Short));
      --  Return the short spelling of Switch, without argument markers

      function Long_Name (Switch : Switch_Id) return String
      is (Option_Image (Switch_Definitions (Switch).Long));
      --  Return the long spelling of Switch, without argument markers

      function GNAT_Command_Line_Short_Switch
        (Switch : Switch_Id) return String;
      --  Return the short switch spelling expected by GNAT.Command_Line

      function GNAT_Command_Line_Long_Switch
        (Switch : Switch_Id) return String;
      --  Return the long switch spelling expected by GNAT.Command_Line

      procedure Register_Switch (Switch : Switch_Id);
      --  Register Switch so that Handle_Switch stores its value.

      function GNAT_Command_Line_Short_Switch
        (Switch : Switch_Id) return String
      is
         Short : constant String := Short_Name (Switch);
      begin
         if Switch_Definitions (Switch).Value_Kind = Flag_Value then
            return Short;
         elsif Switch = Sw_J then
            return Short & ":";
         else
            return Short & "=";
         end if;
      end GNAT_Command_Line_Short_Switch;

      function GNAT_Command_Line_Long_Switch (Switch : Switch_Id) return String
      is
         Long : constant String := Long_Name (Switch);
      begin
         if Switch_Definitions (Switch).Value_Kind = Flag_Value then
            return Long;
         else
            return Long & "=";
         end if;
      end GNAT_Command_Line_Long_Switch;

      procedure Register_Switch (Switch : Switch_Id) is
         Short : constant String := Short_Name (Switch);
         Long  : constant String := Long_Name (Switch);
      begin
         Define_Switch
           (Config,
            (if Short = ""
             then ""
             else GNAT_Command_Line_Short_Switch (Switch)),
            Long_Switch =>
              (if Long = ""
               then ""
               else GNAT_Command_Line_Long_Switch (Switch)));
      end Register_Switch;

   begin
      pragma Assert (Switch_Values_Have_Expected_Kinds (Parsed.Values));

      Initialize_Option_Scan (Parser, Com_Lin_Access);
      Set_Usage
        (Config,
         Usage    => Usage_Message,
         Help_Msg => SPARK_Install.Help_Message);

      if Mode in All_Switches | Global_Switches_Only then
         for Switch in Invocation_Switch_Id loop
            --  Proof manifests are command-line only for now; project file
            --  attributes can get their own syntax once the schema settles.
            if Mode = All_Switches or else Switch /= Sw_Proof_Manifest then
               Register_Switch (Switch);
            end if;
         end loop;
      end if;

      if Mode in All_Switches | Global_Switches_Only | File_Specific_Only then
         for Switch in File_Specific_Switch_Id loop
            if Switch
               not in Sw_Info
                    | Sw_Pedantic
                    | Sw_Warn_Enable
                    | Sw_Warn_Disable
                    | Sw_Warn_Error
            then
               Register_Switch (Switch);
            end if;
         end loop;

         Define_Switch
           (Config,
            Handle_Warning_Switches'Access,
            Long_Switch => Long_Name (Sw_Info));
         Define_Switch
           (Config,
            Handle_Warning_Switches'Access,
            Long_Switch => Long_Name (Sw_Pedantic));
         Define_Switch
           (Config,
            Handle_Warning_Switches'Access,
            GNAT_Command_Line_Short_Switch (Sw_Warn_Enable));
         Define_Switch
           (Config,
            Handle_Warning_Switches'Access,
            GNAT_Command_Line_Short_Switch (Sw_Warn_Disable));
         Define_Switch
           (Config,
            Handle_Warning_Switches'Access,
            GNAT_Command_Line_Short_Switch (Sw_Warn_Error));
      end if;

      if Mode in All_Switches | Global_Switches_Only then
         Define_Switch (Config, "*", Help => "list of source files");
      end if;

      --  Getopt calls callbacks synchronously and this access value is cleared
      --  before returning, so the local Parsed object cannot outlive this use
      --  and Unchecked_Access is safe here.
      Current_Parsed_Switches := Parsed'Unchecked_Access;

      begin
         Getopt
           (Config,
            Callback    => Handle_Switch'Access,
            Parser      => Parser,
            Concatenate => False);

      exception
         when Invalid_Switch =>
            Current_Parsed_Switches := null;
            Fail ("");
         when Exit_From_Command_Line =>
            Current_Parsed_Switches := null;
            Succeed;
         when Invalid_Parameter =>
            Current_Parsed_Switches := null;
            Abort_Msg
              ("No parameter given to switch -" & Full_Switch (Parser),
               With_Help => False);
         when others =>
            Current_Parsed_Switches := null;
            raise;
      end;

      Current_Parsed_Switches := null;

      Free (Config);
      Free_Topmost (Com_Lin_Access);

      return Parsed;
   end Parse_Switches_Internal;

   -------------------------------------------
   -- Parse_Switches_Before_Project_Parsing --
   -------------------------------------------

   function Parse_Switches_Before_Project_Parsing
     (Com_Lin : String_List) return Project_Parsing_Result
   is
      use GNATCOLL.Opt_Parse;
      use GNATCOLL.Strings;

      function Parse_Command_Line_Verbosity
        (Args : String_List) return Verbosity_Choice;
      --  Return the effective verbosity from the command line slice that is
      --  parsed before project loading. The last -q/-v wins.

      function To_String_List
        (Args : XString_Vector) return String_List_Access;
      --  Convert a vector of XStrings to a String_List_Access.

      function To_String_List (Args : String_List) return String_List_Access;
      --  Copy a String_List into a String_List_Access.

      Parser : Argument_Parser :=
        Create_Argument_Parser
          (Help => SPARK_Install.Help_Message, Generate_Help_Flag => False);

      package Version is new
        Parse_Flag (Parser => Parser, Long => "--version");

      package Clean is new Parse_Flag (Parser => Parser, Long => "--clean");

      package Explain is new
        Parse_Option
          (Parser      => Parser,
           Long        => "--explain",
           Arg_Type    => Unbounded_String,
           Default_Val => Null_Unbounded_String);

      package List_Explain_Codes is new
        Parse_Flag (Parser => Parser, Long => "--debug-list-explain-codes");

      package Help is new Parse_Flag (Parser => Parser, Long => "--help");

      package List_Categories is new
        Parse_Flag (Parser => Parser, Long => "--list-categories");

      package GPR_Registry is new
        Parse_Flag
          (Parser => Parser,
           Long   => GPR2.Options.Print_GPR_Registry_Option);

      package GPR_Args is new GPR2.Options.Opt_Parse.Args (Parser => Parser);

      XCom_Lin : XString_Array (Com_Lin'Range);
      Unused   : XString_Vector;
      Cargs    : String_List_Access := null;
      Last_Arg : Natural := Com_Lin'Last;

      ----------------------------------
      -- Parse_Command_Line_Verbosity --
      ----------------------------------

      function Parse_Command_Line_Verbosity
        (Args : String_List) return Verbosity_Choice
      is
         Result : Verbosity_Choice := Normal_Level;
      begin
         for Arg of Args loop
            if Arg.all = "-q" or else Arg.all = "--quiet" then
               Result := Quiet_Level;
            elsif Arg.all = "-v" or else Arg.all = "--verbose" then
               Result := Verbose_Level;
            end if;
         end loop;
         return Result;
      end Parse_Command_Line_Verbosity;

      --------------------
      -- To_String_List --
      --------------------

      function To_String_List (Args : XString_Vector) return String_List_Access
      is
         Result : constant String_List_Access :=
           new String_List (1 .. Natural (Args.Length));
         Index  : Integer := Result'First;
      begin
         for Arg of Args loop
            Result (Index) := new String'(To_String (Arg));
            Index := Index + 1;
         end loop;
         return Result;
      end To_String_List;

      --------------------
      -- To_String_List --
      --------------------

      function To_String_List (Args : String_List) return String_List_Access is
         Result : constant String_List_Access := new String_List (Args'Range);
      begin
         for I in Args'Range loop
            Result (I) := new String'(Args (I).all);
         end loop;
         return Result;
      end To_String_List;

   begin

      for I in Com_Lin'Range loop
         if Com_Lin (I).all = "-cargs" then
            Last_Arg := I - 1;

            if I < Com_Lin'Last then
               Cargs := To_String_List (Com_Lin (I + 1 .. Com_Lin'Last));
            end if;

            exit;
         end if;
      end loop;

      for I in Com_Lin'First .. Last_Arg loop
         XCom_Lin (I) := GNATCOLL.Strings.To_XString (Com_Lin (I).all);
      end loop;
      if not Parser.Parse
               (XCom_Lin (Com_Lin'First .. Last_Arg),
                Unknown_Arguments => Unused)
      then
         Abort_Msg
           ("invalid command line, use --help for more information",
            With_Help => True);
      end if;

      return
        (Opt                => GPR_Args.Parsed_GPR2_Options,
         Version            => Version.Get,
         Clean              => Clean.Get,
         List_Categories    => List_Categories.Get,
         Explain            => Explain.Get,
         List_Explain_Codes => List_Explain_Codes.Get,
         Gpr_Registry       => GPR_Registry.Get,
         Help               => Help.Get,
         Verbosity          =>
           Parse_Command_Line_Verbosity (Com_Lin (Com_Lin'First .. Last_Arg)),
         Cargs              => Cargs,
         Remaining_Args     => To_String_List (Unused));
   end Parse_Switches_Before_Project_Parsing;

   ------------------------
   -- Prepare_Prover_Lib --
   ------------------------

   procedure Prepare_Prover_Lib (Obj_Dir : String) is

      Provers        : String_Lists.List renames
        File_Specific_Map ("default").Provers;
      Prover_Name    : constant String :=
        Ada.Characters.Handling.To_Lower (Provers.First_Element);
      Prover_Lib_Dir : constant String :=
        Ada.Directories.Compose
          (Ada.Directories.Compose (SPARK_Install.Libexec_Share_Why3, "libs"),
           Name => Prover_Name);
      Prover_Obj_Dir : constant String :=
        Ada.Directories.Compose
          (Ada.Directories.Compose (Obj_Dir, "why3_libs"),
           Name => Prover_Name);

      procedure Compile_Lib (Dir, File : String);
      --  compile a Coq library
      --  @param Dir  the directory where the file is located
      --  @param File the file to be compiled

      -----------------
      -- Compile_Lib --
      -----------------

      procedure Compile_Lib (Dir, File : String) is
         Target_Dir : constant String :=
           (if Dir /= ""
            then Ada.Directories.Compose (Prover_Obj_Dir, Dir)
            else Prover_Obj_Dir);
         Lib_Dir    : constant String :=
           (if Dir /= ""
            then Ada.Directories.Compose (Prover_Lib_Dir, Dir)
            else Prover_Lib_Dir);
      begin
         if not Ada.Directories.Exists
                  (Ada.Directories.Compose (Target_Dir, Name => File & ".vo"))
         then
            declare
               Source_Dest : constant String :=
                 Ada.Directories.Compose (Target_Dir, Name => File & ".v");
            begin
               --  Copy file
               Create_Path_Or_Exit (Prover_Obj_Dir);
               if not Ada.Directories.Exists (Target_Dir) then
                  Create_Directory_Or_Exit (Target_Dir);
               end if;
               Ada.Directories.Copy_File
                 (Ada.Directories.Compose (Lib_Dir, Name => File & ".v"),
                  Source_Dest);
               --  Build it
               declare
                  Coqc_Bin : GNAT.OS_Lib.String_Access :=
                    GNAT.OS_Lib.Locate_Exec_On_Path ("coqc");
                  Args     : GNAT.OS_Lib.Argument_List :=
                    [1 => new String'("-R"),
                     2 => new String'(Prover_Obj_Dir),
                     3 => new String'("Why3"),
                     4 => new String'(Source_Dest)];

                  Success : Boolean;

               begin
                  if Coqc_Bin = null then
                     Abort_Msg
                       (Msg       => "coq prover not present in PATH",
                        With_Help => False);
                  end if;
                  GNAT.OS_Lib.Spawn
                    (Program_Name => Coqc_Bin.all,
                     Args         => Args,
                     Success      => Success);
                  if not Success then
                     Abort_Msg
                       (Msg       =>
                          "error during compilations of " & Source_Dest,
                        With_Help => False);
                  end if;

                  GNAT.OS_Lib.Free (Coqc_Bin);

                  Free (Args);
               end;
            end;
         end if;
      end Compile_Lib;

   begin
      --  Compilation of [Why3|SPARK]'s Coq libraries
      --
      --  This list of files comes from the Why3 Makefile. We compile these
      --  files here, when the user runs gnatprove with Coq prover, because we
      --  do not ship Coq ourselves, so cannot compile these files in advance.
      --  The order of files is important, dependencies of some file need to
      --  be compiled before that file.

      Compile_Lib ("", "BuiltIn");
      Compile_Lib ("", "HighOrd");
      Compile_Lib ("", "WellFounded");
      Compile_Lib ("int", "Int");
      Compile_Lib ("int", "Exponentiation");
      Compile_Lib ("int", "Abs");
      Compile_Lib ("int", "ComputerDivision");
      Compile_Lib ("int", "EuclideanDivision");
      Compile_Lib ("int", "Div2");
      Compile_Lib ("int", "MinMax");
      Compile_Lib ("int", "Power");
      Compile_Lib ("int", "NumOf");
      Compile_Lib ("bool", "Bool");
      Compile_Lib ("real", "Real");
      Compile_Lib ("real", "Abs");
      Compile_Lib ("real", "ExpLog");
      Compile_Lib ("real", "FromInt");
      Compile_Lib ("real", "MinMax");
      Compile_Lib ("real", "RealInfix");
      Compile_Lib ("real", "PowerInt");
      Compile_Lib ("real", "Square");
      Compile_Lib ("real", "PowerReal");
      Compile_Lib ("real", "Trigonometry");
      Compile_Lib ("number", "Parity");
      Compile_Lib ("number", "Divisibility");
      Compile_Lib ("number", "Gcd");
      Compile_Lib ("number", "Prime");
      Compile_Lib ("number", "Coprime");
      Compile_Lib ("map", "Map");
      Compile_Lib ("map", "Const");
      Compile_Lib ("map", "Occ");
      Compile_Lib ("map", "MapPermut");
      Compile_Lib ("map", "MapInjection");
      Compile_Lib ("map", "MapExt");
      Compile_Lib ("set", "Set");
      Compile_Lib ("list", "List");
      Compile_Lib ("list", "Length");
      Compile_Lib ("list", "Mem");
      Compile_Lib ("option", "Option");
      Compile_Lib ("list", "Nth");
      Compile_Lib ("list", "NthLength");
      Compile_Lib ("list", "HdTl");
      Compile_Lib ("list", "NthHdTl");
      Compile_Lib ("list", "Append");
      Compile_Lib ("list", "NthLengthAppend");
      Compile_Lib ("list", "Reverse");
      Compile_Lib ("list", "HdTlNoOpt");
      Compile_Lib ("list", "NthNoOpt");
      Compile_Lib ("list", "RevAppend");
      Compile_Lib ("list", "Combine");
      Compile_Lib ("list", "Distinct");
      Compile_Lib ("list", "NumOcc");
      Compile_Lib ("list", "Permut");
      Compile_Lib ("bv", "Pow2int");
      Compile_Lib ("bv", "BV_Gen");
      Compile_Lib ("spark", "SPARK_Raising_Order");
      Compile_Lib ("spark", "SPARK_Integer_Arithmetic");
      Compile_Lib ("", "SPARK");
   end Prepare_Prover_Lib;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Proof_Mode) return String is
   begin
      case P is
         when No_WP       =>
            return "no_wp";

         when All_Split   =>
            return "all_split";

         when Progressive =>
            return "progressive";

         when Per_Path    =>
            return "per_path";

         when Per_Check   =>
            return "per_check";
      end case;
   end To_String;

   ----------------------------
   -- Produce_Explain_Output --
   ----------------------------

   procedure Produce_Explain_Output (Explain_Code : String) is
      C : constant String := Ada.Characters.Handling.To_Upper (Explain_Code);
   begin
      --  Validate the format of C as a valid explain code

      if C'Length /= 5
        or else C (1) /= 'E'
        or else (for some I in 2 .. 5 => C (I) not in '0' .. '9')
      then
         Abort_Msg
           ("error: wrong argument for --explain, "
            & "must be explain code of the form E0001",
            With_Help => False);
      end if;

      declare
         Filename : constant String :=
           Ada.Directories.Compose
             (SPARK_Install.Share_Spark_Explain_Codes, C, "md");
         File     : Ada.Text_IO.File_Type;
      begin
         if not Ada.Directories.Exists (Filename) then
            Abort_Msg
              ("error: wrong argument for --explain, "
               & C
               & " is not a valid explain code",
               With_Help => False);
         end if;

         Ada.Text_IO.Open (File, Ada.Text_IO.In_File, Filename);
         while not Ada.Text_IO.End_Of_File (File) loop
            Ada.Text_IO.Put_Line (Ada.Text_IO.Get_Line (File));
         end loop;
      end;
   end Produce_Explain_Output;

   ---------------------------------------
   -- Produce_List_Explain_Codes_Output --
   ---------------------------------------

   procedure Produce_List_Explain_Codes_Output is
   begin
      --  List every explain code with its one-line description. The list is
      --  derived from the Explain_Code_Kind enumeration, so it cannot drift
      --  from the set of codes the tool knows about.

      for Code in Explain_Code_Kind'Succ (EC_None) .. Explain_Code_Kind'Last
      loop
         Ada.Text_IO.Put_Line
           (To_String (Code) & ": " & Explain_Description (Code));
      end loop;
   end Produce_List_Explain_Codes_Output;

   ------------------------------------
   -- Produce_List_Categories_Output --
   ------------------------------------

   procedure Produce_List_Categories_Output is

      function Category (K : VC_Kind) return String;
      --  Produce a category string for this check kind

      function Effort (K : VC_Kind) return String;
      --  Produce an effort string for this check kind

      --------------
      -- Category --
      --------------

      function Category (K : VC_Kind) return String is
      begin
         case K is
            when VC_RTE_Kind     =>
               return "(run-time-check)";

            when VC_Assert_Kind  =>
               return "(assertion)";

            when VC_LSP_Kind     =>
               return "(liskov-substitution-principle)";

            when VC_Warning_Kind =>
               return "(proof_warning)";
         end case;
      end Category;

      ------------
      -- Effort --
      ------------

      function Effort (K : VC_Kind) return String is
      begin
         case K is
            when VC_RTE_Kind | VC_Assert_Kind | VC_LSP_Kind =>
               return "MEDIUM";

            when VC_Warning_Kind                            =>
               return "EASY";
         end case;
      end Effort;

   begin

      --  The output format agreed upon with gnathub team is as follows:
      --  [category]
      --  key(optional category override) - name - description - effort

      Ada.Text_IO.Put_Line ("[Flow analysis error categories]");
      for K in Flow_Error_Kind loop
         Ada.Text_IO.Put_Line
           (Rule_Name (K)
            & " - "
            & Kind_Name (K)
            & " - "
            & Description (K)
            & " - MEDIUM");
      end loop;

      Ada.Text_IO.Put_Line ("[Flow analysis check categories]");
      for K in Flow_Check_Kind loop
         Ada.Text_IO.Put_Line
           (Rule_Name (K)
            & " - "
            & Kind_Name (K)
            & " - "
            & Description (K)
            & " - EASY");
      end loop;

      Ada.Text_IO.Put_Line ("[Flow analysis warnings categories]");
      for K in Flow_Warning_Kind loop
         Ada.Text_IO.Put_Line
           (Rule_Name (K)
            & " - "
            & Kind_Name (K)
            & " - "
            & Description (K)
            & " - EASY");
      end loop;

      Ada.Text_IO.Put_Line ("[Proof check categories]");
      for K in VC_Kind loop
         if K not in VC_Warning_Kind then
            Ada.Text_IO.Put_Line
              (Rule_Name (K)
               & Category (K)
               & " - "
               & Kind_Name (K)
               & " - "
               & Description (K)
               & " - "
               & Effort (K));
         end if;
      end loop;

      Ada.Text_IO.Put_Line ("[Proof warnings categories]");
      for K in VC_Kind loop
         if K in VC_Warning_Kind then
            Ada.Text_IO.Put_Line
              (Rule_Name (K)
               & " - "
               & Kind_Name (K)
               & " - "
               & Description (K)
               & " - "
               & Effort (K));
         end if;
      end loop;

      Ada.Text_IO.Put_Line ("[Misc warnings categories]");
      for K in Misc_Warning_Kind loop
         Ada.Text_IO.Put_Line
           (Kind_Name (K)
            & " - "
            & Kind_Name (K)
            & " - "
            & Description (K)
            & " - EASY");
      end loop;

      --  Annotation error categories
      Ada.Text_IO.Put_Line ("[Annotation error categories]");
      for K in GNATprove_Annotation_Kind loop
         declare
            Rule_ID : constant String := Annotation_Tag (K);
         begin
            Ada.Text_IO.Put_Line
              (Rule_ID
               & " - "
               & Rule_ID
               & " - "
               & Annotation_Description (K)
               & " - HIGH");
         end;
      end loop;

      --  Unsupported construct categories
      Ada.Text_IO.Put_Line ("[Unsupported construct categories]");
      for K in Unsupported_Kind loop
         declare
            Rule_ID : constant String := Unsupported_Tag (K);
         begin
            Ada.Text_IO.Put_Line
              (Rule_ID
               & " - "
               & Rule_ID
               & " - "
               & Description (K)
               & " - HIGH");
         end;
      end loop;

      --  Violation categories
      Ada.Text_IO.Put_Line ("[Violation categories]");
      for K in Violation_Kind loop
         declare
            Rule_ID : constant String := Violation_Tag (K);
         begin
            Ada.Text_IO.Put_Line
              (Rule_ID
               & " - "
               & Rule_ID
               & " - "
               & Violation_Description (K)
               & " - HIGH");
         end;
      end loop;
      --  Special hardcoded categories
      Ada.Text_IO.Put_Line ("[Misc categories]");
      Ada.Text_IO.Put_Line
        (Misc_Error_Tag
         & " - "
         & Misc_Error_Name
         & " - "
         & Misc_Error_Description
         & " - HIGH");

      --  ??? TODO GNAT front-end categories
   end Produce_List_Categories_Output;

   ----------------------------
   -- Produce_Version_Output --
   ----------------------------

   procedure Produce_Version_Output is

      procedure Print_First_Line_Of_Output
        (Command   : String;
         Arguments : String_Lists.List;
         Status    : out Integer);
      --  Run the given command with the given arguments, and print the first
      --  line of the output (with a single newline at the end in all cases).
      --  Assumes that Command is in PATH or is an absolute path.

      --------------------------------
      -- Print_First_Line_Of_Output --
      --------------------------------

      procedure Print_First_Line_Of_Output
        (Command : String; Arguments : String_Lists.List; Status : out Integer)
      is
         Local_Status : aliased Integer;
         Arg_List     : GNAT.OS_Lib.Argument_List :=
           Argument_List_Of_String_List (Arguments);
         Output       : constant String :=
           GNAT.Expect.Get_Command_Output
             (Command, Arg_List, "", Local_Status'Access, True);
         Last         : Integer := Output'Last;
      begin
         Status := Local_Status;
         GNATCOLL.Utils.Free (Arg_List);
         for C in Output'Range loop
            if Output (C) in ASCII.LF | ASCII.CR then
               Last := C - 1;
               exit;
            end if;
         end loop;
         Ada.Text_IO.Put_Line (Output (Output'First .. Last));
      end Print_First_Line_Of_Output;

      Gnatwhy3          : constant String :=
        Ada.Directories.Compose (SPARK_Install.Libexec_Spark_Bin, "gnatwhy3");
      Alt_Ergo          : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("alt-ergo");
      Colibri           : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("colibri");
      CVC5              : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("cvc5");
      Z3                : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("z3");
      Status            : aliased Integer;
      Dash_Dash_Version : String_Lists.List;
      Dash_Version      : String_Lists.List;

   begin
      Dash_Dash_Version.Append ("--version");
      Dash_Version.Append ("-version");
      Ada.Text_IO.Put_Line (SPARK2014_Version_String);
      Print_First_Line_Of_Output
        (Gnatwhy3, Arguments => Dash_Dash_Version, Status => Status);

      if Alt_Ergo /= null then
         Ada.Text_IO.Put (Alt_Ergo.all & ": ");
         Print_First_Line_Of_Output
           (Alt_Ergo.all, Arguments => Dash_Dash_Version, Status => Status);
         Free (Alt_Ergo);
      end if;
      if Colibri /= null then
         Ada.Text_IO.Put (Colibri.all & ": ");
         Print_First_Line_Of_Output
           (Colibri.all, Arguments => Dash_Dash_Version, Status => Status);
         Free (Colibri);
      end if;
      if CVC5 /= null then
         Ada.Text_IO.Put (CVC5.all & ": ");
         Print_First_Line_Of_Output
           (CVC5.all, Arguments => Dash_Dash_Version, Status => Status);
         Free (CVC5);
      end if;
      if Z3 /= null then
         Ada.Text_IO.Put (Z3.all & ": ");
         Print_First_Line_Of_Output
           (Z3.all, Arguments => Dash_Dash_Version, Status => Status);
         Free (Z3);
      end if;
   end Produce_Version_Output;

   -----------------
   -- Prover_List --
   -----------------

   function Prover_List (FS : File_Specific) return String is
      use String_Lists;

      Buf : Unbounded_String := Null_Unbounded_String;
      C   : Cursor := First (FS.Provers);
   begin
      loop
         Append (Buf, FS.Provers (C));
         Next (C);
         exit when not Has_Element (C);
         Append (Buf, ',');
      end loop;
      return To_String (Buf);
   end Prover_List;

   function Prover_List return String is
   begin
      return Prover_List (File_Specific_Map ("default"));
   end Prover_List;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project.Tree.Object) is

      procedure Init
        (Tree : out Project.Tree.Object; Opt : in out GPR2.Options.Object);
      --  Load the project file; This function requires the project file to be
      --  present.

      procedure Parse_Analysis_Attributes
        (Command_Line : Parsed_Switches; Root_Attributes : Parsed_Switches);
      --  Parse the Switches and Proof_Switches attributes in project files.
      --  The regular command line is needed to interpret them properly.

      procedure Postprocess (Parsed : in out Parsed_Switches);
      --  Read the switch variables set by command-line parsing and set the
      --  gnatprove variables.

      procedure Warn_And_Strip_Non_Root_Invocation_Switches
        (View           : Project.View.Object;
         Attribute_Name : String;
         Switches       : in out Parsed_Switches);
      --  Invocation-level switches from non-root projects are accepted for
      --  compatibility but ignored semantically.

      procedure File_Specific_Postprocess
        (Parsed : Parsed_Switches; FS : out File_Specific);
      --  Same as Postprocess, but for the switches that can be file-specific.
      --  For example, --level, --timeout are handled here.

      procedure Check_Obsolete_Prove_Switches (View : Project.View.Object);
      --  Check for the obsolete Prove.Switches attribute and issue a warning
      --  if present.

      procedure Set_Mode (Parsed : Parsed_Switches; FS : in out File_Specific);
      procedure Set_Output_Mode (Parsed : Parsed_Switches);
      procedure Set_Warning_Mode (Parsed : Parsed_Switches);
      procedure Set_Report_Mode (Parsed : Parsed_Switches);

      procedure Set_Level_Timeout_Steps_Provers
        (Parsed : Parsed_Switches; FS : out File_Specific);
      --  Using the --level, --timeout, --steps, --provers, --ce-steps,
      --  --counterexamples and --proof-warning-timeout switches, set the
      --  corresponding variables.

      procedure Set_Proof_Mode
        (Parsed : Parsed_Switches; FS : in out File_Specific);
      procedure Process_Limit_Switches (Parsed : in out Parsed_Switches);
      procedure Set_Provers
        (Parsed : Parsed_Switches; FS : in out File_Specific);
      procedure Set_Proof_Dir (View : GPR2.Project.View.Object);
      --  If attribute Proof_Dir is set in the project file,
      --  set global variable Proof_Dir to the full path
      --  <path-to-project-file>/<value-of-proof-dir>.

      procedure Sanity_Checking (Parsed : Parsed_Switches);
      --  Check the command line flags for conflicting flags

      function List_From_Attr
        (Attribute : GPR2.Project.Attribute.Object) return String_List_Access;
      --  Helper function to convert attribute to list of strings

      function Source_Key
        (View : Project.View.Object; Fn : String) return String;
      --  Return the file-specific map key for source Fn in View

      function Switch_String
        (Parsed : Parsed_Switches; Switch : Switch_Id) return String;
      --  Return the string value for Switch or the empty string when unset

      -----------------------------------
      -- Check_Obsolete_Prove_Switches --
      -----------------------------------

      procedure Check_Obsolete_Prove_Switches (View : Project.View.Object) is
      begin
         if View.Attribute ((+"Prove", +"Switches")).Is_Defined then
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: attribute ""Switches"" of package ""Prove"" of "
               & "your project file is deprecated");
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: use ""Proof_Switches (""Ada"")"" instead");
         end if;
         null;
      end Check_Obsolete_Prove_Switches;

      -------------------------------
      -- File_Specific_Postprocess --
      -------------------------------

      procedure File_Specific_Postprocess
        (Parsed : Parsed_Switches; FS : out File_Specific) is
      begin
         Set_Level_Timeout_Steps_Provers (Parsed, FS);
         Set_Proof_Mode (Parsed, FS);
         Set_Mode (Parsed, FS);
         FS.No_Inlining := Parsed.Values (Sw_No_Inlining).Boolean_Val;
         FS.No_Loop_Unrolling :=
           Parsed.Values (Sw_No_Loop_Unrolling).Boolean_Val;
         FS.Proof_Warnings := Proof_Warnings;
         FS.No_Inlining :=
           Parsed.Values (Sw_No_Inlining).Boolean_Val
           or Parsed.Values (Sw_No_Global_Generation).Boolean_Val;
         for WK in Misc_Warning_Kind loop
            FS.Warning_Status (WK) :=
              (if Parsed.Warning_Status (WK) /= WS_None
               then Parsed.Warning_Status (WK)
               else VC_Kinds.Warning_Status (WK));
         end loop;
      end File_Specific_Postprocess;

      ----------
      -- Init --
      ----------

      procedure Init
        (Tree : out Project.Tree.Object; Opt : in out GPR2.Options.Object)
      is
         Subdir   : constant String :=
           Ada.Directories.Compose (To_String (Opt.Subdirs), "gnatprove");
         Status   : Boolean;
         Reporter : constant Spark_Reporter :=
           (GPR2.Reporter.Console.Create (GPR2.Reporter.Regular)
            with null record);
      begin
         Opt.Add_Switch (Options.Subdirs, Subdir, Override => True);

         if Opt.No_Project then
            Fail ("gnatprove doesn't support --no-project option");
         end if;

         if not Opt.Project_File.Is_Defined then
            Opt.Add_Switch (Options.P, No_Project_File_Mode, Override => True);
         end if;

         Status :=
           Tree.Load
             (Opt,
              Reporter         => Reporter,
              With_Runtime     => True,
              Absent_Dir_Error => GPR2.No_Error);

         if not Status then
            Fail ("");
         end if;

         if not Tree.Update_Sources then
            Fail ("");
         end if;
      end Init;

      --------------------
      -- List_From_Attr --
      --------------------

      function List_From_Attr
        (Attribute : GPR2.Project.Attribute.Object)
         return GNAT.Strings.String_List_Access is
      begin
         if Attribute.Is_Defined then
            declare
               List : constant GNAT.Strings.String_List_Access :=
                 new GNAT.Strings.String_List
                       (1 .. Integer (Attribute.Count_Values));
               I    : Integer := 1;
            begin
               for Value of Attribute.Values loop
                  List (I) := new String'(Value.Text);
                  I := I + 1;
               end loop;
               return List;
            end;
         else
            return null;
         end if;
      end List_From_Attr;

      ----------------
      -- Source_Key --
      ----------------

      function Source_Key
        (View : Project.View.Object; Fn : String) return String is
      begin
         return View.Source (GPR2.Simple_Name (Fn)).Path_Name.String_Value;
      end Source_Key;

      -------------------
      -- Switch_String --
      -------------------

      function Switch_String
        (Parsed : Parsed_Switches; Switch : Switch_Id) return String
      is
         Value : constant GNAT.Strings.String_Access :=
           Parsed.Values (Switch).String_Val;
      begin
         if Value = null then
            return "";
         else
            return Value.all;
         end if;
      end Switch_String;

      -------------------------------------------------
      -- Warn_And_Strip_Non_Root_Invocation_Switches --
      -------------------------------------------------

      procedure Warn_And_Strip_Non_Root_Invocation_Switches
        (View           : Project.View.Object;
         Attribute_Name : String;
         Switches       : in out Parsed_Switches)
      is
         function Switch_Image (Switch : Switch_Id) return String;
         --  Return the preferred user-facing spelling for Switch

         ------------------
         -- Switch_Image --
         ------------------

         function Switch_Image (Switch : Switch_Id) return String is
         begin
            if Switch_Definitions (Switch).Long /= null then
               return Switch_Definitions (Switch).Long.all;
            else
               return Switch_Definitions (Switch).Short.all;
            end if;
         end Switch_Image;

      begin
         for Switch in Invocation_Switch_Id loop
            if Switches.Present (Switch) then
               Ada.Text_IO.Put_Line
                 (Ada.Text_IO.Standard_Error,
                  "warning: invocation switch """
                  & Switch_Image (Switch)
                  & """ in attribute """
                  & Attribute_Name
                  & """ of non-root project """
                  & View.Path_Name.String_Value
                  & """ is ignored");
               Switches.Values (Switch) := Initial_Switch_Value (Switch);
               Switches.Present (Switch) := False;
            end if;
         end loop;
      end Warn_And_Strip_Non_Root_Invocation_Switches;

      -------------------------------
      -- Parse_Analysis_Attributes --
      -------------------------------

      procedure Parse_Analysis_Attributes
        (Command_Line : Parsed_Switches; Root_Attributes : Parsed_Switches)
      is
         use type Project.View.Object;

         procedure Expand_Ada_Switches (View : Project.View.Object);
         --  Replace the "Ada" section of the File_Specific_Map by entries for
         --  all files in the project, except for those which already have an
         --  entry.

         procedure Expand_Ada_Switches (View : Project.View.Object) is

            Gen : constant File_Specific := File_Specific_Map ("Ada");

            Messages : GPR2.Log.Object;
            pragma Unreferenced (Messages);
            Units    : constant GPR2.Build.Compilation_Unit.Maps.Map :=
              View.Own_Units;
            Position : File_Specific_Maps.Cursor;
            Inserted : Boolean;
         begin
            File_Specific_Map.Delete ("Ada");
            for C in Units.Iterate loop
               File_Specific_Map.Insert
                 (Key      => File_Specific_Key (Units (C)),
                  New_Item => Gen,
                  Position => Position,
                  Inserted => Inserted);
            end loop;
         end Expand_Ada_Switches;

         First : Boolean := True;
      begin

         for Cursor in
           Tree.Iterate
             (Status =>
                [GPR2.Project.S_Externally_Built =>
                   GNATCOLL.Tribooleans.False])
         loop
            declare
               View               : constant Project.View.Object :=
                 Project.Tree.Element (Cursor);
               FS                 : File_Specific;
               Prove_Switches     : constant String_List_Access :=
                 List_From_Attr (View.Attribute ((+"Prove", +"Switches")));
               Proof_Switches_Ada : constant String_List_Access :=
                 List_From_Attr
                   (View.Attribute
                      ((+"Prove", +"Proof_Switches"),
                       Index => GPR2.Project.Attribute_Index.Create ("Ada")));
               Project_Switches   : Parsed_Switches;
            begin

               --  Parse all switches that apply to all files, then merge them
               --  in the right order (most important is last). The root
               --  attributes are already part of Root_Attributes.

               if View = Tree.Root_Project then
                  Merge_Parsed_Switches (Project_Switches, Root_Attributes);
               end if;

               if Prove_Switches /= null then
                  declare
                     Parsed : Parsed_Switches :=
                       Parse_Switches_Internal
                         (Global_Switches_Only, Prove_Switches.all);
                  begin
                     if View /= Tree.Root_Project then
                        Warn_And_Strip_Non_Root_Invocation_Switches
                          (View, "Switches", Parsed);
                     end if;
                     Merge_Parsed_Switches (Project_Switches, Parsed);
                  end;
               end if;

               if Proof_Switches_Ada /= null then
                  declare
                     Parsed : Parsed_Switches :=
                       Parse_Switches_Internal
                         (Global_Switches_Only, Proof_Switches_Ada.all);
                  begin
                     if View /= Tree.Root_Project then
                        Warn_And_Strip_Non_Root_Invocation_Switches
                          (View, "Proof_Switches (""Ada"")", Parsed);
                     end if;
                     Merge_Parsed_Switches (Project_Switches, Parsed);
                  end;
               end if;

               declare
                  Effective : Parsed_Switches;
               begin
                  --  Use the merge helper for a deep copy
                  Merge_Parsed_Switches (Effective, Project_Switches);
                  Merge_Parsed_Switches (Effective, Command_Line);
                  Postprocess (Effective);
                  File_Specific_Postprocess (Effective, FS);
               end;
               File_Specific_Map.Include ("Ada", FS);
               Has_Coq_Prover := Case_Insensitive_Contains (FS.Provers, "coq");
               Has_Manual_Prover :=
                 FS.Provers.Length = 1
                 and then
                   (Case_Insensitive_Contains (FS.Provers, "coq")
                    or else
                      Case_Insensitive_Contains (FS.Provers, "isabelle"));

               for Attr of View.Attributes ((+"Prove", +"Proof_Switches")) loop
                  if Attr.Index.Text not in "Ada" | "ada" then
                     Check_File_Part_Of_Project (View, Attr.Index.Text);
                     declare
                        FS          : File_Specific;
                        FS_Switches : constant String_List_Access :=
                          List_From_Attr (Attr);
                        Effective   : Parsed_Switches;
                     begin
                        --  Use the merge helper for a deep copy
                        Merge_Parsed_Switches (Effective, Project_Switches);

                        if FS_Switches /= null then

                           --  parse the file switches to check if they contain
                           --  invalid switches; this is for error reporting
                           --  only.

                           Merge_Parsed_Switches
                             (Effective,
                              Parse_Switches_Internal
                                (File_Specific_Only, FS_Switches.all));
                        end if;

                        --  Apply the command-line switches last, so they
                        --  override file-specific project switches.

                        Merge_Parsed_Switches (Effective, Command_Line);
                        Postprocess (Effective);
                        File_Specific_Postprocess (Effective, FS);
                        File_Specific_Map.Include
                          (Source_Key (View, Attr.Index.Text), FS);
                     end;
                  end if;
               end loop;
               if First then
                  First := False;
                  declare
                     Default : constant File_Specific :=
                       File_Specific_Map ("Ada");
                  begin
                     File_Specific_Map.Include ("default", Default);
                  end;
               end if;
               Expand_Ada_Switches (View);
            end;
         end loop;
      end Parse_Analysis_Attributes;

      -----------------
      -- Postprocess --
      -----------------

      procedure Postprocess (Parsed : in out Parsed_Switches) is
         function On_Path (Exec : String) return Boolean;
         --  Return True iff Exec is present on PATH

         -------------
         -- On_Path --
         -------------

         function On_Path (Exec : String) return Boolean is
            Location : String_Access := GNAT.OS_Lib.Locate_Exec_On_Path (Exec);

            Present : constant Boolean := Location /= null;

         begin
            Free (Location);
            return Present;
         end On_Path;

      begin
         Sanity_Checking (Parsed);

         SPARK_Install.Z3_Present := On_Path ("z3");
         SPARK_Install.CVC5_Present := On_Path ("cvc5");
         SPARK_Install.Colibri_Present := On_Path ("colibri");

         Debug :=
           Parsed.Values (Sw_D).Boolean_Val
           or Parsed.Values (Sw_Flow_Debug).Boolean_Val;
         Debug_Exec_RAC := Parsed.Values (Sw_Debug_Exec_RAC).Boolean_Val;

         --  Subprograms with no contracts (and a few other criteria) may be
         --  inlined, as this can help provability. In particular it helps as
         --  the user does not need to write a pre- or post-condition. As a
         --  side-effect it also effectively produces a global and depends
         --  contract.
         --
         --  The --no-global-generation switch implies not inlining from two
         --  points of view:
         --
         --     * (logical) By its name, it implies that globals should not be
         --       generated, and inlining has the effect of generating globals.
         --
         --     * (practical) As inlined subprograms are analyzed separately
         --       anyway in order to check for flow issues, flow would reject
         --       all but the most trivial subprograms, since a missing global
         --       generates an error, not a check. Fixing this would require a
         --       global contract, which in turn would eliminate inlining
         --       anyway.

         --  Adjust the number of parallel processes. If -j0 was used, the
         --  number of processes should be set to the actual number of
         --  processors available on the machine.

         if Parsed.Values (Sw_J).Integer_Val = 0 then
            Parallel := Natural (System.Multiprocessors.Number_Of_CPUs);
         elsif Parsed.Values (Sw_J).Integer_Val < 0 then
            Abort_Msg ("error: wrong argument for -j", With_Help => False);
         else
            Parallel := Parsed.Values (Sw_J).Integer_Val;
         end if;

         if Parsed.Values (Sw_No_Counterexample).Boolean_Val then
            Ada.Text_IO.Put_Line
              ("Note: switch ""--no-counterexample"" is ignored.");
            Ada.Text_IO.Put_Line
              ("Note: use ""--counterexamples=off"" instead.");
         end if;

         if Parsed.Values (Sw_No_Axiom_Guard).Boolean_Val then
            Ada.Text_IO.Put_Line
              ("Note: switch ""--no-axiom-guard"" is ignored.");
            Ada.Text_IO.Put_Line
              ("Note: use ""--function-sandboxing=off"" instead.");
         end if;

         if Switch_String (Parsed, Sw_Function_Sandboxing)
            not in "" | "on" | "off"
         then
            Abort_Msg
              ("error: wrong argument for --function-sandboxing, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         if Switch_String (Parsed, Sw_Checks_As_Errors) = ""
           or else Switch_String (Parsed, Sw_Checks_As_Errors) = "off"
         then
            Checks_As_Errors := False;
         elsif Switch_String (Parsed, Sw_Checks_As_Errors) = "on" then
            Checks_As_Errors := True;
         else
            Abort_Msg
              ("error: wrong argument """
               & Switch_String (Parsed, Sw_Checks_As_Errors)
               & """ for --checks-as-errors, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         if Switch_String (Parsed, Sw_Proof_Warnings) = ""
           or else Switch_String (Parsed, Sw_Proof_Warnings) = "off"
         then
            Proof_Warnings := False;
         elsif Switch_String (Parsed, Sw_Proof_Warnings) = "on" then
            Proof_Warnings := True;
         else
            Abort_Msg
              ("error: wrong argument """
               & Switch_String (Parsed, Sw_Proof_Warnings)
               & """ for --proof-warnings, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         --  Handling of Only_Given and Filelist

         Only_Given :=
           Parsed.Values (Sw_U).Boolean_Val
           or else Switch_String (Parsed, Sw_Limit_Subp) /= ""
           or else Switch_String (Parsed, Sw_Limit_Line) /= ""
           or else Switch_String (Parsed, Sw_Limit_Lines) /= "";

         if Parsed.Values (Sw_U).Boolean_Val and then Parsed.File_List.Is_Empty
         then
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: switch -u without a file name is equivalent to "
               & "switch --no-subproject");
         end if;

         Process_Limit_Switches (Parsed);

         GnateT_Switch := new String'(Check_gnateT_Switch (Tree.Root_Project));
         Set_Output_Mode (Parsed);
         Set_Warning_Mode (Parsed);
         Set_Report_Mode (Parsed);
         Set_Proof_Dir (Tree.Root_Project);

         Use_Semaphores :=
           not Debug and then not Parsed.Values (Sw_Dbg_No_Sem).Boolean_Val;
      end Postprocess;

      ----------------------------
      -- Process_Limit_Switches --
      ----------------------------

      procedure Process_Limit_Switches (Parsed : in out Parsed_Switches) is

         Switch_Count : Integer := 0;

         procedure Check_Switch (Arg : GNAT.Strings.String_Access);
         --  Increase Switch_Count by one if arg is not the null pointer or
         --  empty string.

         procedure Process_Limit_Directive (Msg, Limit_String : String);
         --  Check if the Limit_String is a valid directive. Use Msg for error
         --  message prefix. If valid, add the file mentioned in the limit
         --  directive to the list of files.

         procedure Process_Limit_Directive
           (Msg : String; Limit_String : GNAT.Strings.String_Access);
         --  Same, but do nothing if Limit_String is the null pointer or empty
         --  string.

         procedure Process_Limit_Line (Spec : String);
         --  Sanity check the argument to --limit-line or an entry in
         --  --limit-lines. Also, add the argument to the Limit_Lines list.

         ------------------
         -- Check_Switch --
         ------------------

         procedure Check_Switch (Arg : GNAT.Strings.String_Access) is
         begin
            if not Null_Or_Empty_String (Arg) then
               Switch_Count := Switch_Count + 1;
            end if;
         end Check_Switch;

         -----------------------------
         -- Process_Limit_Directive --
         -----------------------------

         procedure Process_Limit_Directive (Msg, Limit_String : String) is
            Colon_Index : constant Natural :=
              Ada.Strings.Fixed.Index (Source => Limit_String, Pattern => ":");
         begin
            if Colon_Index = 0 then
               Abort_Msg
                 (Msg
                  & ": incorrect line specification"
                  & " - missing ':' followed by operand",
                  With_Help => False);
            end if;

            --  Unless -U is specified, use of --limit-[line,region,subp] leads
            --  to only the file with the given line or subprogram to be
            --  analyzed.  Specifying -U with --limit-[line,region,subp] is
            --  useful to force analysis of all files, when the line or
            --  subprogram is inside a generic or itself a generic, so that all
            --  instances of the line/subprogram are analyzed.

            if not Parsed.Values (Sw_UU).Boolean_Val then
               Parsed.File_List.Append
                 (Limit_String (Limit_String'First .. Colon_Index - 1));
            end if;
         end Process_Limit_Directive;

         procedure Process_Limit_Directive
           (Msg : String; Limit_String : GNAT.Strings.String_Access) is
         begin
            if not Null_Or_Empty_String (Limit_String) then
               Process_Limit_Directive (Msg, Limit_String.all);
            end if;
         end Process_Limit_Directive;

         ------------------------
         -- Process_Limit_Line --
         ------------------------

         procedure Process_Limit_Line (Spec : String) is
            --  Matching sequences of file:line, separated by :
            --  then optional :column:check suffix.
            --  (?:...) is a non-capturing group
            Regex : constant String :=
              "^[^:]+:[0-9]+(?::[^:]+:[0-9+])*(?::[0-9]+:([^:]+))?$";
            MA    : Match_Array (0 .. 1);
            Kind  : VC_Kind;
            pragma Unreferenced (Kind);
         begin
            Match (Regex, Spec, MA);
            if MA (0) = No_Match then
               Abort_Msg
                 ("incorrect line specification: """ & Spec & """",
                  With_Help => False);
            end if;
            if MA (1) /= No_Match then
               begin
                  Kind := VC_Kind'Value (Spec (MA (1).First .. MA (1).Last));
               exception
                  when Constraint_Error =>
                     Abort_Msg
                       ("incorrect check name in line specification: "
                        & Spec (MA (1).First .. MA (1).Last),
                        With_Help => False);
               end;
            end if;
            Limit_Lines.Append (Spec);
         end Process_Limit_Line;

      begin

         --  We do not allow mixing of --limit-* switches, except for the
         --  combination of --limit-subp + --limit-line or --limit-region,
         --  as this is used by the gnatstudio plug-in.

         Check_Switch (Parsed.Values (Sw_Limit_Name).String_Val);
         Check_Switch (Parsed.Values (Sw_Limit_Subp).String_Val);
         Check_Switch (Parsed.Values (Sw_Limit_Region).String_Val);
         Check_Switch (Parsed.Values (Sw_Limit_Line).String_Val);
         Check_Switch (Parsed.Values (Sw_Limit_Lines).String_Val);
         if Switch_Count > 1 then
            if Switch_Count = 2
              and then
                not Null_Or_Empty_String
                      (Parsed.Values (Sw_Limit_Subp).String_Val)
              and then
                (not Null_Or_Empty_String
                       (Parsed.Values (Sw_Limit_Region).String_Val)
                 or else
                   not Null_Or_Empty_String
                         (Parsed.Values (Sw_Limit_Line).String_Val))
            then
               null;
            else
               Abort_Msg
                 ("Switches --limit-line, --limit-name, --limit-region and "
                  & "--limit-subp are mutually exclusive",
                  With_Help => False);
            end if;
         end if;

         Process_Limit_Directive
           ("limit-subp", Parsed.Values (Sw_Limit_Subp).String_Val);
         Process_Limit_Directive
           ("limit-region", Parsed.Values (Sw_Limit_Region).String_Val);
         Process_Limit_Directive
           ("limit-line", Parsed.Values (Sw_Limit_Line).String_Val);
         if not Null_Or_Empty_String (Parsed.Values (Sw_Limit_Line).String_Val)
         then
            Process_Limit_Line (Parsed.Values (Sw_Limit_Line).String_Val.all);
         end if;
         if not Null_Or_Empty_String
                  (Parsed.Values (Sw_Limit_Lines).String_Val)
         then
            declare
               File_Handle : Ada.Text_IO.File_Type;
               Line_Count  : Integer := 1;
            begin
               Ada.Text_IO.Open
                 (File_Handle,
                  Ada.Text_IO.In_File,
                  Parsed.Values (Sw_Limit_Lines).String_Val.all);
               while True loop
                  declare
                     Line : constant String :=
                       Trim
                         (Ada.Text_IO.Get_Line (File_Handle),
                          Ada.Strings.Both);
                  begin
                     if Line /= "" then
                        Process_Limit_Directive
                          ("limit-lines: line" & Integer'Image (Line_Count),
                           Line);
                        Process_Limit_Line (Line);
                     end if;
                     Line_Count := Line_Count + 1;
                  end;
               end loop;
            exception
               when Ada.IO_Exceptions.End_Error =>
                  Ada.Text_IO.Close (File_Handle);
            end;
         end if;
      end Process_Limit_Switches;

      ---------------------
      -- Sanity_Checking --
      ---------------------

      procedure Sanity_Checking (Parsed : Parsed_Switches) is
      begin
         if (Parsed.Values (Sw_Output_Msg_Only).Boolean_Val
             and then Parsed.Values (Sw_Replay).Boolean_Val)
           or else
             (Parsed.Values (Sw_Output_Msg_Only).Boolean_Val
              and then Parsed.Values (Sw_F).Boolean_Val)
           or else
             (Parsed.Values (Sw_F).Boolean_Val
              and then Parsed.Values (Sw_Replay).Boolean_Val)
         then
            Abort_Msg
              ("only one switch out of -f, --output-msg-only and --replay"
               & " should be provided to gnatprove",
               With_Help => False);
         end if;
      end Sanity_Checking;

      -------------------------------------
      -- Set_Level_Timeout_Steps_Provers --
      -------------------------------------

      procedure Set_Level_Timeout_Steps_Provers
        (Parsed : Parsed_Switches; FS : out File_Specific)
      is
         procedure Apply_Level_Settings
           (Settings : Proof_Options.Proof_Level_Settings);
         --  Apply settings implied by --level before processing explicit
         --  switches that may override them.

         --------------------------
         -- Apply_Level_Settings --
         --------------------------

         procedure Apply_Level_Settings
           (Settings : Proof_Options.Proof_Level_Settings) is
         begin
            FS.Provers := Proof_Options.Provers_For (Settings.Provers);
            FS.Steps := Settings.Steps;
            FS.Timeout := Settings.Timeout;
            FS.Memlimit := Settings.Memlimit;
            FS.Counterexamples := Settings.Counterexamples;
         end Apply_Level_Settings;
      begin

         if Parsed.Values (Sw_Level).Integer_Val = Invalid_Level then

            --  If level switch was not provided, set other switches to their
            --  default values.

            FS.Provers := Proof_Options.Provers_For (Proof_Options.CVC5_Only);

            --  Default steps are used only if none of --steps and --timeout
            --  is used (either explicitly or through --level). Otherwise
            --  set to zero to indicate steps are not used.

            if Parsed.Values (Sw_Steps).Integer_Val = Invalid_Steps
              and then Switch_String (Parsed, Sw_Timeout) = ""
            then
               FS.Steps := Proof_Options.Default_Steps;
            else
               FS.Steps := 0;
            end if;

            FS.Timeout := 0;
            FS.Memlimit := 0;
            FS.Counterexamples := False;

         elsif Parsed.Values (Sw_Level).Integer_Val
               in Proof_Options.Proof_Level
         then
            Apply_Level_Settings
              (Proof_Options.Settings_For_Level
                 (Parsed.Values (Sw_Level).Integer_Val));

         else
            Abort_Msg
              ("error: wrong argument for --level", With_Help => False);
         end if;

         FS.Check_Counterexamples := True;
         FS.CE_Steps := 0;
         FS.Proof_Warn_Timeout := Invalid_Timeout;

         --  If option --timeout was not provided, keep timeout corresponding
         --  to level switch/default value. Otherwise, take the user-provided
         --  timeout. To be able to detect if --timeout was provided,
         --  Parsed timeout is string-based.

         if Switch_String (Parsed, Sw_Timeout) = "" then
            null;
         else
            begin
               FS.Timeout :=
                 Integer'Value (Switch_String (Parsed, Sw_Timeout));
               if FS.Timeout < 0 then
                  raise Constraint_Error;
               end if;
            exception
               when Constraint_Error =>
                  Abort_Msg
                    ("error: wrong argument for --timeout, "
                     & "must be a non-negative integer",
                     With_Help => False);
            end;
         end if;

         if Parsed.Values (Sw_Memlimit).Integer_Val = 0 then
            null;
         elsif Parsed.Values (Sw_Memlimit).Integer_Val < 0 then
            Abort_Msg
              ("error: wrong argument for --memlimit, "
               & "must be a non-negative integer",
               With_Help => False);
         else
            FS.Memlimit := Parsed.Values (Sw_Memlimit).Integer_Val;
         end if;

         if Parsed.Values (Sw_Steps).Integer_Val = Invalid_Steps then
            null;
         elsif Parsed.Values (Sw_Steps).Integer_Val < 0 then
            Abort_Msg
              ("error: wrong argument for --steps", With_Help => False);
         else
            FS.Steps := Parsed.Values (Sw_Steps).Integer_Val;
         end if;

         if Parsed.Values (Sw_CE_Steps).Integer_Val = Invalid_Steps then
            null;
         elsif Parsed.Values (Sw_CE_Steps).Integer_Val < 0 then
            Abort_Msg
              ("error: wrong argument for --ce-steps", With_Help => False);
         else
            FS.CE_Steps := Parsed.Values (Sw_CE_Steps).Integer_Val;
         end if;

         if Parsed.Values (Sw_Proof_Warn_Timeout).Integer_Val = Invalid_Timeout
         then
            null;
         elsif Parsed.Values (Sw_Proof_Warn_Timeout).Integer_Val < 0 then
            Abort_Msg
              ("error: wrong argument for --proof-warn-timeout",
               With_Help => False);
         else
            FS.Proof_Warn_Timeout :=
              Parsed.Values (Sw_Proof_Warn_Timeout).Integer_Val;
         end if;

         --  Timeout and CE_Steps are fully set now, we can set CE_Timeout.
         --  When steps are used, set timeout for counterexamples to 0.
         --  Otherwise, we cap the CE_Timeout at Constants.Max_CE_Timeout
         --  seconds.

         FS.CE_Timeout :=
           (if FS.CE_Steps > 0
            then 0
            elsif FS.Timeout = 0
            then Constants.Max_CE_Timeout
            else Integer'Min (FS.Timeout, Constants.Max_CE_Timeout));

         Set_Provers (Parsed, FS);

         if Parsed.Values (Sw_Output_Msg_Only).Boolean_Val then
            FS.Provers.Clear;
         end if;

         if Switch_String (Parsed, Sw_Counterexamples) = "" then
            null;
         elsif Switch_String (Parsed, Sw_Counterexamples) = "on" then
            FS.Counterexamples := True;
         elsif Switch_String (Parsed, Sw_Counterexamples) = "off" then
            FS.Counterexamples := False;
         else
            Abort_Msg
              ("error: wrong argument for --counterexamples, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         FS.Counterexamples :=
           FS.Counterexamples
           and then SPARK_Install.CVC5_Present
           and then not Has_Manual_Prover
           and then not Parsed.Values (Sw_Output_Msg_Only).Boolean_Val;

         if Switch_String (Parsed, Sw_Check_Counterexamples) = "" then
            null;
         elsif Switch_String (Parsed, Sw_Check_Counterexamples) = "on" then
            FS.Check_Counterexamples := True;
         elsif Switch_String (Parsed, Sw_Check_Counterexamples) = "off" then
            FS.Check_Counterexamples := False;
         else
            Abort_Msg
              ("error: wrong argument for --check-counterexamples, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         FS.Check_Counterexamples :=
           FS.Counterexamples and then FS.Check_Counterexamples;

      end Set_Level_Timeout_Steps_Provers;

      --------------
      -- Set_Mode --
      --------------

      procedure Set_Mode (Parsed : Parsed_Switches; FS : in out File_Specific)
      is
      begin
         if Switch_String (Parsed, Sw_Mode) = "" then
            FS.Mode := GPM_All;
         elsif Switch_String (Parsed, Sw_Mode) = "prove" then
            FS.Mode := GPM_Prove;
         elsif Switch_String (Parsed, Sw_Mode) = "check" then
            FS.Mode := GPM_Check;
         elsif Switch_String (Parsed, Sw_Mode) = "check_all"
           or else Switch_String (Parsed, Sw_Mode) = "stone"
         then
            FS.Mode := GPM_Check_All;
         elsif Switch_String (Parsed, Sw_Mode) = "flow"
           or else Switch_String (Parsed, Sw_Mode) = "bronze"
         then
            FS.Mode := GPM_Flow;
         elsif Switch_String (Parsed, Sw_Mode) = "all"
           or else Switch_String (Parsed, Sw_Mode) = "silver"
           or else Switch_String (Parsed, Sw_Mode) = "gold"
         then
            FS.Mode := GPM_All;
         else
            Abort_Msg ("error: wrong argument for --mode", With_Help => False);
         end if;

         --  Update mode to the highest we have seen
         --  This follows the logic that Check < Check_All < Flow | Proof <
         --  All.

         if Mode = GPM_All then
            null;
         elsif (Mode = GPM_Flow and then FS.Mode in GPM_Prove | GPM_All)
           or else (Mode = GPM_Prove and then FS.Mode in GPM_Flow | GPM_All)
         then
            Mode := GPM_All;
         elsif Mode = GPM_Check_All
           and then FS.Mode in GPM_Prove | GPM_Flow | GPM_All
         then
            Mode := FS.Mode;
         elsif Mode = GPM_Check then
            Mode := FS.Mode;
         end if;
      end Set_Mode;

      ---------------------
      -- Set_Output_Mode --
      ---------------------

      procedure Set_Output_Mode (Parsed : Parsed_Switches) is
      begin
         if Switch_String (Parsed, Sw_Output) = "" then
            Output := GPO_Pretty_Simple;
         elsif Switch_String (Parsed, Sw_Output) = "brief" then
            Output := GPO_Brief;
         elsif Switch_String (Parsed, Sw_Output) = "oneline" then
            Output := GPO_Oneline;
         elsif Switch_String (Parsed, Sw_Output) = "pretty" then
            Output := GPO_Pretty_Simple;
         else
            Abort_Msg
              ("error: wrong argument for --output", With_Help => False);
         end if;

         --  When outputting to a terminal, switch automatically to colored
         --  output when pretty output is requested.

         if Output = GPO_Pretty_Simple then
            declare
               function Stdout_Set_Colors return Integer;
               pragma Import (C, Stdout_Set_Colors, "stdout_set_colors");
               Colors_Supported : constant Boolean := Stdout_Set_Colors /= 0;
            begin
               if Colors_Supported then
                  Output := GPO_Pretty_Color;
               end if;
            end;
         end if;
      end Set_Output_Mode;

      -------------------
      -- Set_Proof_Dir --
      -------------------

      procedure Set_Proof_Dir (View : GPR2.Project.View.Object) is
         Attr : GPR2.Project.Attribute.Object;
      begin
         if View.Check_Attribute ((+"Prove", +"Proof_Dir"), Result => Attr)
         then
            declare
               My_Proof_Dir : constant Virtual_File :=
                 Create (Filesystem_String (Attr.Value.Text));
               Proj_Dir     : constant Virtual_File :=
                 Create
                   (Filesystem_String (Tree.Root_Project.Path_Name.Dir_Name));
               Full_Name    : constant Virtual_File :=
                 (if Is_Absolute_Path (My_Proof_Dir)
                  then My_Proof_Dir
                  else
                    Create_From_Dir
                      (Proj_Dir, Filesystem_String (Attr.Value.Text)));
            begin
               Full_Name.Normalize_Path;
               Proof_Dir := new String'(Full_Name.Display_Full_Name);
            end;
         end if;
      end Set_Proof_Dir;

      --------------------
      -- Set_Proof_Mode --
      --------------------

      procedure Set_Proof_Mode
        (Parsed : Parsed_Switches; FS : in out File_Specific)
      is
         Input       : constant String := Switch_String (Parsed, Sw_Proof);
         Colon_Index : constant Natural :=
           Index (Source => Input, Pattern => ":");

         Proof_Input : constant String :=
           (if Colon_Index /= 0
            then Input (Input'First .. Colon_Index - 1)
            else Input);
         Lazy_Input  : constant String :=
           (if Colon_Index /= 0
            then Input (Colon_Index + 1 .. Input'Last)
            else "");

      begin
         if Proof_Input = "" then
            FS.Proof := Per_Check;
         elsif Proof_Input = "progressive" then
            FS.Proof := Progressive;
         elsif Proof_Input = "per_path" then
            FS.Proof := Per_Path;
         elsif Proof_Input = "per_check" then
            FS.Proof := Per_Check;

         --  Hidden debugging values

         elsif Proof_Input = "no_wp" then
            FS.Proof := No_WP;
         elsif Proof_Input = "all_split" then
            FS.Proof := All_Split;
         else
            Abort_Msg
              ("error: wrong argument for --proof", With_Help => False);
         end if;

         if Lazy_Input = "" then
            FS.Lazy := True;
         elsif Lazy_Input = "all" then
            FS.Lazy := False;
         elsif Lazy_Input = "lazy" then
            FS.Lazy := True;
         else
            Abort_Msg
              ("error: wrong argument for --proof", With_Help => False);
         end if;
      end Set_Proof_Mode;

      -----------------
      -- Set_Provers --
      -----------------

      procedure Set_Provers
        (Parsed : Parsed_Switches; FS : in out File_Specific)
      is
         First : Integer;
         S     : constant String := Switch_String (Parsed, Sw_Prover);

      begin
         --  This procedure is called when the Provers list is already filled
         --  with the defaults from the --level switch.
         --  In replay mode, we only want to take into account provers when
         --  they were explicitly set, not when set by default. When not
         --  in replay mode, we only need to change the Provers list when
         --  --provers was explicitly set.

         if S = "" then
            if Parsed.Values (Sw_Replay).Boolean_Val then
               FS.Provers.Clear;
            end if;
            return;
         end if;
         FS.Provers.Clear;
         if S /= "all" then
            First := S'First;
            for Cur in S'Range loop
               if S (Cur) = ',' then
                  FS.Provers.Append (S (First .. Cur - 1));
                  First := Cur + 1;
               end if;
            end loop;
            if S /= "" then
               FS.Provers.Append (S (First .. S'Last));
            end if;

            --  Check if cvc5/z3/colibri have explicitly been requested, but
            --  are missing from the install.

            for Prover of FS.Provers loop
               if (Prover = "cvc5" and then not SPARK_Install.CVC5_Present)
                 or else (Prover = "z3" and then not SPARK_Install.Z3_Present)
                 or else
                   (Prover = "colibri"
                    and then not SPARK_Install.Colibri_Present)
               then
                  Abort_Msg
                    ("error: prover "
                     & Prover
                     & " was selected, but it is not installed",
                     With_Help => False);
               end if;
            end loop;

         --  prover switch is set to "all"

         else
            if SPARK_Install.CVC5_Present then
               FS.Provers.Append ("cvc5");
            end if;
            if SPARK_Install.Z3_Present then
               FS.Provers.Append ("z3");
            end if;
            if SPARK_Install.Colibri_Present then
               FS.Provers.Append ("colibri");
            end if;
            FS.Provers.Append ("altergo");
         end if;
      end Set_Provers;

      ---------------------
      -- Set_Report_Mode --
      ---------------------

      procedure Set_Report_Mode (Parsed : Parsed_Switches) is
      begin
         if Switch_String (Parsed, Sw_Report) = "" then
            Report := GPR_Fail;
         elsif Switch_String (Parsed, Sw_Report) = "fail" then
            Report := GPR_Fail;
         elsif Switch_String (Parsed, Sw_Report) = "all" then
            Report := GPR_All;
         elsif Switch_String (Parsed, Sw_Report) = "provers" then
            Report := GPR_Provers;
         elsif Switch_String (Parsed, Sw_Report) = "statistics" then
            Report := GPR_Statistics;
         else
            Abort_Msg
              ("error: wrong argument for --report", With_Help => False);
         end if;
      end Set_Report_Mode;

      ----------------------
      -- Set_Warning_Mode --
      ----------------------

      procedure Set_Warning_Mode (Parsed : Parsed_Switches) is
         Warn_Switch : constant String := Switch_String (Parsed, Sw_Warnings);
      begin
         --  Note that "on" here is retained for backwards compatibility
         --  with release 14.0.1
         if Warn_Switch = "" then
            Warning_Mode := Gnat2Why_Opts.SW_Normal;
         elsif Warn_Switch = "off" then
            Warning_Mode := Gnat2Why_Opts.SW_Suppress;
         elsif Warn_Switch = "error" then
            Warning_Mode := Gnat2Why_Opts.SW_Treat_As_Error;
         elsif Warn_Switch = "on" or else Warn_Switch = "continue" then
            Warning_Mode := Gnat2Why_Opts.SW_Normal;
         else

            Abort_Msg
              ("error: wrong argument for --warnings", With_Help => False);
         end if;
      end Set_Warning_Mode;

      --  Local variables

      Full_Com_Lin : String_List :=
        [1 .. Ada.Command_Line.Argument_Count => <>];
      Com_Lin      : String_List_Access;

      Parse_Result            : Project_Parsing_Result;
      Command_Line_Switches   : Parsed_Switches;
      Invocation_Switches     : Parsed_Switches;
      Root_Attribute_Switches : Parsed_Switches;

   begin

      for Index in 1 .. Full_Com_Lin'Last loop
         Full_Com_Lin (Index) :=
           new String'(Ada.Command_Line.Argument (Index));
      end loop;

      --  The following code parses switches several times, with varying mode
      --  arguments and different switch lists, for different purposes:
      --   - detecting invalid switches in the various attributes; (so the
      --     parsing of a file-specific switch can't override a switch that can
      --     only be specified globally);
      --   - saving file-specific and global switches into separate records;
      --   - parsing for error messages is done before the "real" parsing to
      --     get the values of switches.

      --  This call just parses project-relevant switches
      --  (-P, -X etc) and ignores the rest.

      Set_Project_Attributes;
      Parse_Result := Parse_Switches_Before_Project_Parsing (Full_Com_Lin);
      Free (Full_Com_Lin);
      CL_Switches.Cargs_List.Clear;
      if Parse_Result.Cargs /= null then
         for Arg of Parse_Result.Cargs.all loop
            CL_Switches.Cargs_List.Append (Arg.all);
         end loop;
         Free (Parse_Result.Cargs);
      end if;
      Com_Lin := Parse_Result.Remaining_Args;

      if Parse_Result.Help then
         Display_Help;
         Succeed;
      end if;

      if Parse_Result.Version then
         Produce_Version_Output;
         Succeed;
      end if;

      if Parse_Result.List_Categories then
         Produce_List_Categories_Output;
         Succeed;
      end if;

      if Parse_Result.Explain /= Null_Unbounded_String then
         Produce_Explain_Output (To_String (Parse_Result.Explain));
         Succeed;
      end if;

      if Parse_Result.List_Explain_Codes then
         Produce_List_Explain_Codes_Output;
         Succeed;
      end if;

      if Parse_Result.Gpr_Registry then
         --  Print registered gpr attributes and exit as requested
         --  This should be done here before any warning/error outputs.

         GPR2.Project.Registry.Exchange.Export
           (Output => Ada.Text_IO.Put'Access);
         Succeed;
      end if;

      --  Before doing the actual second parsing, we read the project file in

      Init (Tree, Parse_Result.Opt);
      Check_Obsolete_Prove_Switches (Tree.Root_Project);

      if Parse_Result.Clean then
         Clean_Up (Tree);
         Succeed;
      end if;

      declare
         L : String_List_Access :=
           List_From_Attr
             (Tree.Root_Project.Attribute ((+"Prove", +"Switches")));
      begin
         if L /= null then
            Merge_Parsed_Switches
              (Root_Attribute_Switches,
               Parse_Switches_Internal (Global_Switches_Only, L.all));
            Free (L);
         end if;
      end;

      for Root_Attr of
        Tree.Root_Project.Attributes ((+"Prove", +"Proof_Switches"))
      loop
         if Root_Attr.Index.Text in "Ada" | "ada" then
            declare
               L : String_List_Access := List_From_Attr (Root_Attr);
            begin
               if L /= null then
                  Merge_Parsed_Switches
                    (Root_Attribute_Switches,
                     Parse_Switches_Internal (Global_Switches_Only, L.all));
                  Free (L);
               end if;
            end;
         end if;
      end loop;

      Command_Line_Switches :=
        Parse_Switches_Internal (All_Switches, Com_Lin.all);

      Parse_Analysis_Attributes
        (Command_Line_Switches, Root_Attribute_Switches);

      --  Derive the invocation-wide semantic configuration
      Merge_Parsed_Switches (Invocation_Switches, Root_Attribute_Switches);
      Merge_Parsed_Switches (Invocation_Switches, Command_Line_Switches);
      Postprocess (Invocation_Switches);
      Verbosity := Parse_Result.Verbosity;

      --  Publish the final invocation settings for legacy consumers
      Copy_To_CL_Switches (Invocation_Switches);

      --  ??? Need to move the proof manifest to the per-project part of
      --  cmd-line parsing, as each project can have its own manifest
      Load_Proof_Manifest;

      --  Release copies of command line arguments; they were already parsed
      --  twice and are no longer needed.
      Free (Com_Lin);

      --  Setting the socket name used by the why3server. This name has
      --  to comply to several constraints:
      --
      --  - It has to be unique for each project. This is because we want to
      --    allow simultaneous gnatprove runs on different projects, and on
      --    Windows, sockets/named pipes live in a global name space.
      --
      --  - It should be the same for each invocation of gnatprove of a
      --    given project. This is because we pass the socket name to
      --    gnatwhy3 via gnat2why command line (via Gnat2why_Args more
      --    precisely). If the command line changed on every invocation of
      --    gnatprove, gprbuild would rerun gnat2why even when not
      --    necessary.
      --
      --  What we have come up with until now is a hash of the project file
      --  name (full path).

      declare
         PID_String  : constant String := Integer'Image (Get_Process_Id);
         Socket_Dir  : constant String := Compute_Socket_Dir (Tree);
         Socket_Base : constant String :=
           "why3server_"
           & PID_String (PID_String'First + 1 .. PID_String'Last)
           & ".sock";
      begin
         Socket_Name :=
           new String'
             ((if Socket_Dir = ""
               then Socket_Base
               else Ada.Directories.Compose (Socket_Dir, Socket_Base)));
         if Has_Coq_Prover then
            Prepare_Prover_Lib
              (Tree.Root_Project.Object_Directory.String_Value);
         end if;
      end;
      Sanitize_File_List (Tree);
      Sanity_Check_SARIF_Base_URI (Tree);

      --  Set the maximum number of concurrent gnatwhy3 processes based on
      --  semaphore usage and the calculated parallelism level.
      if Use_Semaphores then
         declare
            Num_Provers : constant Positive :=
              Integer'Max
                (1, Integer (File_Specific_Map ("default").Provers.Length));
         begin
            Max_Why3_Processes := Integer'Max (1, Parallel / Num_Provers);
         end;
      else
         --  Sequential mode: limit to 1 process
         Max_Why3_Processes := 1;
      end if;

      --  Set reporter for build process
      declare
         Reporter       : Spark_Reporter :=
           (GPR2.Reporter.Console.Create (GPR2.Reporter.No_Warnings)
            with null record);
         User_Verbosity : constant GPR2.Reporter.User_Verbosity_Level :=
           (case Configuration.Verbosity is
              when Configuration.Verbose_Level => GPR2.Reporter.Verbose,
              when Configuration.Quiet_Level   => GPR2.Reporter.Important_Only,
              when Configuration.Normal_Level  => GPR2.Reporter.Regular);
      begin
         Reporter.Set_Verbosity (GPR2.Reporter.Regular);
         Reporter.Set_User_Verbosity (User_Verbosity);
         Tree.Set_Reporter (Reporter);
      end;
   end Read_Command_Line;

   ------------------------
   -- Sanitize_File_List --
   ------------------------

   procedure Sanitize_File_List (Tree : Project.Tree.Object) is
      use String_Lists;
   begin
      if File_List.Is_Empty then
         return;
      end if;

      --  We iterate over all names in the file list

      for Cursor in File_List.Iterate loop

         declare
            File_Entry       : String renames File_List (Cursor);
            Has_Path         : constant Boolean :=
              Filename_Type (File_Entry) not in GPR2.Simple_Name;
            Simple_File_Name : constant String :=
              (if Has_Path
               then Ada.Directories.Base_Name (File_Entry)
               else File_Entry);
            Found            : Boolean := False;
         begin
            --  If the provided filename has a path component, we check if the
            --  file exists.

            if Has_Path and then not Ada.Directories.Exists (File_Entry) then
               Abort_Msg
                 ("could not locate " & File_Entry, With_Help => False);
            end if;

            --  We check each project if it contains the name as a unit, then
            --  if it contains it as a file. If no project contains it, we
            --  fail. If two projects contain it, we fail. Otherwise, we
            --  replace the name with the "main part", which is the body or
            --  the spec, if no body exists.

            for NRP of Tree.Namespace_Root_Projects loop
               if NRP.Kind in GPR2.With_Object_Dir_Kind then
                  declare
                     View_DB   : constant GPR2.Build.View_Db.Object :=
                       Tree.Artifacts_Database (NRP);
                     CU        : GPR2.Build.Compilation_Unit.Object;
                     VS        : GPR2.Build.Source.Object;
                     Elt       : constant GPR2.Name_Type :=
                       Name_Type (Simple_File_Name);
                     Ambiguous : Boolean;
                  begin
                     if View_DB.Source_Option >= Sources_Units
                       and then View_DB.Has_Compilation_Unit (Elt)
                     then
                        CU := View_DB.Compilation_Unit (Elt);
                     elsif View_DB.Source_Option > No_Source then
                        VS :=
                          View_DB.Visible_Source
                            (GPR2.Simple_Name (Elt), Ambiguous);
                        pragma Assert (not Ambiguous);
                        if VS.Is_Defined
                          and then View_DB.Has_Compilation_Unit (VS.Unit.Name)
                        then
                           CU := View_DB.Compilation_Unit (VS.Unit.Name);
                        end if;
                     end if;
                     if CU.Is_Defined then
                        if Found then
                           Abort_Msg
                             ("file or compilation unit "
                              & Simple_File_Name
                              & " is not unique in aggregate project",
                              With_Help => False);
                        else
                           File_List.Replace_Element
                             (Cursor,
                              String (CU.Main_Part.Source.Simple_Name));
                           Found := True;
                           CL_Units.Include (CU.Name, CU);
                        end if;
                     end if;
                  end;
               end if;
            end loop;
            if not Found then
               Abort_Msg
                 (File_Entry
                  & " is not a file or compilation unit"
                  & " of any project",
                  With_Help => False);
            end if;
         end;
      end loop;
   end Sanitize_File_List;

   ---------------------------------
   -- Sanity_Check_SARIF_Base_URI --
   ---------------------------------

   procedure Sanity_Check_SARIF_Base_URI (Tree : Project.Tree.Object) is
      Has_SRCROOT : Boolean := False;
   begin
      for Raw of CL_Switches.SARIF_Base_URIs loop
         declare
            Colon : constant Natural := Index (Raw, ":");
            --  Split on the first colon. Identifiers never contain ':'
            --  so this correctly handles Windows paths like C:\foo\.
         begin
            if Colon = 0 then
               Abort_Msg
                 ("--sarif-base-uri: missing ':' in '" & Raw & "'",
                  With_Help => False);
            end if;
            declare
               Id : constant String := Raw (Raw'First .. Colon - 1);
            begin
               if Id = "" then
                  Abort_Msg
                    ("--sarif-base-uri: empty identifier in '" & Raw & "'",
                     With_Help => False);
               end if;
               if Id = "%SRCROOT%" then
                  Has_SRCROOT := True;
               end if;
            end;
         end;
      end loop;
      if not Has_SRCROOT then
         CL_Switches.SARIF_Base_URIs.Append
           ("%SRCROOT%:" & Tree.Root_Project.Dir_Name.String_Value);
      end if;
   end Sanity_Check_SARIF_Base_URI;

   procedure Set_Project_Attributes is

      function File_Specific_Switch_List return String;
      --  Return the switches accepted in file-specific Proof_Switches
      --  attributes, for user consumption.

      function Description_Name
        (Switch : File_Specific_Switch_Id) return String;
      --  Return the documented spelling of a file-specific switch

      ----------------------
      -- Description_Name --
      ----------------------

      function Description_Name
        (Switch : File_Specific_Switch_Id) return String
      is
         Meta : constant Switch_Metadata := Switch_Definitions (Switch);
      begin
         pragma Assert (Meta.Long /= null or else Meta.Short /= null);
         return
           "'"
           & (if Meta.Long /= null then Meta.Long.all else Meta.Short.all)
           & "'";
      end Description_Name;

      -------------------------------
      -- File_Specific_Switch_List --
      -------------------------------

      function File_Specific_Switch_List return String is
         Buf   : Unbounded_String := Null_Unbounded_String;
         First : Boolean := True;
      begin
         for Switch in File_Specific_Switch_Id loop
            if not First then
               Append (Buf, ", ");
            end if;
            Append (Buf, Description_Name (Switch));
            First := False;
         end loop;
         return To_String (Buf);
      end File_Specific_Switch_List;

   begin
      Project.Registry.Pack.Add (+"Prove", Project.Registry.Pack.Everywhere);
      Project.Registry.Pack.Description.Set_Package_Description
        (+"Prove",
         "This package specifies the options used when calling "
         & "'gnatprove' tool.");
      Project.Registry.Attribute.Add
        (Q_Attribute_Id'(+"Prove", +"Switches"),
         Index_Type           => Project.Registry.Attribute.No_Index,
         Value                => Project.Registry.Attribute.List,
         Value_Case_Sensitive => False,
         Is_Allowed_In        => Project.Registry.Attribute.Everywhere);
      Project.Registry.Attribute.Description.Set_Attribute_Description
        (Q_Attribute_Id'(+"Prove", +"Switches"),
         "This deprecated attribute is the same as Proof_Switches "
         & "(""Ada"").");
      Project.Registry.Attribute.Add
        (Q_Attribute_Id'(+"Prove", +"Proof_Switches"),
         Index_Type           =>
           Project.Registry.Attribute.FileGlob_Or_Language_Index,
         Value                => Project.Registry.Attribute.List,
         Value_Case_Sensitive => False,
         Is_Allowed_In        => Project.Registry.Attribute.Everywhere);
      Project.Registry.Attribute.Description.Set_Attribute_Description
        (Q_Attribute_Id'(+"Prove", +"Proof_Switches"),
         "Defines additional command line switches that are used for the "
         & "invocation of GNATprove. Only the following switches are "
         & "allowed for file-specific switches: "
         & File_Specific_Switch_List);
      Project.Registry.Attribute.Add
        (Q_Attribute_Id'(+"Prove", +"Proof_Dir"),
         Index_Type           => Project.Registry.Attribute.No_Index,
         Value                => Project.Registry.Attribute.Single,
         Value_Case_Sensitive => True,
         Is_Allowed_In        => Project.Registry.Attribute.Everywhere);
      Project.Registry.Attribute.Description.Set_Attribute_Description
        (Q_Attribute_Id'(+"Prove", +"Proof_Dir"),
         "Defines the directory where are stored the files "
         & "concerning the state of the proof of a project. This "
         & "directory contains a sub-directory sessions with one "
         & "directory per source package analyzed for proof. Each of "
         & "these package directories contains a Why3 session file. If a "
         & "manual prover is used to prove some VCs, then a "
         & "sub-directory called by the name of the prover is created "
         & "next to sessions, with the same organization of "
         & "sub-directories. Each of these package directories contains "
         & "manual proof files. Common proof files to be used across "
         & "various proofs can be stored at the toplevel of the "
         & "prover-specific directory.");
   end Set_Project_Attributes;

   -----------------------
   -- SPARK_Report_File --
   -----------------------

   function SPARK_Report_File (Out_Dir : String) return String is
   begin
      return Ada.Directories.Compose (Out_Dir, "gnatprove.out");
   end SPARK_Report_File;

   -------------
   -- Succeed --
   -------------

   procedure Succeed is
   begin
      raise GNATprove_Success with "";
   end Succeed;

   -----------------------
   -- Compute_Why3_Args --
   -----------------------

   function Compute_Why3_Args
     (Obj_Dir : String; FS : File_Specific) return String_Lists.List
   is

      Args          : String_Lists.List;
      Why3_VF       : constant Virtual_File :=
        (if Why3_Conf.all /= ""
         then Create (Filesystem_String (Why3_Conf.all))
         else No_File);
      Gnatwhy3_Conf : constant String :=
        (if Why3_VF /= No_File
         then
           (if Is_Absolute_Path (Why3_VF)
            then Why3_Conf.all
            else
              Ada.Directories.Compose
                (+Get_Current_Dir.Full_Name, Why3_Conf.all))
         else "");

      -------------------------
      --  Local subprograms  --
      -------------------------

      procedure Prepare_Why3_Manual;
      --  Build user libraries (if any) for manual provers

      ---------------------------
      --  Prepare_Why3_Manual  --
      ---------------------------

      procedure Prepare_Why3_Manual is
         Args     : GNAT.OS_Lib.Argument_List :=
           (if Gnatwhy3_Conf /= ""
            then
              [1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all),
               6 => new String'("--why3-conf"),
               7 => new String'(Gnatwhy3_Conf)]
            else
              [1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all)]);
         Res      : Boolean;
         Old_Dir  : constant String := Ada.Directories.Current_Directory;
         Gnatwhy3 : constant String :=
           Ada.Directories.Compose
             (SPARK_Install.Libexec_Spark_Bin, "gnatwhy3");
      begin
         --  Use the Obj_Dir of gnat2why which already is "/.../gnatprove"
         Ada.Directories.Set_Directory (Obj_Dir);
         if Verbosity = Verbose_Level then
            Ada.Text_IO.Put
              ("Changing to object directory: """ & Obj_Dir & """");
            Ada.Text_IO.New_Line;
            Ada.Text_IO.Put (Gnatwhy3 & " ");
            for Arg of Args loop
               Ada.Text_IO.Put (Arg.all & " ");
            end loop;
            Ada.Text_IO.New_Line;
         end if;
         GNAT.OS_Lib.Spawn
           (Program_Name => Gnatwhy3, Args => Args, Success => Res);
         Free (Args);
         Ada.Directories.Set_Directory (Old_Dir);
         if Verbosity = Verbose_Level then
            Ada.Text_IO.Put
              ("Changing back to directory: """ & Old_Dir & """");
            Ada.Text_IO.New_Line;
         end if;
         if not Res then
            Abort_Msg
              ("error: failed to compile shared Coq library",
               With_Help => False);
         end if;
      end Prepare_Why3_Manual;

   begin
      --  The first "argument" is in fact the command name itself, because in
      --  some cases we might want to change it.

      --  ??? If the semaphore is disabled via the --debug-no-semaphore switch,
      --  each gnat2why process may spawn many gnatwhy3 processes all at once.
      --  This may freeze the developer's machine if each of these processes
      --  takes a lot of memory.

      if Use_Semaphores then
         Args.Append ("spark_semaphore_wrapper");
      end if;

      if CL_Switches.Memcached_Server /= null
        and then CL_Switches.Memcached_Server.all /= ""
      then
         Args.Append ("spark_memcached_wrapper");
         --  The first argument of spark_memcached_wrapper is the salt. We
         --  don't use the salt for gnatwhy3, so use any dummy string.
         Args.Append ("salt");
         Args.Append (CL_Switches.Memcached_Server.all);
      end if;

      Args.Append ("gnatwhy3");

      Args.Append ("--timeout");
      Args.Append (Image (FS.Timeout, 1));

      Args.Append ("--steps");
      Args.Append (Image (FS.Steps, 1));

      Args.Append ("--ce-steps");
      Args.Append (Image (FS.CE_Steps, 1));

      Args.Append ("--memlimit");
      Args.Append (Image (FS.Memlimit, 1));

      if not FS.Provers.Is_Empty then
         Args.Append ("--prover");
         Args.Append (Prover_List (FS));
      end if;

      Args.Append ("--proof");
      Args.Append (To_String (FS.Proof));

      if Debug then
         Args.Append ("--debug");
      end if;

      if Debug_Save_VCs then
         Args.Append ("--debug-save-vcs");
      end if;

      if Force then
         Args.Append ("--force");
      end if;

      if not FS.Lazy then
         Args.Append ("--prove-all");
      end if;

      if Replay then
         Args.Append ("--replay");
      end if;

      Args.Append ("-j");
      Args.Append (Image (Parallel, 1));

      if CL_Switches.Limit_Line.all /= "" then
         Args.Append ("--limit-line");
         Args.Append (CL_Switches.Limit_Line.all);
      end if;

      if CL_Switches.Limit_Lines.all /= "" then
         Args.Append ("--limit-lines");
         Args.Append (Ada.Directories.Full_Name (CL_Switches.Limit_Lines.all));
      end if;
      if CL_Switches.Limit_Region.all /= "" then
         Args.Append ("--limit-region");
         Args.Append (CL_Switches.Limit_Region.all);
      end if;

      if Proof_Dir /= null then
         pragma Assert (Proof_Dir.all /= "");
         Create_Path_Or_Exit
           (Ada.Directories.Compose (Proof_Dir.all, "sessions"));
         Args.Append ("--proof-dir");
         --  Why3 is executed in the gnatprove directory and does not know
         --  the project directory so we give it an absolute path to the
         --  proof_dir.
         Args.Append (Proof_Dir.all);
         if Has_Manual_Prover then
            Prepare_Why3_Manual;
         end if;
      end if;

      if Gnatwhy3_Conf /= "" then
         Args.Append ("--why3-conf");
         Args.Append (Gnatwhy3_Conf);
      end if;

      if Why3_Debug.all /= "" then
         Args.Append ("--debug-why3");
         Args.Append (Why3_Debug.all);
      end if;

      Args.Append ("--counterexample");
      Args.Append (if FS.Counterexamples then "on" else "off");

      Args.Append ("--giant-step-rac");
      Args.Append (if FS.Check_Counterexamples then "on" else "off");

      if FS.Check_Counterexamples and then not FS.Provers.Is_Empty then
         Args.Append ("--rac-prover");
         if SPARK_Install.CVC5_Present then
            Args.Append ("cvc5");
         else
            Args.Append ("altergo");
         end if;
      end if;

      if Z3_Counterexample then
         Args.Append ("--ce-prover");
         Args.Append ("z3_ce");
      end if;

      Args.Append ("--warn-prover");
      if SPARK_Install.CVC5_Present then
         Args.Append ("cvc5");
      else
         Args.Append ("altergo");
      end if;

      if FS.Proof_Warn_Timeout /= Invalid_Timeout then
         Args.Append ("--warn-timeout");
         Args.Append (Image (FS.Proof_Warn_Timeout, 1));
      end if;

      if Debug_Prover_Errors then
         Args.Append ("--debug-prover-errors");
      end if;

      if Why3_Logging then
         Args.Append ("--logging");
      end if;

      Args.Append ("--ce-timeout");
      Args.Append (Image (FS.CE_Timeout, 1));

      return Args;
   end Compute_Why3_Args;

end Configuration;
