------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
with Ada.Containers;            use Ada.Containers;
with Ada.Environment_Variables;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Ada.Text_IO;               use Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Gnat2Why_Opts.Writing;
with GNAT.Command_Line;         use GNAT.Command_Line;
with GNAT.Directory_Operations;
with GNAT.OS_Lib;
with GNAT.Strings;              use GNAT.Strings;
with Platform;                  use Platform;
with SPARK2014VSN;              use SPARK2014VSN;
with System.Multiprocessors;
with VC_Kinds;

package body Configuration is

   Invalid_Level : constant := -1;

   Invalid_Steps : constant := -1;

   Usage_Message : constant String := "-Pproj [switches] [-cargs switches]";
   --  Used to print part of the help message for gnatprove

   Clean : aliased Boolean;
   --  Set to True when --clean was given. Triggers cleanup of GNATprove
   --  intermediate files.

   Proj_Env : Project_Environment_Access;
   --  This is the project environment used to load the project. It may be
   --  modified before loading it, e.g. -X switches

   procedure Abort_Msg (Msg       : String;
                        With_Help : Boolean)
     with No_Return;
   --  Stop the program, output the message and the help message when
   --  requested, then exit.

   procedure Clean_Up (Tree : Project_Tree);
   --  Deletes generated "gnatprove" sub-directories in all object directories
   --  of the project.

   function Compute_Socket_Dir (Root_Project : Project_Type) return String;
   --  Returns the directory where the socket file will be created. On
   --  Windows, this is irrelevant, so the function returns the empty string.
   --  On Unix, the following rules are applied:
   --  - if TMPDIR is set, exists and is writable, use that
   --  - if /tmp exists and is writable, use that
   --  - otherwise return the object directory.

   procedure Handle_Project_Loading_Switches
     (Switch    : String;
      Parameter : String;
      Section   : String);
   --  Command line handler which deals with -X switches and -aP switches

   procedure Handle_Switch
     (Switch    : String;
      Parameter : String;
      Section   : String);
   --  Deal with all switches that are not automatic. In gnatprove, all
   --  recognized switches are automatic, so this procedure should only be
   --  called for unknown switches and for switches in section -cargs.

   procedure Prepare_Prover_Lib (Obj_Dir : String);
   --  Deal with the why3 libraries manual provers might need.
   --  Copies needed sources into gnatprove and builds the library.
   --  For the moment, only Coq is handled.

   procedure Sanitize_File_List (Tree : Project_Tree);
   --  Apply the following rules to each file in [File_List]:
   --    if the file is a body, do nothing;
   --    if the file is a spec, and a body exists, replace by filename of body
   --    if the file is a separate, replace with filename of body
   --  This is required to avoid calling gnat2why on a separate body (will
   --  crash) or on a spec when there is a body (gnat2why will incorrectly
   --  assume that there is no body).

   procedure Print_Errors (S : String);
   --  The String in argument is an error message from gnatcoll. Print it on
   --  stderr with a prefix.

   procedure Produce_Version_Output;
   --  Print the version of gnatprove, why3 and shipped provers

   procedure Produce_List_Categories_Output;
   --  List information for all messages issued by the tool

   procedure Set_CodePeer_Mode (Input : String);
   --  Parse the --codepeer option (possibilities are "on" and "off")

   function Check_gnateT_Switch (Tree : Project_Tree) return String;
   --  Try to compute the gnateT switch to be used for gnat2why. If there is
   --  a target and runtime set, but we can't compute the switch, a warning
   --  is issued.

   procedure Check_File_Part_Of_Project (Tree : Project_Tree;
                                         Fn   : String);
   --  raise an error if the file FN is not part of the project
   --  @param Tree the project tree
   --  @param FN a file name

   function Is_Coq_Prover return Boolean;
   --  @return True iff one alternate prover is "coq"

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
     (Project_Parsing,
      --  only parses switches that are related to loading of the project file
      --  (-P, -X, etc). and some switches that exit immediately (--version,
      --  --clean), ignores other switches.

      All_Switches,
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

   procedure Parse_Switches (Mode : Parsing_Modes; Com_Lin : String_List);
   --  parse the command line switches according to the provided mode; set
   --  global variables associated to the switches.

   procedure Display_Help;

   package body Prj_Attr is

      package body Prove is

         --------------------
         -- Proof_Switches --
         --------------------

         function Proof_Switches (Proj : Project_Type; Index : String)
                                  return GNAT.Strings.String_List_Access
         is
            Attr_Proof_Switches : constant Attribute_Pkg_List :=
              Build ("Prove", "Proof_Switches");
         begin
            if Index in "Ada" | "ada" then
               return Prj_Attr.Prove.Proof_Switches_Ada;
            end if;
            return Attribute_Value (Proj, Attr_Proof_Switches, Index);
         end Proof_Switches;
      end Prove;

   end Prj_Attr;

   ---------------
   -- Abort_Msg --
   ---------------

   procedure Abort_Msg (Msg       : String;
                        With_Help : Boolean) is
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
      GNAT.OS_Lib.OS_Exit (1);
   end Abort_Msg;

   --------------------------------
   -- Check_File_Part_Of_Project --
   --------------------------------

   procedure Check_File_Part_Of_Project (Tree : Project_Tree;
                                         Fn   : String)
   is
      File_VF : constant Virtual_File :=
        Tree.Create (Filesystem_String (Fn));
      Info    : constant File_Info := Tree.Info (File_VF);
   begin
      if Project (Info) = No_Project then
         Abort_Msg
           ("file " & Fn & " of attribute Proof_Switches " &
              "is not part of the project",
            With_Help => False);
      end if;
   end Check_File_Part_Of_Project;

   -------------------------
   -- Check_gnateT_Switch --
   -------------------------

   function Check_gnateT_Switch (Tree : Project_Tree) return String is
   begin
      if not Tree.Root_Project.Target_Same_As_Host
        and then
          (Prj_Attr.Target.all /= "" or else CL_Switches.Target.all /= "")
      then

         --  User has already set the attribute, don't try anything smart

         if Prj_Attr.Builder.Global_Compilation_Switches_Ada /= null
           and then
             (for some Switch of
                Prj_Attr.Builder.Global_Compilation_Switches_Ada.all =>
                  GNATCOLL.Utils.Starts_With (Switch.all, "-gnateT="))
         then
            return "";
         end if;

         declare
            Att    : constant Attribute_Pkg_String :=
              Build ("", "runtime_dir");
            RT_Dir : constant String :=
              Tree.Root_Project.Attribute_Value (Att, "ada");
         begin
            if RT_Dir /= "" then
               declare
                  Targ_Prop_File : constant String :=
                    Compose (RT_Dir, "ada_target_properties");
               begin
                  if Exists (Targ_Prop_File) then
                     return "-gnateT=" & Targ_Prop_File;
                  end if;
               end;
            end if;
         end;

         --  If we reached here, there *should* be a target properties
         --  file, but we can't find it and the user didn't add one. Print
         --  a warning.

         Put_Line
           (Standard_Error,
            "warning: attribute ""Target"" of your project file is " &
              "only used to determine runtime library");
         Put_Line
           (Standard_Error,
            "warning: to specify target properties, specify option " &
              """-gnateT"" using ""Builder.Global_Compilation_Switches""");
      end if;
      return "";
   end Check_gnateT_Switch;

   --------------
   -- Clean_Up --
   --------------

   procedure Clean_Up (Tree : Project_Tree) is

      procedure Clean_Up_One_Directory (Dir : Virtual_File);
      --  Remove a generated "gnatprove" sub-directory

      function Is_Externally_Built (Project : Project_Type) return Boolean;
      --  Returns True if the project is externally built

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
               if Verbose then
                  Ada.Text_IO.Put
                    ("Deleting directory " & Rm_Dir & "...");
               end if;
               GNAT.Directory_Operations.Remove_Dir
                 (Rm_Dir, Recursive => True);
               if Verbose then
                  Ada.Text_IO.Put_Line (" done");
               end if;
            end if;
         end if;
      exception
         when GNAT.Directory_Operations.Directory_Error =>
            if Verbose then
               Ada.Text_IO.Put_Line (" failed, please delete manually");
            end if;
      end Clean_Up_One_Directory;

      -------------------------
      -- Is_Externally_Built --
      -------------------------

      function Is_Externally_Built (Project : Project_Type) return Boolean is
         Val : constant String :=
           Ada.Characters.Handling.To_Lower
             (Project.Attribute_Value (Build ("", "Externally_Built")));
      begin
         return Val = "true";
      end Is_Externally_Built;

      --  Local variables

      Proj_Type : constant Project_Type := Root_Project (Tree);
      Iter      : Project_Iterator := Proj_Type.Start;
      Project   : Project_Type;

   --  Start of processing for Clean_Up

   begin
      loop
         Project := Current (Iter);
         exit when Project = No_Project;

         --  Externally built projects should never be cleaned up

         if not Is_Externally_Built (Project) then
            Clean_Up_One_Directory (Project.Artifacts_Dir);
            Clean_Up_One_Directory (Project.Library_Directory);
            Clean_Up_One_Directory (Project.Library_Ali_Directory);
         end if;

         Next (Iter);
      end loop;
   end Clean_Up;

   ------------------------
   -- Compute_Socket_Dir --
   ------------------------

   function Compute_Socket_Dir (Root_Project : Project_Type) return String is

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
         return Exists (Dir)
           and then GNAT.OS_Lib.Is_Write_Accessible_File (Dir);
      end Exists_And_Is_Writable;

   --  Start of processing for Compute_Socket_Dir

   begin
      if Get_OS_Flavor in X86_Windows | X86_64_Windows then
         return "";
      end if;
      if Ada.Environment_Variables.Exists (TMPDIR_Envvar)
        and then Exists_And_Is_Writable
          (Ada.Environment_Variables.Value (TMPDIR_Envvar))
      then
         return Ada.Environment_Variables.Value (TMPDIR_Envvar);
      elsif Exists_And_Is_Writable (TMP_Dir) then
         return TMP_Dir;
      else
         return Root_Project.Artifacts_Dir.Display_Full_Name;
      end if;
   end Compute_Socket_Dir;

   ------------------
   -- Display_Help --
   ------------------

   procedure Display_Help is
   begin
      Ada.Text_IO.Put_Line ("Usage: gnatprove " & Usage_Message);
      Ada.Text_IO.Put_Line (SPARK_Install.Help_Message);
   end Display_Help;

   -------------------------------------
   -- Handle_Project_Loading_Switches --
   -------------------------------------

   procedure Handle_Project_Loading_Switches
     (Switch    : String;
      Parameter : String;
      Section   : String)
   is
      pragma Unreferenced (Section);
      Equal : Natural := 0;
   begin
      if Switch'Length > 2
        and then Switch (Switch'First + 1) = 'X'
      then

         --  When a -X switch was found, we need to:
         --  * add the scenario variable to the environment that we use to load
         --    the project;
         --  * store the switch to add it to calls to gprbuild that we do later

         --  First we add the variable to the environment. For that, we search
         --  for the "=" sign which separates the variable from the value ..

         Equal := Ada.Strings.Fixed.Index (Switch, "=");

         --  ... and then set the variable in the environment.

         Proj_Env.Change_Environment
           (Switch (Switch'First + 2 .. Equal - 1),
            Switch (Equal + 1 .. Switch'Last));

         --  Second, we add the whole switch to the list of Scenario switches

         CL_Switches.X.Append (Switch);
      elsif Switch = "-aP" then
         CL_Switches.GPR_Project_Path.Append (Parameter);
      end if;
   end Handle_Project_Loading_Switches;

   -------------------
   -- Handle_Switch --
   -------------------

   procedure Handle_Switch
     (Switch    : String;
      Parameter : String;
      Section   : String)
   is
      pragma Unreferenced (Parameter);
   begin
      if Section = "cargs" then
         CL_Switches.Cargs_List.Append (Switch);

      elsif Switch (Switch'First) /= '-' then

         --  We assume that the "switch" is actually an argument and put it in
         --  the file list

         CL_Switches.File_List.Append (Switch);

      --  We explicitly ignore project-loading switches here. They have been
      --  taken into account in the parsing of the command line.

      elsif Switch'Length >= 2
        and then Switch (Switch'First + 1) = 'X'
      then
         null;
      elsif Switch = "-aP" then
         null;
      else
         raise Invalid_Switch;
      end if;
   end Handle_Switch;

   ----------------------
   -- Is_Manual_Prover --
   ----------------------

   function Is_Manual_Prover return Boolean is
      Provers : String_Lists.List renames
        File_Specific_Map ("Ada").Provers;
   begin
      return Provers.Length = 1
        and then
          (Case_Insensitive_Contains (Provers, "coq")
           or else Case_Insensitive_Contains (Provers, "isabelle"));
   end Is_Manual_Prover;

   -------------------
   -- Is_Coq_Prover --
   -------------------

   function Is_Coq_Prover return Boolean is
      Provers : String_Lists.List renames
        File_Specific_Map ("Ada").Provers;
   begin
      return Case_Insensitive_Contains (Provers, "coq");
   end Is_Coq_Prover;

   --------------------
   -- Parse_Switches --
   --------------------

   procedure Parse_Switches (Mode : Parsing_Modes; Com_Lin : String_List) is

      procedure Free_Topmost is new Ada.Unchecked_Deallocation
        (Object => String_List, Name => String_List_Access);

      Config         : Command_Line_Configuration;
      Parser         : Opt_Parser;
      Com_Lin_Access : String_List_Access :=
        new String_List'(Com_Lin);

      use CL_Switches;

   begin
      Initialize_Option_Scan (Parser, Com_Lin_Access);
      Set_Usage (Config,
                 Usage    => Usage_Message,
                 Help_Msg => SPARK_Install.Help_Message);

      --  If no arguments have been given, print help message and exit.
      --  Empty switches list is allowed for modes File_Specific_Only and
      --  Global_Switches_Only.

      if Mode in Project_Parsing | All_Switches
        and then Com_Lin'Length = 0
      then
         Abort_Msg ("", With_Help => True);
      end if;

      if Mode in Project_Parsing | All_Switches then
         Define_Switch (Config, "-aP=");
         Define_Switch
           (Config,
            Clean'Access,
            Long_Switch => "--clean");
         Define_Switch
           (Config,
            List_Categories'Access,
            Long_Switch => "--list-categories");
         Define_Switch
           (Config,
            CL_Switches.P'Access,
            "-P:");
         Define_Switch
           (Config,
            CL_Switches.Target'Access,
            Long_Switch => "--target=");
         Define_Switch
           (Config,
            CL_Switches.RTS'Access,
            Long_Switch => "--RTS=");
         Define_Switch
           (Config,
            CL_Switches.Subdirs'Access,
            Long_Switch => "--subdirs=");
         Define_Switch
           (Config,
            Version'Access,
         Long_Switch => "--version");
      end if;

      if Mode in Project_Parsing | All_Switches | Global_Switches_Only then
         Define_Switch
           (Config,
            CL_Switches.V'Access,
            "-v", Long_Switch => "--verbose");
      end if;

      if Mode in All_Switches | Global_Switches_Only then
         Define_Switch
           (Config,
            CL_Switches.Assumptions'Access,
            Long_Switch => "--assumptions");

         --  This switch is not documented on purpose. We provide the fake_*
         --  binaries instead of the real prover binaries. This helps when
         --  collecting benchmarks for prover developers.
         Define_Switch
           (Config, CL_Switches.Benchmark'Access,
            Long_Switch => "--benchmark");
         Define_Switch
           (Config,
            CL_Switches.Checks_As_Errors'Access,
            Long_Switch => "--checks-as-errors");
         Define_Switch
           (Config,
            CL_Switches.CodePeer'Access,
            Long_Switch => "--codepeer=");
         Define_Switch
           (Config,
            CL_Switches.CWE'Access,
            Long_Switch => "--cwe");
         Define_Switch
           (Config,
            CL_Switches.D'Access,
            "-d", Long_Switch => "--debug");
         Define_Switch
           (Config,
            CL_Switches.Dbg_Proof_Only'Access,
            Long_Switch => "--dbg-proof-only");
         Define_Switch
           (Config,
            CL_Switches.Debug_Save_VCs'Access,
            Long_Switch => "--debug-save-vcs");
         Define_Switch
           (Config,
            CL_Switches.Dbg_No_Sem'Access,
            Long_Switch => "--debug-no-semaphore");
         Define_Switch
           (Config,
            CL_Switches.Debug_Trivial'Access,
            Long_Switch => "--debug-trivial");
         Define_Switch
           (Config,
            CL_Switches.Flow_Debug'Access,
            Long_Switch => "--flow-debug");
         Define_Switch
           (Config,
            CL_Switches.Flow_Termination'Access,
            Long_Switch => "--flow-termination");
         Define_Switch
           (Config,
            CL_Switches.Flow_Show_GG'Access,
            Long_Switch => "--flow-show-gg");
         Define_Switch
           (Config,
            CL_Switches.F'Access,
            "-f");
         Define_Switch
           (Config,
            CL_Switches.IDE_Progress_Bar'Access,
            Long_Switch => "--ide-progress-bar");
         Define_Switch
           (Config,
            CL_Switches.Info'Access,
            Long_Switch => "--info");
         Define_Switch
           (Config, CL_Switches.J'Access,
            Long_Switch => "-j:",
            Initial => 1);
         Define_Switch
           (Config,
            CL_Switches.K'Access,
            "-k");
         Define_Switch
           (Config,
            CL_Switches.Limit_Line'Access,
            Long_Switch => "--limit-line=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Region'Access,
            Long_Switch => "--limit-region=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Subp'Access,
            Long_Switch => "--limit-subp=");
         Define_Switch
           (Config, CL_Switches.Memcached_Server'Access,
            Long_Switch => "--memcached-server=");
         Define_Switch
           (Config,
            CL_Switches.Mode'Access,
            Long_Switch => "--mode=");
         Define_Switch
           (Config,
            CL_Switches.M'Access,
            "-m");
         Define_Switch
           (Config,
            CL_Switches.No_Axiom_Guard'Access,
            Long_Switch => "--no-axiom-guard");
         Define_Switch
           (Config,
            CL_Switches.No_Global_Generation'Access,
            Long_Switch => "--no-global-generation");
         Define_Switch
           (Config,
            CL_Switches.No_Subprojects'Access,
            Long_Switch => "--no-subprojects");
         Define_Switch
           (Config,
            CL_Switches.Output'Access,
            Long_Switch => "--output=");
         Define_Switch
           (Config,
            CL_Switches.Output_Header'Access,
            Long_Switch => "--output-header");
         Define_Switch
           (Config,
            CL_Switches.Output_Msg_Only'Access,
            Long_Switch => "--output-msg-only");
         Define_Switch
           (Config,
            CL_Switches.Pedantic'Access,
            Long_Switch => "--pedantic");
         Define_Switch
           (Config,
            CL_Switches.Proof_Warnings'Access,
            Long_Switch => "--proof-warnings");
         Define_Switch
           (Config,
            CL_Switches.Q'Access,
            "-q", Long_Switch => "--quiet");
         Define_Switch
           (Config,
            CL_Switches.Replay'Access,
            Long_Switch => "--replay");
         Define_Switch
           (Config,
            CL_Switches.Report'Access,
            Long_Switch => "--report=");
         Define_Switch
           (Config,
            CL_Switches.Subdirs'Access,
            Long_Switch => "--subdirs=");
         Define_Switch
           (Config,
            CL_Switches.U'Access,
            "-u");
         Define_Switch
           (Config,
            CL_Switches.UU'Access,
            "-U");
         Define_Switch
           (Config,
            CL_Switches.Warnings'Access,
            Long_Switch => "--warnings=");
         Define_Switch
           (Config, CL_Switches.Why3_Conf'Access,
            Long_Switch => "--why3-conf=");
         Define_Switch
           (Config, CL_Switches.Why3_Debug'Access,
            Long_Switch => "--why3-debug=");
         Define_Switch
           (Config,
            CL_Switches.Z3_Counterexample'Access,
            Long_Switch => "--z3-counterexample");
         Define_Section (Config, "cargs");
         Define_Switch (Config, "*", Section => "cargs");
      end if;

      if Mode in All_Switches | Global_Switches_Only | File_Specific_Only then
         Define_Switch
           (Config, CL_Switches.Level'Access,
            Long_Switch => "--level=",
            Initial => Invalid_Level);
         Define_Switch
           (Config,
            CL_Switches.Memlimit'Access,
            Long_Switch => "--memlimit=");
         Define_Switch
           (Config,
            CL_Switches.No_Counterexample'Access,
            Long_Switch => "--no-counterexample");
         Define_Switch
           (Config,
            CL_Switches.No_Inlining'Access,
            Long_Switch => "--no-inlining");
         Define_Switch
           (Config,
            CL_Switches.No_Loop_Unrolling'Access,
            Long_Switch => "--no-loop-unrolling");
         Define_Switch
           (Config,
            CL_Switches.Proof'Access,
            Long_Switch => "--proof=");
         Define_Switch
           (Config,
            CL_Switches.Prover'Access,
            Long_Switch => "--prover=");

         --  If not specified on the command-line, value of steps is invalid
         Define_Switch
           (Config, CL_Switches.Steps'Access,
            Long_Switch => "--steps=",
            Initial => Invalid_Steps);
         Define_Switch
           (Config,
            CL_Switches.Timeout'Access,
            Long_Switch => "--timeout=");
      end if;

      if Mode in All_Switches | Project_Parsing then
         Define_Switch (Config, "*", Help => "list of source files");
      end if;

      declare
         Callback : constant Switch_Handler :=
           (if Mode = Project_Parsing then
               Handle_Project_Loading_Switches'Access
            else Handle_Switch'Access);
      begin
         Getopt (Config,
                 Callback    => Callback,
                 Parser      => Parser,
                 Concatenate => False);

      exception
         when Invalid_Switch =>
            GNAT.OS_Lib.OS_Exit (1);
         when Exit_From_Command_Line =>
            GNAT.OS_Lib.OS_Exit (0);
         when Invalid_Parameter =>
            Abort_Msg ("No parameter given to switch -" & Full_Switch (Parser),
                       With_Help => False);
      end;

      Free (Config);
      Free_Topmost (Com_Lin_Access);
   end Parse_Switches;

   ------------------------
   -- Prepare_Prover_Lib --
   ------------------------

   procedure Prepare_Prover_Lib (Obj_Dir : String) is

      Provers        : String_Lists.List renames
        File_Specific_Map ("Ada").Provers;
      Prover_Name    : constant String :=
        Ada.Characters.Handling.To_Lower (Provers.First_Element);
      Prover_Lib_Dir : constant String :=
        Compose
          (Compose (SPARK_Install.Libexec_Share_Why3, "libs"),
           Name => Prover_Name);
      Prover_Obj_Dir : constant String := Compose
        (Compose (Obj_Dir, "why3_libs"),
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
           (if Dir /= "" then Compose (Prover_Obj_Dir, Dir)
            else Prover_Obj_Dir);
         Lib_Dir    : constant String :=
           (if Dir /= "" then Compose (Prover_Lib_Dir, Dir)
            else Prover_Lib_Dir);
      begin
         if not Exists (Compose (Target_Dir, Name => File & ".vo")) then
            declare
               Source_Dest : constant String :=
                 Compose (Target_Dir, Name => File & ".v");
            begin
               --  Copy file
               Create_Path (Prover_Obj_Dir);
               if not Exists (Target_Dir) then
                  Create_Directory (Target_Dir);
               end if;
               Copy_File (Compose (Lib_Dir, Name => File & ".v"),
                          Source_Dest);
               --  Build it
               declare
                  Coqc_Bin : String_Access :=
                    GNAT.OS_Lib.Locate_Exec_On_Path ("coqc");
                  Args : GNAT.OS_Lib.Argument_List :=
                    (1 => new String'("-R"),
                     2 => new String'(Prover_Obj_Dir),
                     3 => new String'("Why3"),
                     4 => new String'(Source_Dest));

                  Success : Boolean;

               begin
                  if Coqc_Bin = null then
                     Abort_Msg (Msg       => "coq prover not present in PATH",
                                With_Help => False);
                  end if;
                  GNAT.OS_Lib.Spawn (Program_Name => Coqc_Bin.all,
                                     Args         => Args,
                                     Success      => Success);
                  if not Success then
                     Abort_Msg (Msg       =>
                                  "error during compilations of " &
                                  Source_Dest,
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
         when No_WP       => return "no_wp";
         when All_Split   => return "all_split";
         when Progressive => return "progressive";
         when Per_Path    => return "per_path";
         when Per_Check   => return "per_check";
      end case;
   end To_String;

   ------------------
   -- Print_Errors --
   ------------------

   procedure Print_Errors (S : String) is
   begin
      Ada.Text_IO.Put_Line (Standard_Error, "gnatprove: " & S);
   end Print_Errors;

   ------------------------------------
   -- Produce_List_Categories_Output --
   ------------------------------------

   procedure Produce_List_Categories_Output is
      use VC_Kinds;
   begin
      Ada.Text_IO.Put_Line ("[Flow analysis check categories]");
      for K in Valid_Flow_Tag_Kind loop
         Ada.Text_IO.Put_Line (Rule_Name (K) & " - " & Kind_Name (K) & " - " &
                                 Description (K));
      end loop;

      Ada.Text_IO.Put_Line ("[Proof check categories]");
      for K in VC_Kind loop
         if K not in VC_Warning_Kind then
            Ada.Text_IO.Put_Line (Rule_Name (K) & " - " & Kind_Name (K) &
                                    " - " & Description (K));
         end if;
      end loop;

      Ada.Text_IO.Put_Line ("[Proof warnings categories]");
      for K in VC_Kind loop
         if K in VC_Warning_Kind then
            Ada.Text_IO.Put_Line (Rule_Name (K) & " - " & Kind_Name (K) &
                                    " - " & Description (K));
         end if;
      end loop;

      --  ??? TODO GNAT front-end categories
   end Produce_List_Categories_Output;

   ----------------------------
   -- Produce_Version_Output --
   ----------------------------

   procedure Produce_Version_Output is
      Gnatwhy3 : constant String :=
        Compose (SPARK_Install.Libexec_Spark_Bin, "gnatwhy3");
      Alt_Ergo : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("alt-ergo");
      CVC4 : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("cvc4");
      Z3 : String_Access :=
        GNAT.OS_Lib.Locate_Exec_On_Path ("z3");
      Status : aliased Integer;
      Dash_Dash_Version : String_Lists.List;
      Dash_Version : String_Lists.List;
   begin
      Dash_Dash_Version.Append ("--version");
      Dash_Version.Append ("-version");
      Ada.Text_IO.Put_Line (SPARK2014_Version_String);
      Call_With_Status (Gnatwhy3,
                        Arguments => Dash_Dash_Version,
                        Status    => Status);

      if Alt_Ergo /= null then
         Ada.Text_IO.Put (Alt_Ergo.all & ": ");
         Call_With_Status (Alt_Ergo.all,
                           Arguments => Dash_Version,
                           Status    => Status);
         Free (Alt_Ergo);
      end if;
      if CVC4 /= null then
         Ada.Text_IO.Put (CVC4.all & ": ");
         Call_With_Status (CVC4.all,
                           Arguments => Dash_Dash_Version,
                           Status    => Status);
         Free (CVC4);
      end if;
      if Z3 /= null then
         Ada.Text_IO.Put (Z3.all & ": ");
         Call_With_Status (Z3.all,
                           Arguments => Dash_Dash_Version,
                           Status    => Status);
         Free (Z3);
      end if;
   end Produce_Version_Output;

   -----------------
   -- Prover_List --
   -----------------

   function Prover_List (FS : File_Specific) return String is
      use Ada.Strings.Unbounded;
      use String_Lists;

      Buf : Unbounded_String := Null_Unbounded_String;
      C : Cursor := First (FS.Provers);
   begin
      loop
         Append (Buf, FS.Provers (C));
         Next (C);
         exit when not Has_Element (C);
         Append (Buf, ',');
      end loop;
      return To_String (Buf);
   end Prover_List;

   function Prover_List (Source_File : String) return String is
   begin
      return Prover_List (File_Specific_Map (Source_File));
   end Prover_List;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project_Tree) is

      function Init return Project_Tree;
      --  Load the project file; This function requires the project file to be
      --  present.

      procedure Postprocess;
      --  Read the switch variables set by command-line parsing and set the
      --  gnatprove variables.

      procedure File_Specific_Postprocess (FS : out File_Specific);
      --  Same as Postprocess, but for the switches that can be file-specific.
      --  For example, --level, --timeout are handled here.

      procedure Set_Project_Vars (Proj : Project_Type);
      --  Set the variables of the Prj_Attr package

      procedure Set_Mode;
      procedure Set_Output_Mode;
      procedure Set_Warning_Mode;
      procedure Set_Report_Mode;

      procedure Set_Level_Timeout_Steps_Provers (FS : out File_Specific);
      --  Using the --level, --timeout, --steps and --provers switches, set the
      --  corresponding variables.

      procedure Set_Proof_Mode (FS : in out File_Specific);
      procedure Process_Limit_Switches;
      procedure Set_Provers
        (Prover : GNAT.Strings.String_Access;
         FS     : in out File_Specific);
      procedure Set_Proof_Dir;
      --  If attribute Proof_Dir is set in the project file,
      --  set global variable Proof_Dir to the full path
      --  <path-to-project-file>/<value-of-proof-dir>.

      procedure Limit_Provers (Provers : in out String_Lists.List);
      --  This subprogram is here for SPARK Discovery. It removes cvc4/z3 from
      --  the provers list, if not found on the PATH. If that makes the list of
      --  provers become empty, alt-ergo is added as prover, so that we have at
      --  least one prover.

      procedure Sanity_Checking;
      --  Check the command line flags for conflicting flags

      -------------------------------
      -- File_Specific_Postprocess --
      -------------------------------

      procedure File_Specific_Postprocess (FS : out File_Specific) is
      begin
         Set_Level_Timeout_Steps_Provers (FS);
         Set_Proof_Mode (FS);
         FS.No_Inlining := CL_Switches.No_Inlining;
         FS.Info := CL_Switches.Info;
         FS.No_Loop_Unrolling := CL_Switches.No_Loop_Unrolling;
         FS.Proof_Warnings := CL_Switches.Proof_Warnings;
         FS.No_Inlining := CL_Switches.No_Inlining or
                           CL_Switches.No_Global_Generation;
      end File_Specific_Postprocess;

      ----------
      -- Init --
      ----------

      function Init return Project_Tree is
         GNAT_Version : GNAT.Strings.String_Access;
         Tree         : Project_Tree;

      begin
         if not Null_Or_Empty_String (CL_Switches.Subdirs) then
            Phase2_Subdir := Filesystem_String (CL_Switches.Subdirs.all) /
              Phase2_Subdir;

         end if;

         Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
         Free (GNAT_Version);
         Set_Object_Subdir (Proj_Env.all,
                            Filesystem_String
                              (Phase2_Subdir.Display_Full_Name));
         Proj_Env.Register_Default_Language_Extension ("C", ".h", ".c");
         declare
            Sswitches : constant String :=
              Register_New_Attribute ("Switches", "Prove",
                                      Is_List => True);
         begin
            if Sswitches /= "" then
               Abort_Msg (Sswitches, With_Help => False);
            end if;
         end;

         declare
            Sswitches : constant String :=
              Register_New_Attribute ("Proof_Switches", "Prove",
                                      Is_List => True,
                                      Indexed => True);
         begin
            if Sswitches /= "" then
               Abort_Msg (Sswitches, With_Help => False);
            end if;
         end;

         declare
            Sproof_dir : constant String :=
              Register_New_Attribute ("Proof_Dir", "Prove");
         begin
            if Sproof_dir /= "" then
               Abort_Msg (Sproof_dir, With_Help => False);
            end if;
         end;

         declare
            Targ : constant String :=
              (if CL_Switches.Target /= null then CL_Switches.Target.all
               else "");
            RTS : constant String :=
              (if CL_Switches.RTS /= null then CL_Switches.RTS.all else "");
         begin
            Set_Target_And_Runtime
              (Proj_Env.all, Targ, RTS);
         end;
         Set_Automatic_Config_File (Proj_Env.all);
         declare
            Arr  : constant File_Array := Proj_Env.Predefined_Project_Path;
            Arr2 : File_Array
              (1 .. Integer (CL_Switches.GPR_Project_Path.Length));
            I    : Integer := 1;
         begin
            for S of CL_Switches.GPR_Project_Path loop
               Arr2 (I) := Create (Filesystem_String (S));
               I := I + 1;
            end loop;
            Proj_Env.Set_Predefined_Project_Path (Arr & Arr2);
         end;

         if CL_Switches.P.all /= "" then
            Tree.Load
              (GNATCOLL.VFS.Create (Filesystem_String (CL_Switches.P.all)),
               Proj_Env,
               Errors => Print_Errors'Access);
         else
            Abort_Msg ("No project file is given", With_Help => False);
         end if;
         return Tree;
      end Init;

      -------------------
      -- Limit_Provers --
      -------------------

      procedure Limit_Provers (Provers : in out String_Lists.List) is

         procedure Remove_Prover (Name : String);
         --  Remove prover from Provers list
         --  @param Name prover name to be removed

         -------------------
         -- Remove_Prover --
         -------------------

         procedure Remove_Prover (Name : String) is
            C : String_Lists.Cursor := Case_Insensitive_Find (Provers, Name);
         begin
            if String_Lists.Has_Element (C) then
               Provers.Delete (C);
            end if;
         end Remove_Prover;

         Is_Empty_At_Start : constant Boolean := Provers.Is_Empty;

      --  Start of processing for Limit_Prover

      begin
         if not SPARK_Install.CVC4_Present then
            Remove_Prover ("cvc4");
         end if;
         if not SPARK_Install.Z3_Present then
            Remove_Prover ("z3");
         end if;

         if not Is_Empty_At_Start and then Provers.Is_Empty then
            Provers.Append ("altergo");
         end if;

      end Limit_Provers;

      -----------------
      -- Postprocess --
      -----------------

      procedure Postprocess is
         function On_Path (Exec : String) return Boolean;
         --  Return True iff Exec is present on PATH

         -------------
         -- On_Path --
         -------------

         function On_Path (Exec : String) return Boolean is
            Location : String_Access :=
              GNAT.OS_Lib.Locate_Exec_On_Path (Exec);

            Present : constant Boolean := Location /= null;

         begin
            Free (Location);
            return Present;
         end On_Path;

      --  Start of processing for Postprocess

      begin
         Sanity_Checking;

         SPARK_Install.Z3_Present   := On_Path ("z3");
         SPARK_Install.CVC4_Present := On_Path ("cvc4");

         Debug := CL_Switches.D or CL_Switches.Flow_Debug;

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

         if CL_Switches.J = 0 then
            Parallel := Natural (System.Multiprocessors.Number_Of_CPUs);
         elsif CL_Switches.J < 0 then
            Abort_Msg ("error: wrong argument for -j",
                       With_Help => False);
         else
            Parallel := CL_Switches.J;
         end if;

         --  Handling of Only_Given and Filelist

         Only_Given := CL_Switches.U
           or not Null_Or_Empty_String (CL_Switches.Limit_Subp)
           or not Null_Or_Empty_String (CL_Switches.Limit_Line);

         Process_Limit_Switches;

         Set_CodePeer_Mode (CL_Switches.CodePeer.all);
         GnateT_Switch := new String'(Check_gnateT_Switch (Tree));
         Set_Mode;
         Set_Output_Mode;
         Set_Warning_Mode;
         Set_Report_Mode;
         Set_Proof_Dir;

         CodePeer := CodePeer and then Mode in GPM_Prove | GPM_All;
         Use_Semaphores := (not Debug) and then (not CL_Switches.Dbg_No_Sem);
      end Postprocess;

      ----------------------------
      -- Process_Limit_Switches --
      ----------------------------

      procedure Process_Limit_Switches is
      begin
         --  Unless -U is specified, use of --limit-[line,region,subp] leads
         --  to only the file with the given line or subprogram to be analyzed.
         --  Specifying -U with --limit-[line,region,subp] is useful to
         --  force analysis of all files, when the line or subprogram is
         --  inside a generic or itself a generic, so that all instances of
         --  the line/subprogram are analyzed.

         if not All_Projects then
            declare
               Limit_String : GNAT.Strings.String_Access := null;

            begin
               --  Limit_Line, Limit_Region, and Limit_Subp all imply -u for
               --  the corresponding file. We take care of that using the
               --  Limit_String variable, note that "Limit_Line" is
               --  stronger naturally.

               if not Null_Or_Empty_String (CL_Switches.Limit_Subp) then
                  Limit_String := CL_Switches.Limit_Subp;
               end if;

               if not Null_Or_Empty_String (CL_Switches.Limit_Region) then
                  Limit_String := CL_Switches.Limit_Region;
               end if;

               if not Null_Or_Empty_String (CL_Switches.Limit_Line) then
                  Limit_String := CL_Switches.Limit_Line;
               end if;

               if Limit_String /= null then
                  declare
                     Colon_Index : constant Natural :=
                       Ada.Strings.Fixed.Index (Source  => Limit_String.all,
                                                Pattern => ":");

                  begin
                     if Colon_Index = 0 then
                        Abort_Msg
                          ("limit-line: incorrect line specification" &
                             " - missing ':' followed by operand",
                           With_Help => False);
                     end if;
                     CL_Switches.File_List.Append
                       (Limit_String.all
                          (Limit_String.all'First .. Colon_Index - 1));
                  end;
               end if;
            end;
         end if;
      end Process_Limit_Switches;

      ---------------------
      -- Sanity_Checking --
      ---------------------

      procedure Sanity_Checking is
      begin
         if (CL_Switches.Output_Msg_Only and CL_Switches.Replay)
           or else (CL_Switches.Output_Msg_Only and CL_Switches.F)
           or else (CL_Switches.F and CL_Switches.Replay)
         then
            Abort_Msg
              ("only one switch out of -f, --output-msg-only and --replay" &
                 " should be provided to gnatprove",
               With_Help => False);
         end if;
      end Sanity_Checking;

      -------------------------------------
      -- Set_Level_Timeout_Steps_Provers --
      -------------------------------------

      procedure Set_Level_Timeout_Steps_Provers (FS : out File_Specific) is
      begin

         case CL_Switches.Level is

            --  If level switch was not provided, set other switches to their
            --  default values.

            when Invalid_Level =>

               FS.Provers.Append ("cvc4");
               FS.Steps := Default_Steps;
               FS.Timeout := 0;
               FS.Memlimit := 0;

            --  See the UG for the meaning of the level switches

            when 0 =>
               FS.Provers.Append ("cvc4");
               FS.Steps := 0;
               FS.Timeout := 1;
               FS.Memlimit := 1000;

            when 1 =>
               FS.Provers.Append ("cvc4");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 1;
               FS.Memlimit := 1000;

            when 2 =>
               FS.Provers.Append ("cvc4");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 5;
               FS.Memlimit := 1000;

            when 3 =>
               FS.Provers.Append ("cvc4");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 20;
               FS.Memlimit := 2000;

            when 4 =>
               FS.Provers.Append ("cvc4");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 60;
               FS.Memlimit := 2000;

            when others =>
               Abort_Msg ("error: wrong argument for --level",
                          With_Help => False);

               raise Program_Error;
         end case;

         --  If option --timeout was not provided, keep timeout corresponding
         --  to level switch/default value. Otherwise, take the user-provided
         --  timeout. To be able to detect if --timeout was provided,
         --  CL_Switches.Timeout is string-based.

         if CL_Switches.Timeout.all = "" then
            null;
         else
            begin
               FS.Timeout := Integer'Value (CL_Switches.Timeout.all);
               if FS.Timeout < 0 then
                  raise Constraint_Error;
               end if;
            exception
               when Constraint_Error =>
                  Abort_Msg ("error: wrong argument for --timeout, " &
                               "must be a non-negative integer",
                             With_Help => False);
            end;
         end if;

         if CL_Switches.Memlimit = 0 then
            null;
         elsif CL_Switches.Memlimit < 0 then
            Abort_Msg ("error: wrong argument for --memlimit, " &
                         "must be a non-negative integer",
                       With_Help => False);
         else
            FS.Memlimit := CL_Switches.Memlimit;
         end if;

         if CL_Switches.Steps = Invalid_Steps then
            null;
         elsif CL_Switches.Steps < 0 then
            Abort_Msg ("error: wrong argument for --steps",
                       With_Help => False);
         else
            FS.Steps := CL_Switches.Steps;
         end if;

         --  Timeout is fully set now, we can set CE_Timeout. Basically we cap
         --  the CE_Timeout at Constants.Max_CE_Timeout seconds.

         FS.CE_Timeout :=
           (if FS.Timeout = 0 then Constants.Max_CE_Timeout
            else Integer'Min (FS.Timeout, Constants.Max_CE_Timeout));

         Set_Provers (CL_Switches.Prover, FS);
         Limit_Provers (FS.Provers);

         if CL_Switches.Output_Msg_Only then
            FS.Provers.Clear;
         end if;
      end Set_Level_Timeout_Steps_Provers;

      --------------
      -- Set_Mode --
      --------------

      procedure Set_Mode is
      begin
         if CL_Switches.Mode.all = "" then
            Mode := GPM_All;
         elsif CL_Switches.Mode.all = "prove" then
            Mode := GPM_Prove;
         elsif CL_Switches.Mode.all = "check" then
            Mode := GPM_Check;
         elsif CL_Switches.Mode.all = "check_all"
           or else CL_Switches.Mode.all = "stone"
         then
            Mode := GPM_Check_All;
         elsif CL_Switches.Mode.all = "flow"
           or else CL_Switches.Mode.all = "bronze"
         then
            Mode := GPM_Flow;
         elsif CL_Switches.Mode.all = "all"
           or else CL_Switches.Mode.all = "silver"
           or else CL_Switches.Mode.all = "gold"
         then
            Mode := GPM_All;
         else
            Abort_Msg ("error: wrong argument for --mode",
                       With_Help => False);
         end if;
      end Set_Mode;

      ---------------------
      -- Set_Output_Mode --
      ---------------------

      procedure Set_Output_Mode is
      begin
         if CL_Switches.Output.all = "" then
            Output := GPO_Pretty;
         elsif CL_Switches.Output.all = "brief" then
            Output := GPO_Brief;
         elsif CL_Switches.Output.all = "oneline" then
            Output := GPO_Oneline;
         elsif CL_Switches.Output.all = "pretty" then
            Output := GPO_Pretty;
         else
            Abort_Msg ("error: wrong argument for --output",
                       With_Help => False);
         end if;
      end Set_Output_Mode;

      ----------------------
      -- Set_Project_Vars --
      ----------------------

      procedure Set_Project_Vars (Proj : Project_Type) is
         Glob_Comp_Switch_Attr : constant Attribute_Pkg_List :=
           Build ("Builder", "Global_Compilation_Switches");
         Proof_Dir_Attr        : constant Attribute_Pkg_String :=
           Build ("Prove", "Proof_Dir");
         Switches_Attr         : constant Attribute_Pkg_List :=
           Build ("Prove", "Switches");
         Attr_Proof_Switches   : constant Attribute_Pkg_List :=
           Build ("Prove", "Proof_Switches");
      begin
         Prj_Attr.Target := new String'(Proj.Get_Target);
         Prj_Attr.Runtime := new String'(Proj.Get_Runtime);
         Prj_Attr.Builder.Global_Compilation_Switches_Ada :=
           (if Has_Attribute (Proj, Glob_Comp_Switch_Attr, "Ada")
            then Attribute_Value (Proj,
                                  Glob_Comp_Switch_Attr, "Ada")
            else null);
         Prj_Attr.Prove.Proof_Dir :=
           (if Has_Attribute (Proj, Proof_Dir_Attr)
            then new String'(Attribute_Value (Proj,
                                              Proof_Dir_Attr))
            else null);
         Prj_Attr.Prove.Switches :=
           (if Has_Attribute (Proj, Switches_Attr)
            then Attribute_Value (Proj, Switches_Attr)
            else null);
         Prj_Attr.Prove.Proof_Switches_Ada :=
           (if Has_Attribute (Proj, Attr_Proof_Switches, "Ada")
            then Attribute_Value (Proj, Attr_Proof_Switches, "Ada")
            elsif Has_Attribute (Proj, Attr_Proof_Switches, "ada")
            then Attribute_Value (Proj, Attr_Proof_Switches, "ada")
            else null);
         Prj_Attr.Prove.Proof_Switches_Indices :=
           new GNAT.Strings.String_List'
             (Attribute_Indexes (Proj, Attr_Proof_Switches,
                                 Use_Extended => False));

         if Prj_Attr.Prove.Switches /= null
           and then Prj_Attr.Prove.Switches.all'Length > 0
         then
            Put_Line
              (Standard_Error,
               "warning: attribute ""Switches"" of package ""Prove"" of " &
                 "your project file is deprecated");
            Put_Line
              (Standard_Error,
               "warning: use ""Proof_Switches (""Ada"")"" instead");
         end if;
      end Set_Project_Vars;

      -------------------
      -- Set_Proof_Dir --
      -------------------

      procedure Set_Proof_Dir is
      begin
         if Prj_Attr.Prove.Proof_Dir /= null
           and then Prj_Attr.Prove.Proof_Dir.all /= ""
         then
            declare
               Dir_Name : constant Virtual_File :=
                 Create (Tree.Root_Project.Project_Path.Dir_Name);
               Full_Name : constant Virtual_File :=
                 Create_From_Dir (Dir_Name, +Prj_Attr.Prove.Proof_Dir.all);
            begin
               Full_Name.Normalize_Path;
               Proof_Dir := new String'(Full_Name.Display_Full_Name);
            end;
         end if;
      end Set_Proof_Dir;

      --------------------
      -- Set_Proof_Mode --
      --------------------

      procedure Set_Proof_Mode (FS : in out File_Specific) is
         Input : String renames CL_Switches.Proof.all;
         Colon_Index : constant Natural :=
           Index (Source => Input, Pattern => ":");

         Proof_Input : constant String :=
           (if Colon_Index /= 0 then Input (Input'First .. Colon_Index - 1)
            else Input);
         Lazy_Input : constant String :=
           (if Colon_Index /= 0 then Input (Colon_Index + 1 .. Input'Last)
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
            Abort_Msg ("error: wrong argument for --proof",
                       With_Help => False);
         end if;

         if Lazy_Input = "" then
            FS.Lazy := True;
         elsif Lazy_Input = "all" then
            FS.Lazy := False;
         elsif Lazy_Input = "lazy" then
            FS.Lazy := True;
         else
            Abort_Msg ("error: wrong argument for --proof",
                       With_Help => False);
         end if;
      end Set_Proof_Mode;

      -----------------
      -- Set_Provers --
      -----------------

      procedure Set_Provers
        (Prover : GNAT.Strings.String_Access;
         FS     : in out File_Specific)
      is
         First : Integer;
         S : constant String :=
           (if Prover /= null then Prover.all else "");

      begin
         --  This procedure is called when the Provers list is already filled
         --  with the defaults from the --level switch.
         --  In replay mode, we only want to take into account provers when
         --  they were explicitly set, not when set by default. When not
         --  in replay mode, we only need to change the Provers list when
         --  --provers was explicitly set.

         if S = "" then
            if CL_Switches.Replay then
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

            --  Check if cvc4 or z3 have explicitly been requested, but are
            --  missing from the install.

            for Prover of FS.Provers loop
               if (Prover = "cvc4" and then not SPARK_Install.CVC4_Present)
                 or else
                   (Prover = "z3" and then not SPARK_Install.Z3_Present)
               then
                  Abort_Msg ("error: prover " & Prover &
                               " was selected, but it is not installed",
                             With_Help => False);
               end if;
            end loop;

         --  prover switch is set to "all"

         else
            if SPARK_Install.CVC4_Present then
               FS.Provers.Append ("cvc4");
            end if;
            if SPARK_Install.Z3_Present then
               FS.Provers.Append ("z3");
            end if;
            FS.Provers.Append ("altergo");
         end if;
      end Set_Provers;

      ---------------------
      -- Set_Report_Mode --
      ---------------------

      procedure Set_Report_Mode is
      begin
         if CL_Switches.Report.all = "" then
            Report := GPR_Fail;
         elsif CL_Switches.Report.all = "fail" then
            Report := GPR_Fail;
         elsif CL_Switches.Report.all = "all" then
            Report := GPR_All;
         elsif CL_Switches.Report.all = "provers" then
            Report := GPR_Provers;
         elsif CL_Switches.Report.all = "statistics" then
            Report := GPR_Statistics;
         else
            Abort_Msg ("error: wrong argument for --report",
                       With_Help => False);
         end if;
      end Set_Report_Mode;

      ----------------------
      -- Set_Warning_Mode --
      ----------------------

      procedure Set_Warning_Mode is
         Warn_Switch : String renames CL_Switches.Warnings.all;
      begin
         --  Note that "on" here is retained for backwards compatibility
         --  with release 14.0.1
         if Warn_Switch = "" then
            Warning_Mode := Gnat2Why_Opts.SW_Normal;
         elsif Warn_Switch = "off" then
            Warning_Mode := Gnat2Why_Opts.SW_Suppress;
         elsif Warn_Switch = "error" then
            Warning_Mode := Gnat2Why_Opts.SW_Treat_As_Error;
         elsif Warn_Switch = "on"
           or else Warn_Switch = "continue"
         then
            Warning_Mode := Gnat2Why_Opts.SW_Normal;
         else

            Abort_Msg ("error: wrong argument for --warnings",
                       With_Help => False);
         end if;
      end Set_Warning_Mode;

      --  Local variables

      Com_Lin : String_List :=
        (1 .. Ada.Command_Line.Argument_Count => <>);

      --  Help message read from a static file

      use CL_Switches;

   --  Start of processing for Read_Command_Line

   begin

      for Index in 1 .. Com_Lin'Last loop
         Com_Lin (Index) :=
           new String'(Ada.Command_Line.Argument (Index));
      end loop;

      --  The following code calls Parse_Switches several times, with varying
      --  mode argument and different switches, for different purposes. The
      --  same global variables are used for the result of the command line
      --  parsing (CL_Switches.*), but we make sure that this is correct by:
      --   - detecting invalid switches in the various attributes; (so the
      --     parsing of a file-specific switch can't override a switch that can
      --     only be specified globally);
      --   - saving file-specific and global switches into separate records;
      --   - parsing for error messages is done before the "real" parsing to
      --     get the values of switches.

      Initialize (Proj_Env);

      --  This call to Parse_Switches just parses project-relevant switches
      --  (-P, -X etc) and ignores the rest.

      Parse_Switches (Project_Parsing, Com_Lin);

      if CL_Switches.Version then
         Produce_Version_Output;
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      if CL_Switches.List_Categories then
         Produce_List_Categories_Output;
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      --  Before doing the actual second parsing, we read the project file in

      Tree := Init;
      Set_Project_Vars (Tree.Root_Project);

      if Clean then
         Clean_Up (Tree);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      if Prj_Attr.Prove.Switches /= null
        and then Prj_Attr.Prove.Switches.all'Length > 0
      then
         --  parse the Switches attribute of the project file; this is to
         --  detect invalid switches only.

         Parse_Switches (Global_Switches_Only,
                         Prj_Attr.Prove.Switches.all);
      end if;

      if Prj_Attr.Prove.Proof_Switches_Ada /= null then
         --  parse the Proof_Switches ("Ada") attribute of the project file;
         --  this is to detect invalid switches only.

         Parse_Switches (Global_Switches_Only,
                         Prj_Attr.Prove.Proof_Switches_Ada.all);
      end if;

      declare
         function Concat3 (A, B : String_List_Access; C : String_List)
           return String_List;

         function Concat4 (A, B, C : String_List_Access; D : String_List)
           return String_List;

         -------------
         -- Concat3 --
         -------------

         function Concat3 (A, B : String_List_Access; C : String_List)
                           return String_List is
         begin
            return (if A = null then (1 .. 0 => <>) else A.all) &
                   (if B = null then (1 .. 0 => <>) else B.all) &
                   C;
         end Concat3;

         -------------
         -- Concat4 --
         -------------

         function Concat4 (A, B, C : String_List_Access; D : String_List)
                           return String_List is
         begin
            return (if A = null then (1 .. 0 => <>) else A.all) &
                   (if B = null then (1 .. 0 => <>) else B.all) &
                   (if C = null then (1 .. 0 => <>) else C.all) &
                   D;
         end Concat4;

         Proj_Type : constant Project_Type := Root_Project (Tree);

      begin

         declare
            FS             : File_Specific;
            Parsed_Cmdline : constant String_List :=
              Concat3 (Prj_Attr.Prove.Switches,
                       Prj_Attr.Prove.Proof_Switches_Ada, Com_Lin);
         begin

            --  parse all switches that apply to all files, concatenated in the
            --  right order (most important is last).

            Parse_Switches (All_Switches, Parsed_Cmdline);
            Postprocess;
            File_Specific_Postprocess (FS);
            File_Specific_Map.Insert ("Ada", FS);

            --  ??? this piece of code should be in Postprocess, but it
            --  requires the FS object to be inserted in the map already.

            Counterexample :=
              not CL_Switches.No_Counterexample
              and then SPARK_Install.CVC4_Present
              and then not Is_Manual_Prover
              and then not CL_Switches.Output_Msg_Only;
         end;

         for FS_Entry of Prj_Attr.Prove.Proof_Switches_Indices.all loop
            if FS_Entry.all not in "Ada" | "ada" then
               Check_File_Part_Of_Project (Tree, FS_Entry.all);
               declare
                  FS             : File_Specific;
                  FS_Switches    : constant String_List_Access :=
                    Prj_Attr.Prove.Proof_Switches (Proj_Type, FS_Entry.all);
                  Parsed_Cmdline : constant String_List :=
                    Concat4 (Prj_Attr.Prove.Switches,
                             Prj_Attr.Prove.Proof_Switches_Ada,
                             FS_Switches, Com_Lin);
               begin
                  if FS_Switches /= null then

                     --  parse the file switches to check if they contain
                     --  invalid switches; this is for error reporting only.

                     Parse_Switches (File_Specific_Only,
                                     FS_Switches.all);
                  end if;

                  --  parse all switches that apply to a single file,
                  --  *including* the global switches. File-specific switches
                  --  are more important than the other switches in the project
                  --  file, but less so than the command line switches.

                  Parse_Switches (All_Switches, Parsed_Cmdline);
                  File_Specific_Postprocess (FS);
                  File_Specific_Map.Insert (FS_Entry.all, FS);
               end;
            end if;
         end loop;

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
         --  What we have come up with until now is a hash of the project dir.

         declare
            Obj_Dir_Hash : constant Hash_Type :=
              Full_Name_Hash (Proj_Type.Artifacts_Dir);
            Socket_Dir   : constant String := Compute_Socket_Dir (Proj_Type);
            Socket_Base  : constant String :=
               "why3server" & Hash_Image (Obj_Dir_Hash) & ".sock";
         begin
            Socket_Name := new String'(
               (if Socket_Dir = "" then Socket_Base
                else Compose (Socket_Dir, Socket_Base)));
            if Is_Coq_Prover then
               Prepare_Prover_Lib (Proj_Type.Artifacts_Dir.Display_Full_Name);
            end if;
         end;
      end;

      Sanitize_File_List (Tree);
   end Read_Command_Line;

   ------------------------
   -- Sanitize_File_List --
   ------------------------

   procedure Sanitize_File_List (Tree : Project_Tree) is
      use String_Lists;
   begin
      for Cursor in CL_Switches.File_List.Iterate loop
         declare
            File_VF : constant Virtual_File :=
              Tree.Create (Filesystem_String (Element (Cursor)));
            Info    : constant File_Info := Tree.Info (File_VF);
         begin
            case Unit_Part (Info) is
               when Unit_Body =>
                  null;
               when Unit_Spec =>
                  declare
                     Other_VF : constant Virtual_File :=
                       Tree.Other_File (File_VF);
                  begin
                     if Is_Regular_File (Other_VF) then
                        CL_Switches.File_List.Replace_Element
                          (Cursor,
                           String (Base_Name (Other_VF)));
                     end if;
                  end;
               when Unit_Separate =>

                  --  Here we try to find the proper unit to which belongs
                  --  the separate file. The "unit_name" function of
                  --  gnatcoll.projects sometimes returns the proper unit name,
                  --  but sometimes returns something like "unit.separate". If
                  --  there is a dot before the subunit name in what has been
                  --  returned, we remove the dot and the subunit name, but
                  --  keep all dots and names that belong to the child package
                  --  structure.

                  declare
                     Ptype : constant Project_Type := Tree.Root_Project;
                     Sep_Name : constant String := Unit_Name (Info);
                     Find_Dot : constant Natural :=
                       Index (Source  => Sep_Name,
                              Pattern => ".",
                              Going   => Ada.Strings.Backward);
                     U_Name : constant String :=
                       (if Find_Dot = 0 then Sep_Name
                        else Sep_Name (Sep_Name'First .. Find_Dot - 1));
                     Other_VF : constant Virtual_File :=
                       Tree.Create (Ptype.File_From_Unit
                                    (U_Name,
                                       Unit_Body,
                                       "Ada"));
                  begin
                     if Is_Regular_File (Other_VF) then
                        CL_Switches.File_List.Replace_Element
                          (Cursor,
                           String (Base_Name (Other_VF)));
                     end if;
                  end;
            end case;
         end;
      end loop;
   end Sanitize_File_List;

   -----------------------
   -- Set_CodePeer_Mode --
   -----------------------

   procedure Set_CodePeer_Mode (Input : String) is
   begin
      if Input = "" then
         CodePeer := False;
      elsif Input = "on" then
         CodePeer := True;
      elsif Input = "off" then
         CodePeer := False;
      else
         Abort_Msg ("error: wrong argument for --codepeer, " &
                      "must be one of (on, off)",
                    With_Help => False);
      end if;
   end Set_CodePeer_Mode;

   -----------------------
   -- SPARK_Report_File --
   -----------------------

   function SPARK_Report_File (Out_Dir : String) return String is
   begin
      return Ada.Directories.Compose (Out_Dir, "gnatprove.out");
   end SPARK_Report_File;

   -----------------------
   -- Compute_Why3_Args --
   -----------------------

   function Compute_Why3_Args (Obj_Dir : String;
                               FS      : File_Specific)
                               return String_Lists.List
   is

      Args    : String_Lists.List;
      Why3_VF : constant Virtual_File :=
        (if CL_Switches.Why3_Conf.all /= ""
         then Create (Filesystem_String (CL_Switches.Why3_Conf.all))
         else No_File);
      Gnatwhy3_Conf : constant String :=
        (if Why3_VF /= No_File then
           (if Is_Absolute_Path (Why3_VF)
            then CL_Switches.Why3_Conf.all
            else Compose (+Get_Current_Dir.Full_Name,
                          CL_Switches.Why3_Conf.all))
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
         Args : GNAT.OS_Lib.Argument_List :=
           (if Gnatwhy3_Conf /= "" then
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List ("Ada")),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all),
               6 => new String'("--why3-conf"),
               7 => new String'(Gnatwhy3_Conf))
            else
              (1 => new String'("--prepare-shared"),
               2 => new String'("--prover"),
               3 => new String'(Prover_List ("Ada")),
               4 => new String'("--proof-dir"),
               5 => new String'(Proof_Dir.all)));
         Res : Boolean;
         Old_Dir  : constant String := Current_Directory;
         Gnatwhy3 : constant String :=
           Compose (SPARK_Install.Libexec_Spark_Bin, "gnatwhy3");
      begin
         --  Use the Obj_Dir of gnat2why which already is "/.../gnatprove"
         Set_Directory (Obj_Dir);
         if Verbose then
            Ada.Text_IO.Put
              ("Changing to object directory: """ & Obj_Dir & """");
            Ada.Text_IO.New_Line;
            Ada.Text_IO.Put (Gnatwhy3 & " ");
            for Arg of Args loop
               Ada.Text_IO.Put (Arg.all & " ");
            end loop;
            Ada.Text_IO.New_Line;
         end if;
         GNAT.OS_Lib.Spawn (Program_Name => Gnatwhy3,
                            Args         => Args,
                            Success      => Res);
         Free (Args);
         Set_Directory (Old_Dir);
         if Verbose then
            Ada.Text_IO.Put
              ("Changing back to directory: """ & Old_Dir & """");
            Ada.Text_IO.New_Line;
         end if;
         if not Res then
            Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error,
                                  "Failed to compile shared");
            GNAT.OS_Lib.OS_Exit (1);
         end if;
      end Prepare_Why3_Manual;

   --  Start of processing for Compute_Why3_Args

   begin
      --  The first "argument" is in fact the command name itself, because in
      --  some cases we might want to change it.

      --  ??? If the semaphore is disabled via the --debug-no-semaphore switch,
      --  each gnat2why process may spawn many gnatwhy3 processes all at once.
      --  This may freeze the developer's machine if each of these processes
      --  takes a lot of memory.

      if Use_Semaphores then
         Args.Append ("spark_semaphore_wrapper");
         Args.Append (Base_Name (Socket_Name.all));
      end if;

      if CL_Switches.Memcached_Server /= null
        and then CL_Switches.Memcached_Server.all /= ""
      then
         Args.Append ("spark_memcached_wrapper");
         Args.Append (CL_Switches.Memcached_Server.all);
      end if;

      Args.Append ("gnatwhy3");

      Args.Append ("--timeout");
      Args.Append (Image (FS.Timeout, 1));

      Args.Append ("--steps");
      Args.Append (Image (FS.Steps, 1));

      Args.Append ("--memlimit");
      Args.Append (Image (FS.Memlimit, 1));

      if not FS.Provers.Is_Empty then
         Args.Append ("--prover");
         Args.Append (Prover_List (FS));
      end if;

      Args.Append ("--proof");
      Args.Append (To_String (FS.Proof));

      Args.Append ("--socket");
      Args.Append (Socket_Name.all);

      if Debug then
         Args.Append ("--debug");
      end if;

      if CL_Switches.Debug_Save_VCs then
         Args.Append ("--debug-save-vcs");
      end if;

      if Force then
         Args.Append ("--force");
      end if;

      if not FS.Lazy then
         Args.Append ("--prove-all");
      end if;

      if CL_Switches.Replay then
         Args.Append ("--replay");
      end if;

      Args.Append ("-j");
      Args.Append (Image (Parallel, 1));

      if CL_Switches.Limit_Line.all /= "" then
         Args.Append ("--limit-line");
         Args.Append (CL_Switches.Limit_Line.all);
      end if;
      if CL_Switches.Limit_Region.all /= "" then
         Args.Append ("--limit-region");
         Args.Append (CL_Switches.Limit_Region.all);
      end if;

      if Proof_Dir /= null then
         pragma Assert (Proof_Dir.all /= "");
         Create_Path (Compose (Proof_Dir.all, "sessions"));
         Args.Append ("--proof-dir");
         --  Why3 is executed in the gnatprove directory and does not know
         --  the project directory so we give it an absolute path to the
         --  proof_dir.
         Args.Append (Proof_Dir.all);
         if Is_Manual_Prover then
            Prepare_Why3_Manual;
         end if;
      end if;

      if Gnatwhy3_Conf /= "" then
         Args.Append ("--why3-conf");
         Args.Append (Gnatwhy3_Conf);
      end if;

      if CL_Switches.Why3_Debug.all /= "" then
         Args.Append ("--debug-why3");
         Args.Append (CL_Switches.Why3_Debug.all);
      end if;

      Args.Append ("--counterexample");
      Args.Append (if Counterexample then "on" else "off");

      if CL_Switches.Z3_Counterexample then
         Args.Append ("--ce-prover");
         Args.Append ("z3_ce");
      end if;

      Args.Append ("--ce-timeout");
      Args.Append (Image (FS.CE_Timeout, 1));

      return Args;
   end Compute_Why3_Args;

end Configuration;
