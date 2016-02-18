------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Text_IO;               use Ada.Text_IO;
with GNAT.Command_Line;         use GNAT.Command_Line;
with GNAT.Directory_Operations;
with GNAT.Strings;              use GNAT.Strings;
with GNAT.OS_Lib;
with SPARK2014VSN;              use SPARK2014VSN;
with System.Multiprocessors;

package body Configuration is

   MMode_Input  : aliased GNAT.Strings.String_Access;
   --  The mode of gnatprove, and the input variable for command line parsing
   --  set by option --mode=

   Warning_Input : aliased GNAT.Strings.String_Access;
   --  The warnings mode of gnatprove, and the input variable for command line
   --  parsing set by option --warnings=

   Report_Input : aliased GNAT.Strings.String_Access;
   --  The input variable for command line parsing set by option --report=

   Clean        : aliased Boolean;
   --  Set to True when --clean was given. Triggers cleanup of GNATprove
   --  intermediate files.

   Proj_Env     : Project_Environment_Access;
   --  This is the project environment used to load the project. It may be
   --  modified before loading it, e.g. -X switches

   procedure Abort_Msg (Config    : Command_Line_Configuration;
                        Msg       : String;
                        With_Help : Boolean)
     with No_Return;
   --  Stop the program, output the message and the help message when
   --  requested, then exit

   procedure Clean_Up (Tree : Project_Tree);
   --  Deletes generated "gnatprove" sub-directories in all object directories
   --  of the project.

   procedure Configure_Proof_Dir (Proj_Type : Project_Type);
   --  If attribute Proof_Dir is set in the project file, set global variable
   --  Proof_Dir to the full path <path-to-project-file>/<value-of-proof-dir>.

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
   --  called for unknown switches and for switches in section -cargs

   procedure Prepare_Prover_Lib (Config : Command_Line_Configuration);
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
   --  assume that there is no body)

   procedure Print_Errors (S : String);
   --  The String in argument is an error message from gnatcoll. Print it on
   --  stderr with a prefix

   procedure Set_Proof_Mode
     (Config : Command_Line_Configuration;
      Input  : String;
      Proof  : out Proof_Mode;
      Lazy   : out Boolean);
   --  parse the "--proof" option into the two values "proof" and "lazy"

   procedure Set_CodePeer_Mode
     (Config : Command_Line_Configuration;
      Input  : String);
   --  parse the --codepeer option (possibilities are "on" and "off")

   procedure Set_RTS_Dir
     (Config    : Command_Line_Configuration;
      Proj_Type : Project_Type;
      RTS_Dir   : in out GNAT.Strings.String_Access);
   --  if a runtime dir was defined, normalize it into an absolute path. To
   --  find the runtime dir, we first look at the initial value of RTS which
   --  contains the command-line argument of --RTS, if present. If it was not
   --  present, look in the project file to find the Runtime attribute.

   procedure Set_Target_Dir (Proj_Type : Project_Type);
   --  if "Target" attribute is set in the project file, set the global
   --  variable Target_Dir to its value, otherwise set that variable
   --  to "null". Also, issue a warning if -gnateT is not set in
   --  Builder.Global_Configuration_Switches

   procedure Check_gnateT_Switch (Proj_Type : Project_Type);
   --  Do the actual check and issue warning for the check mentioned in
   --  Set_Target_Dir: if -gnateT is not set in
   --  Builder.Global_Configuration_Switches

   function Is_Coq_Prover return Boolean;
   --  @return True iff one alternate prover is "coq"

   Usage_Message : constant String :=
     "-Pproj [files] [switches] [-cargs switches]";

   --  Hidden switches: --ide-progress-bar
   Help_Message : constant String :=
"proj is a GNAT project file" &
ASCII.LF &
"files is one or more file names" &
ASCII.LF &
"-cargs switches are passed to gcc" &
ASCII.LF &
ASCII.LF &
"gnatprove basic switches:" & ASCII.LF &
" -aP=p               Add path p to project path" &
ASCII.LF &
"     --assumptions   Output assumptions information" &
ASCII.LF &
"     --codepeer=c    Enable or disable CodePeer analysis (c=on,off*)" &
ASCII.LF &
"     --clean         Remove GNATprove intermediate files, and exit" &
ASCII.LF &
" -f                  Force recompilation/analysis of all units" &
ASCII.LF &
" -h, --help          Display this usage information" &
ASCII.LF &
" -jnnn               Use nnn parallel processes (default: 1)" &
ASCII.LF &
" -k                  Do not stop analysis at the first error" &
ASCII.LF &
"     --level=n       Set the level of proof " &
"(0 = faster* to 4 = more powerful)" &
ASCII.LF &
" -m                  Minimal reanalysis" &
ASCII.LF &
"     --mode=m        Set the mode of GNATprove (m=check, flow, prove, all*)"
& ASCII.LF &
" -q, --quiet         Be quiet/terse" &
ASCII.LF &
"     --report=r      Set the report mode of GNATprove " &
"(r=fail*, all, statistics)"
&
ASCII.LF &
" -u                  Unique analysis. Only analyze the given units" &
ASCII.LF &
" -U                  Analyze all units of all projects" &

ASCII.LF &
" -v, --verbose       Output extra verbose information" &
ASCII.LF &
"     --version       Output version of the tool and exit" &
ASCII.LF &
"     --warnings=w    Set the warning mode of GNATprove " &
"(w=off, continue*, error)" &
ASCII.LF &
ASCII.LF &
" * Main mode values" &
ASCII.LF &
"   . all           - Activates all modes (default)" &
ASCII.LF &
"   . check         - Check SPARK restrictions for code where SPARK_Mode=On" &
ASCII.LF &
"   . flow          - Prove object initialization and flow contracts" &
ASCII.LF &
"   . prove         - Prove subprogram contracts and absence of run-time " &
"errors" &
ASCII.LF &
ASCII.LF &
" * Report mode values" &
ASCII.LF &
"   . all           - Report all results of proving checks" &
ASCII.LF &
"   . fail          - Report failures to prove checks (default)" &
ASCII.LF &
"   . statistics    - Same as all, plus timing and steps information" &
ASCII.LF &
ASCII.LF &
" * Warning mode values" &
ASCII.LF &
"   . continue      - Issue warnings and continue (default)" &
ASCII.LF &
"   . error         - Treat warnings as errors" &
ASCII.LF &
"   . off           - Do not issue warnings" &
ASCII.LF &
ASCII.LF &
"gnatprove advanced switches:" &
ASCII.LF &
" --no-counterexample Do not generate a counterexample for unproved formulas" &
ASCII.LF &
" -d, --debug         Debug mode" &
ASCII.LF &
" --dbg-proof-only    Disable flow analysis (possibly unsound results)" &
ASCII.LF &
" --flow-debug        Extra debugging for flow analysis (requires graphviz)" &
ASCII.LF &
" --limit-line=s      Limit analysis to given file and line" &
ASCII.LF &
" --limit-subp=s      Limit analysis to subprogram defined by file and line" &
ASCII.LF &
" --pedantic          Use a strict interpretation of the Ada standard" &
ASCII.LF &
" --proof=g[:l]       Set the proof modes for generation of formulas" &
ASCII.LF &
"                     (g=per_check*, per_path, progressive) (l=lazy*, all)" &
ASCII.LF &
" --prover=s[,s]*     Use given provers (s=altergo, cvc4*, z3, ...)" &
ASCII.LF &
" --RTS=dir           Specify the Ada runtime name/location" &
ASCII.LF &
" --steps=nnn         Set the maximum number of proof steps (prover-specific)"
& ASCII.LF &
" --timeout=s         Set the prover timeout in seconds (default: 1)" &
ASCII.LF &
" --why3-conf=f       Specify a configuration file for why3" &
ASCII.LF &
ASCII.LF &
" * Proof mode values for generation" &
ASCII.LF &
"   . per_check     - Generate one formula per check (default)" &
ASCII.LF &
"   . per_path      - Generate one formula per path for each check" &
ASCII.LF &
"   . progressive   - Start with one formula per check, then split into" &
ASCII.LF &
"                     paths when needed" &
ASCII.LF &
ASCII.LF &
" * Proof mode values for laziness" &
ASCII.LF &
"   . all           - Attempt to prove all formulas" &
ASCII.LF &
"                     (most suited for combination of automatic and " &
"manual proof)" &
ASCII.LF &
"   . lazy          - Stop at first unproved formula for each check" &
ASCII.LF &
"                     (most suited for fully automatic proof) (default)" &
ASCII.LF &
ASCII.LF &
" * Prover name values" &
ASCII.LF &
"   (Default prover is cvc4.)" &
ASCII.LF &
"   (Provers marked with [steps] support the --steps switch.)" &
ASCII.LF &
"   . altergo       - [steps] Use Alt-Ergo" &
ASCII.LF &
"   . cvc4          - [steps] Use CVC4" &
ASCII.LF &
"   . z3            - [steps] Use Z3" &
ASCII.LF &
"   . ...           - Any other prover configured in your .why3.conf file" &
ASCII.LF;

   ---------------
   -- Abort_Msg --
   ---------------

   procedure Abort_Msg (Config    : Command_Line_Configuration;
                        Msg       : String;
                        With_Help : Boolean) is
   begin
      if Msg /= "" then
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      end if;
      if With_Help then
         Display_Help (Config);
      else
         Ada.Text_IO.Put_Line
           ("Try ""gnatprove --help"" for more information.");
      end if;
      GNAT.OS_Lib.OS_Exit (1);
   end Abort_Msg;

   -------------------------
   -- Check_gnateT_Switch --
   -------------------------

   procedure Check_gnateT_Switch (Proj_Type : Project_Type) is
      Attr : constant Attribute_Pkg_List :=
        Build ("Builder", "Global_Compilation_Switches");
   begin

      --  We check the conditions for *not* issuing the warning, in which
      --  case we return. At the end of the procedure, the warning is issued
      --  unconditionally.

      if Has_Attribute (Proj_Type, Attr, "Ada") then
         declare
            Args : GNAT.Strings.String_List_Access :=
              Attribute_Value (Proj_Type, Attr, "Ada");
         begin
            for Arg of Args.all loop
               if GNATCOLL.Utils.Starts_With (Arg.all, "-gnateT=") then
                  return;
               end if;
            end loop;
            Free (Args);
         end;
      end if;
      Put_Line
        (Standard_Error,
         "warning: attribute ""Target"" of your project file is currently " &
           "ignored by gnatprove");
      Put_Line
        (Standard_Error,
         "warning: to specify target properties, specify option ""-gnateT"" " &
           "using ""Builder.Global_Compilation_Switches""");
   end Check_gnateT_Switch;

   --------------
   -- Clean_Up --
   --------------

   procedure Clean_Up (Tree : Project_Tree) is

      function Is_Externally_Built (Project : Project_Type) return Boolean;
      --  Returns True if the project is externally built

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
            declare
               Obj_Dir  : constant Virtual_File := Project.Object_Dir;
               Name_Dir : constant String := +Base_Dir_Name (Obj_Dir);
               Rm_Dir   : constant String := Obj_Dir.Display_Full_Name;
            begin
               pragma Assert (Name_Dir = Name_GNATprove);
               if GNAT.OS_Lib.Is_Directory (Rm_Dir) then
                  if Verbose then
                     Ada.Text_IO.Put ("Deleting directory " & Rm_Dir & "...");
                  end if;
                  GNAT.Directory_Operations.Remove_Dir (Rm_Dir, True);
                  if Verbose then
                     Ada.Text_IO.Put_Line (" done");
                  end if;
               end if;
            exception
               when GNAT.Directory_Operations.Directory_Error =>
                  if Verbose then
                     Ada.Text_IO.Put_Line (" failed, please delete manually");
                  end if;
            end;
         end if;

         Next (Iter);
      end loop;
   end Clean_Up;

   -------------------------
   -- Configure_Proof_Dir --
   -------------------------

   procedure Configure_Proof_Dir (Proj_Type : Project_Type) is
      Attr : constant Attribute_Pkg_String := Build ("Prove", "Proof_Dir");
   begin
      if Has_Attribute (Proj_Type, Attr) then
         declare
            Dir_Name : constant Virtual_File :=
              Create (Proj_Type.Project_Path.Dir_Name);
            File_Name : constant String :=
              Attribute_Value (Proj_Type, Attr, Default => "");
            Full_Name : constant Virtual_File :=
              Create_From_Dir (Dir_Name, +File_Name);
         begin
            Full_Name.Normalize_Path;
            Proof_Dir := new String'(Full_Name.Display_Full_Name);
         end;
      end if;
   end Configure_Proof_Dir;

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

         Equal := Switch'First + 2;
         while Equal in Switch'Range
           and then Switch (Equal) /= '='
         loop
            Equal := Equal + 1;
         end loop;

         --  ... and then set the variable in the environment.

         Proj_Env.Change_Environment
           (Switch (Switch'First + 2 .. Equal - 1),
            Switch (Equal + 1 .. Switch'Last));

         --  Second, we add the whole switch to the list of Scenario switches

         Scenario_Variables.Append (Switch);
      elsif Switch = "-aP" then
         GPR_Project_Path.Append (Parameter);
      end if;
   end Handle_Project_Loading_Switches;

   -------------------
   -- Handle_Switch --
   -------------------

   procedure Handle_Switch
     (Switch    : String;
      Parameter : String;
      Section   : String) is
   begin
      if Section = "cargs" then
         Cargs_List.Append (Switch & Separator & Parameter);

      elsif Switch (Switch'First) /= '-' then

         --  We assume that the "switch" is actually an argument and put it in
         --  the file list

         File_List.Append (Switch);

      --  We can ignore -X switches, have been parsed by the first pass

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
   begin
      if Alter_Prover.all = "" then
         return False;
      elsif
        Alter_Prover.all = "coq" or else
        Alter_Prover.all = "isabelle"
      then
         return True;
      else
         return False;
      end if;
   end Is_Manual_Prover;

   -------------------
   -- Is_Coq_Prover --
   -------------------

   function Is_Coq_Prover return Boolean is
   begin
      if Is_Manual_Prover and then Alter_Prover.all = "coq" then
         return True;
      end if;
      return False;
   end Is_Coq_Prover;

   ------------------------
   -- Prepare_Prover_Lib --
   ------------------------

   procedure Prepare_Prover_Lib (Config : Command_Line_Configuration) is

      Success : Boolean := True;
      Prover_Name : constant String :=
        Ada.Characters.Handling.To_Lower (Alter_Prover.all);
      Prover_Lib_Dir : constant String := Compose
        (Compose (Why3_Dir, "libs"), Name => Prover_Name);
      Prover_Obj_Dir : constant String := Compose
        (Compose (Main_Subdir.all, "why3_libs"), Name => Prover_Name);

      procedure Compile_Lib (Dir, File : String);

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
               Source_Dest : String_Access :=
                 new String'(Compose (Target_Dir, Name => File & ".v"));
            begin
               --  Copy file
               Create_Path (Prover_Obj_Dir);
               if not Exists (Target_Dir) then
                  Create_Directory (Target_Dir);
               end if;
               Copy_File (Compose (Lib_Dir, Name => File & ".v"),
                          Source_Dest.all);
               --  Build it
               declare
                  Coqc_Bin : String_Access :=
                    GNAT.OS_Lib.Locate_Exec_On_Path ("coqc");
                  Args : GNAT.OS_Lib.Argument_List :=
                    (1 => new String'("-R"),
                     2 => new String'(Prover_Obj_Dir),
                     3 => new String'("Why3"),
                     4 => Source_Dest);
               begin
                  if Coqc_Bin = null then
                     Abort_Msg (Config,
                                Msg       => "coq prover not present in PATH",
                                With_Help => False);
                  end if;
                  GNAT.OS_Lib.Spawn (Program_Name => Coqc_Bin.all,
                                     Args         => Args,
                                     Success      => Success);
                  if not Success then
                     Abort_Msg (Config,
                                Msg       =>
                                  "error during compilations of " &
                                  Source_Dest.all,
                                With_Help => False);
                  end if;

                  GNAT.OS_Lib.Free (Coqc_Bin);

                  for It in Args'Range loop
                     Free (Args (It));
                  end loop;
                  Source_Dest := null;
               end;
            end;
         end if;
      end Compile_Lib;

   begin
      Compile_Lib ("", "BuiltIn");
      Compile_Lib ("bool", "Bool");
      Compile_Lib ("int", "Int");
      Compile_Lib ("int", "Abs");
      Compile_Lib ("int", "EuclideanDivision");
      Compile_Lib ("int", "ComputerDivision");
   end Prepare_Prover_Lib;

   ---------------
   -- To_String --
   ---------------

   function To_String (P : Proof_Mode) return String is
   begin
      case P is
         when No_WP => return "no_wp";
         when All_Split => return "all_split";
         when Then_Split => return "then_split";
         when Path_WP => return "path_wp";
         when No_Split => return "no_split";
      end case;
   end To_String;

   ------------------
   -- Print_Errors --
   ------------------

   procedure Print_Errors (S : String) is
   begin
      Ada.Text_IO.Put_Line (Standard_Error, "gnatprove: " & S);
   end Print_Errors;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project_Tree) is
      Config : Command_Line_Configuration;

      function Init return Project_Tree;
      --  Load the project file; This function requires the project file to be
      --  present.

      ----------
      -- Init --
      ----------

      function Init return Project_Tree is
         GNAT_Version : GNAT.Strings.String_Access;
         Tree         : Project_Tree;

      begin
         Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
         Set_Object_Subdir (Proj_Env.all, Subdir_Name);
         Proj_Env.Register_Default_Language_Extension ("C", ".h", ".c");
         declare
            Sswitches : constant String :=
                  Register_New_Attribute ("Switches", "Prove",
                                          Is_List => True);
         begin
            if Sswitches /= "" then
               Abort_Msg (Config, Sswitches, With_Help => False);
            end if;
         end;

         declare
            Sproof_dir : constant String :=
              Register_New_Attribute ("Proof_Dir", "Prove");
         begin
            if Sproof_dir /= "" then
               Abort_Msg (Config, Sproof_dir, With_Help => False);
            end if;
         end;

         declare
            Arr  : constant File_Array := Proj_Env.Predefined_Project_Path;
            Arr2 : File_Array (1 .. Integer (GPR_Project_Path.Length));
            I    : Integer := 1;
         begin
            for S of GPR_Project_Path loop
               Arr2 (I) := Create (Filesystem_String (S));
               I := I + 1;
            end loop;
            Proj_Env.Set_Predefined_Project_Path (Arr & Arr2);
         end;

         if Project_File.all /= "" then
            Tree.Load
              (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
               Proj_Env,
               Errors => Print_Errors'Access);
         else
            Abort_Msg (Config, "No project file is given", With_Help => False);
         end if;
         return Tree;
      end Init;

      First_Config : Command_Line_Configuration;
      Com_Lin : aliased String_List :=
        (1 .. Ada.Command_Line.Argument_Count => <>);

   --  Start of processing for Read_Command_Line

   begin
      Set_Usage
        (First_Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      Set_Usage
        (Config,
         Usage     => Usage_Message,
         Help_Msg  => Help_Message);

      --  if no arguments have been given, print help message and exit

      if Com_Lin'Length = 0 then
         Abort_Msg (Config, "", With_Help => True);
      end if;

      --  We parse the command line *twice*. The reason is that before parsing
      --  the commandline, we need to load the project (e.g. because the
      --  project also may specify extra switches), but loading the project
      --  requires reading some specific switches such as -P and -X.

      --  The first parsing only defines -P, -X and immediately terminating
      --  switches such as --version and --clean. We also need a wildcard to
      --  ignore the other switches.

      --  Then, the project is loaded. We concatenate the extra switches to the
      --  command line and then we reparse the whole thing.

      --  As parsing the command line consumes it, we start by copying it.

      for Index in 1 .. Com_Lin'Last loop
         Com_Lin (Index) :=
           new String'(Ada.Command_Line.Argument (Index));
      end loop;

      Define_Switch
        (First_Config, Project_File'Access,
         "-P:",
         Help => "The name of the project file");

      Define_Switch
        (First_Config,
         Version'Access,
         Long_Switch => "--version",
         Help => "Output version of the tool");

      Define_Switch
        (First_Config,
         Verbose'Access,
         "-v", Long_Switch => "--verbose");

      Define_Switch
         (First_Config,
          Clean'Access,
          Long_Switch => "--clean",
          Help => "Remove GNATprove intermediate files");

      Define_Switch (First_Config, "-aP=");

      Define_Switch (First_Config, "*", Help => "list of source files");

      --  We now initialize the project environment; it may be changed by the
      --  first parse of the command line.

      Initialize (Proj_Env);

      Getopt (First_Config,
              Callback => Handle_Project_Loading_Switches'Access,
              Concatenate => False);

      if Version then
         Ada.Text_IO.Put_Line (SPARK2014_Version_String);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      --  The second parsing needs the info for all switches, including the
      --  ones that are only used by the first pass (e.g. -aP), so that they
      --  can be properly ignored. An exception is the option -X, which is
      --  explicitly ignored by the callback Handle_Switch

      Define_Switch (Config, "-aP=");

      Define_Switch
         (Config,
          Debug'Access,
          "-d", Long_Switch => "--debug");

      Define_Switch
         (Config,
          Flow_Extra_Debug'Access,
          Long_Switch => "--flow-debug");

      Define_Switch
         (Config,
          Debug_Proof_Only'Access,
          Long_Switch => "--dbg-proof-only");

      Define_Switch
        (Config, Project_File'Access,
         "-P:");

      Define_Switch
        (Config,
         Force'Access,
         "-f");

      Define_Switch
        (Config, Parallel'Access,
         Long_Switch => "-j:",
         Initial => 1);

      Define_Switch
        (Config,
         Continue_On_Error'Access,
         "-k");

      Define_Switch
        (Config,
         MMode_Input'Access,
         Long_Switch => "--mode=");

      Define_Switch
        (Config,
         Minimal_Compile'Access,
         "-m");

      Define_Switch
        (Config,
         Warning_Input'Access,
         Long_Switch => "--warnings=");

      Define_Switch
        (Config,
         Proof_Input'Access,
         Long_Switch => "--proof=");

      Define_Switch
        (Config,
         CodePeer_Input'Access,
         Long_Switch => "--codepeer=");

      Define_Switch
        (Config,
         Pedantic'Access,
         Long_Switch => "--pedantic");

      Define_Switch
        (Config,
         RTS_Dir'Access,
         Long_Switch => "--RTS=");

      Define_Switch
        (Config,
         IDE_Progress_Bar'Access,
         Long_Switch => "--ide-progress-bar");

      Define_Switch
         (Config,
          Quiet'Access,
          "-q", Long_Switch => "--quiet");

      Define_Switch
        (Config,
         Report_Input'Access,
         Long_Switch => "--report=");

      --  If not specified on the command-line, value of steps is invalid
      Define_Switch
         (Config, Steps'Access,
          Long_Switch => "--steps=",
          Initial => Invalid_Step);

      --  If not specified on the command-line, value of level is invalid
      Define_Switch
         (Config, Level'Access,
          Long_Switch => "--level=",
          Initial => Invalid_Level);

      --  If not specified on the command-line, value of timeout is invalid
      Define_Switch
         (Config, Timeout'Access,
          Long_Switch => "--timeout=",
          Initial => Invalid_Timeout);

      Define_Switch
         (Config,
          Only_Given'Access,
          "-u");

      Define_Switch
         (Config,
          All_Projects'Access,
          "-U");

      Define_Switch
        (Config,
         Verbose'Access,
         "-v", Long_Switch => "--verbose");

      Define_Switch
        (Config,
         Assumptions'Access,
         Long_Switch => "--assumptions");

      Define_Switch
        (Config,
         Limit_Line'Access,
         Long_Switch => "--limit-line=");

      Define_Switch (Config, "*");

      Define_Switch
        (Config,
         Limit_Subp'Access,
         Long_Switch => "--limit-subp=");

      Define_Switch
        (Config,
         Alter_Prover'Access,
         Long_Switch => "--prover=");

      Define_Switch
        (Config,
         No_Counterexample'Access,
         Long_Switch => "--no-counterexample");

      Define_Switch
        (Config,
         Report_Input'Access,
         Long_Switch => "--report=");

      Define_Switch
        (Config, Why3_Config_File'Access,
         Long_Switch => "--why3-conf=");

      --  This switch is not documented on purpose. We provide the fake_*
      --  binaries instead of the real prover binaries. This helps when
      --  collecting benchmarks for prover developers.
      Define_Switch
         (Config, Benchmark_Mode'Access,
          Long_Switch => "--benchmark");

      --  This switch is not documented on purpose. This enables memcached
      --  caching for developers.

      Define_Switch
         (Config, Caching'Access,
          Long_Switch => "--cache");

      Define_Section (Config, "cargs");
      Define_Switch (Config, "*", Section => "cargs");

      --  Before doing the actual second parsing, we read the project file in

      Tree := Init;

      if Clean then
         Clean_Up (Tree);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      declare
         Proj_Type      : constant Project_Type := Root_Project (Tree);
         Extra_Switches : constant String_List_Access :=
           Attribute_Value (Proj_Type, Build ("Prove", "Switches"));
      begin
         if Extra_Switches /= null then
            declare
               All_Switches   : aliased constant String_List :=
                 Extra_Switches.all & Com_Lin;
               All_Access     : constant String_List_Access :=
                 new String_List'(All_Switches);
               Parser         : Opt_Parser;
            begin
               Initialize_Option_Scan (Parser, All_Access);
               Getopt (Config,
                       Callback => Handle_Switch'Access,
                       Parser   => Parser,
                       Concatenate => False);
            end;
         else
            Getopt (Config,
                    Callback => Handle_Switch'Access,
                    Concatenate => False);
         end if;

         Configure_Proof_Dir (Proj_Type);

         --  After the call to Init, the object directory includes the
         --  sub-directory "gnatprove" set through Set_Object_Subdir.
         Main_Subdir := new String'(Proj_Type.Object_Dir.Display_Full_Name);

         declare
            Obj_Dir_Hash : constant Hash_Type :=
              Full_Name_Hash (Proj_Type.Object_Dir);
         begin
            Socket_Name := new String'
              ("why3server" & Hash_Image (Obj_Dir_Hash) & ".sock");
         end;
      end;

      --  Adjust the number of parallel processes. If -j0 was used, the
      --  number of processes should be set to the actual number of
      --  processors available on the machine.

      if Parallel = 0 then
         Parallel := Natural (System.Multiprocessors.Number_Of_CPUs);
      elsif Parallel < 0 then
         Abort_Msg (Config,
                    "error: wrong argument for -j",
                    With_Help => False);
      end if;

      --  Check value of integer switches --steps, --level and --timeout, to
      --  make sure they are either the special invalid value or an expected
      --  value.

      if Steps < 0 and Steps /= Invalid_Step then
         Abort_Msg (Config,
                    "error: wrong argument for --steps",
                    With_Help => False);
      end if;

      if Level not in 0 .. 4 and Level /= Invalid_Level then
         Abort_Msg (Config,
                    "error: wrong argument for --level",
                    With_Help => False);
      end if;

      if Timeout < 0 and Timeout /= Invalid_Timeout then
         Abort_Msg (Config,
                    "error: wrong argument for --timeout",
                    With_Help => False);
      end if;

      --  Set modes from string values passed in argument to switches

      if MMode_Input.all = "prove" then
         MMode := GPM_Prove;
      elsif MMode_Input.all = "check" then
         MMode := GPM_Check;
      elsif MMode_Input.all = "flow" then
         MMode := GPM_Flow;
      elsif MMode_Input.all = "all" or else MMode_Input.all = "" then
         MMode := GPM_All;
      else
         Abort_Msg (Config,
                    "error: wrong argument for --mode",
                    With_Help => False);
      end if;

      --  Note that "on" here is retained for backwards compatibility
      --  with release 14.0.1
      if Warning_Input.all = "off" then
         Warning_Mode := Opt.Suppress;
      elsif Warning_Input.all = "error" then
         Warning_Mode := Opt.Treat_As_Error;
      elsif Warning_Input.all = "on"
        or else Warning_Input.all = "continue"
        or else Warning_Input.all = ""
      then
         Warning_Mode := Opt.Normal;
      else
         Abort_Msg (Config,
                    "error: wrong argument for --warnings",
                    With_Help => False);
      end if;

      if Report_Input.all = "fail" or else Report_Input.all = "" then
         Report := GPR_Fail;
      elsif Report_Input.all = "all" then
         Report := GPR_Verbose;
      elsif Report_Input.all = "statistics" then
         Report := GPR_Statistics;
      else
         Abort_Msg (Config,
                    "error: wrong argument for --report",
                    With_Help => False);
      end if;

      Set_Proof_Mode (Config, Proof_Input.all, Proof,  Lazy);
      Set_CodePeer_Mode (Config, CodePeer_Input.all);
      Set_RTS_Dir (Config, Tree.Root_Project, RTS_Dir);
      Set_Target_Dir (Tree.Root_Project);

      if Flow_Extra_Debug and not Debug then
         Abort_Msg (Config,
                    "extra debugging for flow analysis requires -d",
                    With_Help => False);
      end if;

      --  Unless -U is specified, use of --limit-line or --limit-subp leads
      --  to only the file with the given line or subprogram to be analyzed.
      --  Specifying -U with --limit-line or --limit-subp is useful to
      --  force analysis of all files, when the line or subprogram is
      --  inside a generic or itself a generic, so that all instances of
      --  the line/subprogram are analyzed.

      if not All_Projects then
         declare
            Limit_String : GNAT.Strings.String_Access := null;

         begin
            --  Limit_Line and Limit_Subp both imply -u for the corresponding
            --  file. We take care of that using the Limit_String variable,
            --  note that "Limit_Line" is stronger naturally.

            if not Null_Or_Empty_String (Limit_Subp) then
               Limit_String := Limit_Subp;
            end if;

            if not Null_Or_Empty_String (Limit_Line) then
               Limit_String := Limit_Line;
            end if;

            if Limit_String /= null then
               declare
                  Index : Integer := Limit_String.all'First;
               begin
                  while Index < Limit_String.all'Last and then
                    Limit_String.all (Index) /= ':' loop
                     Index := Index + 1;
                  end loop;
                  if Index = Limit_String.all'Last then
                     Abort_Msg
                       (Config,
                        "limit-line: incorrect line specification" &
                          " - missing ':' followed by operand",
                        With_Help => False);
                  end if;
                  File_List.Append
                    (Limit_String.all (Limit_String.all'First .. Index - 1));
               end;
               Only_Given := True;
            end if;
         end;
      end if;

      if Is_Coq_Prover then
         Prepare_Prover_Lib (Config);
      end if;
      Sanitize_File_List (Tree);

   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
      when Invalid_Parameter =>
         Abort_Msg (Config,
                    "No parameter given to switch -" & Full_Switch,
                    With_Help => False);
   end Read_Command_Line;

   ------------------------
   -- Sanitize_File_List --
   ------------------------

   procedure Sanitize_File_List (Tree : Project_Tree) is
      use String_Lists;
   begin
      for Cursor in File_List.Iterate loop
         declare
            File_VF : constant Virtual_File :=
              Create_From_Base (Filesystem_String (Element (Cursor)));
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
                     File_List.Replace_Element
                       (Cursor,
                        String (Base_Name (Other_VF)));
                  end if;
               end;
               when Unit_Separate =>

                  --  Here we try to find the proper unit to which belongs
                  --  the separate file. The "unit_name" function of
                  --  gnatcoll.projects sometimes returns the proper unit name,
                  --  but sometimes returns something like "unit.separate". If
                  --  there is a dot in what has been returned, we remove it.

                  declare
                     Ptype : constant Project_Type := Tree.Root_Project;
                     Sep_Name : constant String := Unit_Name (Info);
                     Find_Dot : constant Natural := Index (Sep_Name, ".");
                     U_Name : constant String :=
                       (if Find_Dot = 0 then Sep_Name
                        else Sep_Name (Sep_Name'First .. Find_Dot - 1));
                     Other_VF : constant Virtual_File :=
                       Create_From_Base (Ptype.File_From_Unit
                                           (U_Name,
                                            Unit_Body,
                                            "Ada"));
                  begin
                     if Is_Regular_File (Other_VF) then
                        File_List.Replace_Element
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

   procedure Set_CodePeer_Mode
     (Config : Command_Line_Configuration;
      Input  : String) is
   begin
      CodePeer := False;
      if Input = "on" then
         CodePeer := True;
      elsif Input = "off" then
         CodePeer := False;
      elsif Input = "" then
         null;
      else
         Abort_Msg (Config,
                    "error: wrong argument for --codepeer, " &
                      "must be one of (on, off)",
                    With_Help => False);
      end if;
   end Set_CodePeer_Mode;

   --------------------
   -- Set_Proof_Mode --
   --------------------

   procedure Set_Proof_Mode
     (Config : Command_Line_Configuration;
      Input  : String;
      Proof  : out Proof_Mode;
      Lazy   : out Boolean)
   is
      Find_Colon : Integer := 0;
   begin
      for I in Input'Range loop
         if Input (I) = ':' then
            Find_Colon := I;
            exit;
         end if;
      end loop;

      declare
         Proof_Input : constant String :=
           (if Find_Colon /= 0 then Input (Input'First .. Find_Colon - 1)
            else Input);
         Lazy_Input : constant String :=
           (if Find_Colon /= 0 then Input (Find_Colon + 1 .. Input'Last)
            else "");
      begin
         if Proof_Input = "progressive" then
            Proof := Then_Split;
         elsif Proof_Input = "per_path" then
            Proof := Path_WP;
         elsif Proof_Input = "per_check" then
            Proof := No_Split;

         --  Hidden debugging values

         elsif Proof_Input = "no_wp" then
            Proof := No_WP;
         elsif Proof_Input = "all_split" then
            Proof := All_Split;

         --  The default proof mode is per_check

         elsif Proof_Input = "" then
            Proof := No_Split;
         else
            Abort_Msg (Config,
                       "error: wrong argument for --proof",
                       With_Help => False);
         end if;

         if Lazy_Input = "all" then
            Lazy := False;
         elsif Lazy_Input = "lazy" or else Lazy_Input = "" then
            Lazy := True;
         else
            Abort_Msg (Config,
                       "error: wrong argument for --proof",
                       With_Help => False);
         end if;
      end;
   end Set_Proof_Mode;

   -----------------
   -- Set_RTS_Dir --
   -----------------

   procedure Set_RTS_Dir
     (Config    : Command_Line_Configuration;
      Proj_Type : Project_Type;
      RTS_Dir   : in out GNAT.Strings.String_Access)
   is
      Target  : constant String := Proj_Type.Get_Target;
      Runtime : constant String := Proj_Type.Get_Runtime;
   begin
      --  When command-line switch --RTS is not provided, consider attribute
      --  Runtime of project file.

      if Null_Or_Empty_String (RTS_Dir) then

         --  If project has a target and runtime attribute specified, then
         --  look for a corresponding runtime directory in the compiler
         --  installation, which should work if GNAT and SPARK were
         --  installed at the same location.

         if Target /= "" and then Runtime /= "" then
            declare
               Dir     : constant String :=
                 Executable_Location & Target &
                 GNAT.Directory_Operations.Dir_Separator & "lib" &
                 GNAT.Directory_Operations.Dir_Separator & "gnat" &
                 GNAT.Directory_Operations.Dir_Separator & Runtime;
            begin
               if GNAT.OS_Lib.Is_Directory (Dir) then
                  RTS_Dir := new String'(Dir);
               end if;
            end;
         end if;

         --  Otherwise, pass the value of the runtime attribute directly, which
         --  should work if the runtime has been copied in SPARK installation.

         if Null_Or_Empty_String (RTS_Dir)
           and then Proj_Type.Has_Attribute (Runtime_Attribute)
         then
            RTS_Dir := new String'
              (Proj_Type.Attribute_Value (Runtime_Attribute, Index => "Ada"));
         end if;
      end if;

      --  When --RTS is not provided and attribute Runtime is not set in the
      --  project file, return.

      if Null_Or_Empty_String (RTS_Dir) then
         return;
      end if;

      --  Search for the full path to the runtime directory

      declare
         Dir : Virtual_File :=
           Create_From_Base (Filesystem_String (RTS_Dir.all));
      begin

         --  if this test is true, then RTS_Dir is a valid absolute or relative
         --  path (we don't care which)

         if Is_Directory (Dir) then
            Normalize_Path (Dir);
            RTS_Dir := new String'(Dir.Display_Full_Name);
         else
            Dir := Create_From_Dir
              (Create (Filesystem_String (Runtimes_Dir)),
               Filesystem_String (RTS_Dir.all));
            if Is_Directory (Dir) then
               Normalize_Path (Dir);
               RTS_Dir := new String'(Dir.Display_Full_Name);
            else
               Abort_Msg (Config, "could not find runtime " & RTS_Dir.all,
                          With_Help => False);
            end if;
         end if;
      end;
   end Set_RTS_Dir;

   --------------------
   -- Set_Target_Dir --
   --------------------

   procedure Set_Target_Dir (Proj_Type : Project_Type) is
   begin
      Target_Dir := null;
      if Has_Attribute (Proj_Type, Target_Attribute) then
         declare
            Targ : constant String :=
              Attribute_Value (Proj_Type, Target_Attribute);
         begin
            if Targ /= "" then
               Target_Dir := new String'(Targ);
               Check_gnateT_Switch (Proj_Type);
            end if;
         end;
      end if;
   end Set_Target_Dir;

   -----------------------
   -- SPARK_Report_File --
   -----------------------

   function SPARK_Report_File (Out_Dir : String) return String is
   begin
      return Ada.Directories.Compose (Out_Dir, "gnatprove.out");
   end SPARK_Report_File;

end Configuration;
