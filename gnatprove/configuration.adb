------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2019, AdaCore                   --
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
with Ada.Direct_IO;
with Ada.Environment_Variables;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Ada.Text_IO;               use Ada.Text_IO;
with Call;                      use Call;
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

   Clean : aliased Boolean;
   --  Set to True when --clean was given. Triggers cleanup of GNATprove
   --  intermediate files.

   Proj_Env : Project_Environment_Access;
   --  This is the project environment used to load the project. It may be
   --  modified before loading it, e.g. -X switches

   procedure Abort_Msg (Config    : Command_Line_Configuration;
                        Msg       : String;
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
   --  assume that there is no body).

   procedure Print_Errors (S : String);
   --  The String in argument is an error message from gnatcoll. Print it on
   --  stderr with a prefix.

   procedure Produce_Version_Output;
   --  Print the version of gnatprove, why3 and shipped provers

   procedure Produce_List_Categories_Output;
   --  List information for all messages issued by the tool

   procedure Set_CodePeer_Mode
     (Config : Command_Line_Configuration;
      Input  : String);
   --  Parse the --codepeer option (possibilities are "on" and "off")

   procedure Check_gnateT_Switch;
   --  Do the actual check and issue warning for the check mentioned in
   --  Set_Target_Dir: if -gnateT is not set in
   --  Builder.Global_Configuration_Switches.

   function Is_Coq_Prover return Boolean;
   --  @return True iff one alternate prover is "coq"

   --  Hidden switches: --ide-progress-bar

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

   procedure Check_gnateT_Switch is
   begin
      if Prj_Attr.Target.all /= ""
        or else CL_Switches.Target.all /= ""
      then

         --  We check the conditions for *not* issuing the warning, in which
         --  case we return. At the end of the procedure, the warning is issued
         --  unconditionally.

         if Prj_Attr.Builder.Global_Compilation_Switches_Ada /= null then
            for Arg of Prj_Attr.Builder.Global_Compilation_Switches_Ada.all
            loop
               if GNATCOLL.Utils.Starts_With (Arg.all, "-gnateT=") then
                  return;
               end if;
            end loop;
         end if;
         Put_Line
           (Standard_Error,
            "warning: attribute ""Target"" of your project file is " &
              "only used to determine runtime library");
         Put_Line
           (Standard_Error,
            "warning: to specify target properties, specify option " &
              """-gnateT"" using ""Builder.Global_Compilation_Switches""");
      end if;
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
            pragma Assert (Name_Dir = Name_GNATprove);
            if GNAT.OS_Lib.Is_Directory (Rm_Dir) then
               if CL_Switches.V then
                  Ada.Text_IO.Put
                    ("Deleting directory " & Rm_Dir & "...");
               end if;
               GNAT.Directory_Operations.Remove_Dir (Rm_Dir, True);
               if CL_Switches.V then
                  Ada.Text_IO.Put_Line (" done");
               end if;
            end if;
         end if;
      exception
         when GNAT.Directory_Operations.Directory_Error =>
            if CL_Switches.V then
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
      Section   : String) is
   begin
      if Section = "cargs" then
         CL_Switches.Cargs_List.Append (Switch & Separator & Parameter);

      elsif Switch (Switch'First) /= '-' then

         --  We assume that the "switch" is actually an argument and put it in
         --  the file list

         CL_Switches.File_List.Append (Switch);

      --  Switches related to project loading like -X and -aP make no sense to
      --  be specified *in* the project file. It's not easy to check, because
      --  it would require parsing the Switches attribute in the project file
      --  separately. Instead, we check that every -X or -aP switch found here
      --  has already been parsed in the first pass.

      elsif Switch'Length >= 2
        and then Switch (Switch'First + 1) = 'X'
      then
         if not CL_Switches.X.Contains (Switch) then
            Put_Line
              (Standard_Error,
               "warning: switch " & Switch & " specified in the project file" &
                 " will be ignored. It needs to be specified on the command " &
                 "line directly.");
         end if;
      elsif Switch = "-aP" then
         if not CL_Switches.GPR_Project_Path.Contains (Parameter) then
            Put_Line
              (Standard_Error,
               "warning: switch " & Switch & " specified in the project file" &
                 " will be ignored. It needs to be specified on the command " &
                 "line directly.");
         end if;
      else
         raise Invalid_Switch;
      end if;
   end Handle_Switch;

   ----------------------
   -- Is_Manual_Prover --
   ----------------------

   function Is_Manual_Prover return Boolean is
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
   begin
      return Case_Insensitive_Contains (Provers, "coq");
   end Is_Coq_Prover;

   ------------------------
   -- Prepare_Prover_Lib --
   ------------------------

   procedure Prepare_Prover_Lib (Config : Command_Line_Configuration) is

      Prover_Name : constant String :=
        Ada.Characters.Handling.To_Lower (Provers.First_Element);
      Prover_Lib_Dir : constant String :=
        Compose
          (Compose (File_System.Install.Share_Why3, "libs"),
           Name => Prover_Name);
      Prover_Obj_Dir : constant String := Compose
        (Compose (Main_Subdir.all, "why3_libs"), Name => Prover_Name);

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
                                  Source_Dest,
                                With_Help => False);
                  end if;

                  GNAT.OS_Lib.Free (Coqc_Bin);

                  for It in Args'Range loop
                     Free (Args (It));
                  end loop;
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
      Compile_Lib ("set", "Set");
      Compile_Lib ("map", "Map");
      Compile_Lib ("map", "Const");
      Compile_Lib ("map", "Occ");
      Compile_Lib ("map", "MapPermut");
      Compile_Lib ("map", "MapInjection");
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
      Compile_Lib ("seq", "Seq");
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
      Ada.Text_IO.Put_Line ("[Flow analysis categories]");
      for K in Valid_Flow_Tag_Kind loop
         Ada.Text_IO.Put_Line (Rule_Name (K) & " - " & Kind_Name (K) & " - " &
                                 Description (K));
      end loop;
      Ada.Text_IO.Put_Line ("[Proof categories]");
      for K in VC_Kind loop
         if K not in VC_Warning_Kind then
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
        Compose (File_System.Install.Libexec_Spark_Bin, "gnatwhy3");
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

   function Prover_List return String is
      use Ada.Strings.Unbounded;
      use String_Lists;

      Buf : Unbounded_String := Null_Unbounded_String;
      C : Cursor := First (Provers);
   begin
      loop
         Append (Buf, Element (C));
         Next (C);
         exit when not Has_Element (C);
         Append (Buf, ',');
      end loop;
      return To_String (Buf);
   end Prover_List;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line (Tree : out Project_Tree) is
      Config : Command_Line_Configuration;

      function Init return Project_Tree;
      --  Load the project file; This function requires the project file to be
      --  present.

      procedure Postprocess;
      --  read the switch variables set by CL parsing and set the gnatprove
      --  variables

      procedure Set_Project_Vars;
      --  set the variables of the Prj_Attr package

      procedure Set_Mode;
      procedure Set_Warning_Mode;
      procedure Set_Report_Mode;

      procedure Set_Level_Timeout_Steps_Provers;
      --  using the --level, --timeout, --steps and --provers switches, set the
      --  corresponding variables

      procedure Set_Proof_Mode;
      procedure Process_Limit_Switches;
      procedure Set_Provers;
      procedure Set_Proof_Dir;
      --  If attribute Proof_Dir is set in the project file,
      --  set global variable Proof_Dir to the full path
      --  <path-to-project-file>/<value-of-proof-dir>.

      procedure Limit_Provers;
      --  This subprogram is here for SPARK Discovery. It removes cvc4/z3 from
      --  the provers list, if not found on the PATH. If that makes the list of
      --  provers become empty, alt-ergo is added as prover, so that we have at
      --  least one prover.

      procedure Sanity_Checking;
      --  Check the command line flags for conflicting flags

      function Read_Help_Message return String;
      --  Returns contents of the static help message file

      ----------
      -- Init --
      ----------

      function Init return Project_Tree is
         GNAT_Version : GNAT.Strings.String_Access;
         Tree         : Project_Tree;

      begin
         if not Null_Or_Empty_String (CL_Switches.Subdirs) then
            Subdir := Filesystem_String (CL_Switches.Subdirs.all) / Subdir;
         end if;

         Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
         Free (GNAT_Version);
         Set_Object_Subdir (Proj_Env.all,
                            Filesystem_String (Subdir.Display_Full_Name));
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
            Abort_Msg (Config, "No project file is given", With_Help => False);
         end if;
         return Tree;
      end Init;

      -------------------
      -- Limit_Provers --
      -------------------

      procedure Limit_Provers is

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
         if not File_System.Install.CVC4_Present then
            Remove_Prover ("cvc4");
         end if;
         if not File_System.Install.Z3_Present then
            Remove_Prover ("z3");
         end if;

         if not Is_Empty_At_Start and Provers.Is_Empty then
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

         File_System.Install.Z3_Present   := On_Path ("z3");
         File_System.Install.CVC4_Present := On_Path ("cvc4");

         Verbose           := CL_Switches.V;
         Force             := CL_Switches.F;
         Debug             := CL_Switches.D or CL_Switches.Flow_Debug;
         Quiet             := CL_Switches.Q;
         Minimal_Compile   := CL_Switches.M;
         Flow_Extra_Debug  := CL_Switches.Flow_Debug;
         Flow_Termination  := CL_Switches.Flow_Termination;
         Flow_Show_GG      := CL_Switches.Flow_Show_GG;
         Continue_On_Error := CL_Switches.K;
         All_Projects      := CL_Switches.UU;
         IDE_Mode          := CL_Switches.IDE_Progress_Bar;
         Limit_Line        := CL_Switches.Limit_Line;
         Limit_Region      := CL_Switches.Limit_Region;
         Limit_Subp        := CL_Switches.Limit_Subp;
         Memcached_Server  := CL_Switches.Memcached_Server;
         Why3_Config_File  := CL_Switches.Why3_Conf;
         No_Axiom_Guard    := CL_Switches.No_Axiom_Guard;
         CWE               := CL_Switches.CWE;

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

         No_Inlining          := CL_Switches.No_Inlining or
           CL_Switches.No_Global_Generation;
         No_Global_Generation := CL_Switches.No_Global_Generation;

         --  Adjust the number of parallel processes. If -j0 was used, the
         --  number of processes should be set to the actual number of
         --  processors available on the machine.

         if CL_Switches.J = 0 then
            Parallel := Natural (System.Multiprocessors.Number_Of_CPUs);
         elsif CL_Switches.J < 0 then
            Abort_Msg (Config,
                       "error: wrong argument for -j",
                       With_Help => False);
         else
            Parallel := CL_Switches.J;
         end if;

         --  handling of Only_Given and Filelist

         Only_Given := CL_Switches.U
           or not Null_Or_Empty_String (CL_Switches.Limit_Subp)
           or not Null_Or_Empty_String (CL_Switches.Limit_Line);

         Process_Limit_Switches;

         Set_CodePeer_Mode (Config, CL_Switches.CodePeer.all);
         Check_gnateT_Switch;
         Set_Mode;
         Set_Warning_Mode;
         Set_Report_Mode;
         Set_Level_Timeout_Steps_Provers;
         Set_Proof_Mode;
         Set_Proof_Dir;

         Counterexample :=
           not CL_Switches.No_Counterexample
           and then File_System.Install.CVC4_Present
           and then not Is_Manual_Prover
           and then not CL_Switches.Output_Msg_Only;
         Z3_Counterexample := CL_Switches.Z3_Counterexample;
         CodePeer := CodePeer and then Mode in GPM_Prove | GPM_All;
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

               if not Null_Or_Empty_String (Limit_Subp) then
                  Limit_String := Limit_Subp;
               end if;

               if not Null_Or_Empty_String (Limit_Region) then
                  Limit_String := Limit_Region;
               end if;

               if not Null_Or_Empty_String (Limit_Line) then
                  Limit_String := Limit_Line;
               end if;

               if Limit_String /= null then
                  declare
                     Colon_Index : constant Natural :=
                       Ada.Strings.Fixed.Index (Source  => Limit_String.all,
                                                Pattern => ":");

                  begin
                     if Colon_Index = 0 then
                        Abort_Msg
                          (Config,
                           "limit-line: incorrect line specification" &
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

      -----------------------
      -- Read_Help_Message --
      -----------------------

      function Read_Help_Message return String is
         File_Name : String renames File_System.Install.Help_Msg_File;
         File_Size : constant Natural :=
           Natural (Ada.Directories.Size (File_Name));

         subtype File_String    is String (1 .. File_Size);
         package File_String_IO is new Ada.Direct_IO (File_String);

         File     : File_String_IO.File_Type;
         Contents : File_String;
      begin
         File_String_IO.Open  (File, Mode => File_String_IO.In_File,
                               Name => File_Name);
         File_String_IO.Read  (File, Item => Contents);
         File_String_IO.Close (File);

         return Contents;
      end Read_Help_Message;

      ---------------------
      -- Sanity_Checking --
      ---------------------

      procedure Sanity_Checking is
      begin
         if (CL_Switches.Output_Msg_Only and CL_Switches.Replay)
           or else (CL_Switches.Output_Msg_Only and CL_Switches.F)
           or else (CL_Switches.F and CL_Switches.Output_Msg_Only)
         then
            Abort_Msg
              (Config,
               "only one switch out of -f, --output-msg-only and --replay" &
                 " should be provided to gnatprove",
               With_Help => False);
         end if;
      end Sanity_Checking;

      -------------------------------------
      -- Set_Level_Timeout_Steps_Provers --
      -------------------------------------

      procedure Set_Level_Timeout_Steps_Provers is
      begin

         case CL_Switches.Level is

            --  If level switch was not provided, set other switches to their
            --  default values.

            when Invalid_Level =>

               Provers.Append ("cvc4");
               Steps := Default_Steps;
               Timeout := 0;
               Memlimit := 0;

            --  See the UG for the meaning of the level switches

            when 0 =>
               Provers.Append ("cvc4");
               Steps := 0;
               Timeout := 1;
               Memlimit := 1000;

            when 1 =>
               Provers.Append ("cvc4");
               Provers.Append ("z3");
               Provers.Append ("altergo");
               Steps := 0;
               Timeout := 1;
               Memlimit := 1000;

            when 2 =>
               Provers.Append ("cvc4");
               Provers.Append ("z3");
               Provers.Append ("altergo");
               Steps := 0;
               Timeout := 5;
               Memlimit := 1000;

            when 3 =>
               Provers.Append ("cvc4");
               Provers.Append ("z3");
               Provers.Append ("altergo");
               Steps := 0;
               Timeout := 20;
               Memlimit := 2000;

            when 4 =>
               Provers.Append ("cvc4");
               Provers.Append ("z3");
               Provers.Append ("altergo");
               Steps := 0;
               Timeout := 60;
               Memlimit := 2000;

            when others =>
               Abort_Msg (Config,
                          "error: wrong argument for --level",
                          With_Help => False);

               raise Program_Error;
         end case;

         --  If option --timeout was not provided, keep timeout corresponding
         --  to level switch/default value. Otherwise, take the user-provided
         --  timeout.

         if CL_Switches.Timeout.all = "" then
            null;
         else
            begin
               Timeout := Integer'Value (CL_Switches.Timeout.all);
               if Timeout < 0 then
                  raise Constraint_Error;
               end if;
            exception
               when Constraint_Error =>
                  Abort_Msg (Config,
                             "error: wrong argument for --timeout, " &
                               "must be auto or a non-negative integer",
                             With_Help => False);
            end;
         end if;

         if CL_Switches.Memlimit = 0 then
            null;
         else
            Memlimit := CL_Switches.Memlimit;
         end if;

         if CL_Switches.Steps = Invalid_Steps then
            null;
         elsif CL_Switches.Steps < 0 then
            Abort_Msg (Config,
                       "error: wrong argument for --steps",
                       With_Help => False);
         else
            Steps := CL_Switches.Steps;
         end if;

         --  Timeout is fully set now, we can set CE_Timeout. Basically we cap
         --  the CE_Timeout at Constants.Max_CE_Timeout seconds.

         CE_Timeout :=
           (if Timeout = 0 then Constants.Max_CE_Timeout
            else Integer'Min (Timeout, Constants.Max_CE_Timeout));

         Set_Provers;
         Limit_Provers;

         if CL_Switches.Output_Msg_Only then
            Provers.Clear;
         end if;
      end Set_Level_Timeout_Steps_Provers;

      --------------
      -- Set_Mode --
      --------------

      procedure Set_Mode is
      begin
         Mode := GPM_All;
         if CL_Switches.Mode.all = "" then
            null;
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
            Abort_Msg (Config,
                       "error: wrong argument for --mode",
                       With_Help => False);
         end if;
      end Set_Mode;

      ----------------------
      -- Set_Project_Vars --
      ----------------------

      procedure Set_Project_Vars is
         Glob_Comp_Switch_Attr : constant Attribute_Pkg_List :=
           Build ("Builder", "Global_Compilation_Switches");
         Proof_Dir_Attr : constant Attribute_Pkg_String :=
           Build ("Prove", "Proof_Dir");
      begin
         Prj_Attr.Target := new String'(Tree.Root_Project.Get_Target);
         Prj_Attr.Runtime := new String'(Tree.Root_Project.Get_Runtime);
         Prj_Attr.Builder.Global_Compilation_Switches_Ada :=
           (if Has_Attribute (Tree.Root_Project, Glob_Comp_Switch_Attr, "Ada")
            then Attribute_Value (Tree.Root_Project,
                                  Glob_Comp_Switch_Attr, "Ada")
            else null);
         Prj_Attr.Prove.Proof_Dir :=
           (if Has_Attribute (Tree.Root_Project, Proof_Dir_Attr)
            then new String'(Attribute_Value (Tree.Root_Project,
                                              Proof_Dir_Attr))
            else null);
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

      procedure Set_Proof_Mode is
         Input : String renames CL_Switches.Proof.all;
         Colon_Index : constant Natural :=
           Index (Source => Input, Pattern => ":");

      begin
         Lazy := True;

         declare
            Proof_Input : constant String :=
              (if Colon_Index /= 0 then Input (Input'First .. Colon_Index - 1)
               else Input);
            Lazy_Input : constant String :=
              (if Colon_Index /= 0 then Input (Colon_Index + 1 .. Input'Last)
               else "");
         begin
            if Proof_Input = "" then
               Proof := Per_Check;
            elsif Proof_Input = "progressive" then
               Proof := Progressive;
            elsif Proof_Input = "per_path" then
               Proof := Per_Path;
            elsif Proof_Input = "per_check" then
               Proof := Per_Check;

               --  Hidden debugging values

            elsif Proof_Input = "no_wp" then
               Proof := No_WP;
            elsif Proof_Input = "all_split" then
               Proof := All_Split;
            else
               Abort_Msg (Config,
                          "error: wrong argument for --proof",
                          With_Help => False);
            end if;

            if Lazy_Input = "" then
               null;
            elsif Lazy_Input = "all" then
               Lazy := False;
            elsif Lazy_Input = "lazy" then
               Lazy := True;
            else
               Abort_Msg (Config,
                          "error: wrong argument for --proof",
                          With_Help => False);
            end if;
         end;
      end Set_Proof_Mode;

      -----------------
      -- Set_Provers --
      -----------------

      procedure Set_Provers is
         First : Integer;
         S : constant String :=
           (if CL_Switches.Prover /= null then CL_Switches.Prover.all else "");

      begin
         --  This procedure is called when the Provers list is already filled
         --  with the defaults from the --level switch.
         --  In replay mode, we only want to take into account provers when
         --  they were explicitly set, not when set by default. When not
         --  in replay mode, we only need to change the Provers list when
         --  --provers was explicitly set.

         if S = "" then
            if CL_Switches.Replay then
               Provers.Clear;
            end if;
            return;
         end if;
         Provers.Clear;
         First := S'First;
         for Cur in S'Range loop
            if S (Cur) = ',' then
               Provers.Append (S (First .. Cur - 1));
               First := Cur + 1;
            end if;
         end loop;
         if S /= "" then
            Provers.Append (S (First .. S'Last));
         end if;

         --  we now check if cvc4 or z3 have explicitly been requested, but are
         --  missing from the install

         for Prover of Provers loop
            if (Prover = "cvc4" and then not File_System.Install.CVC4_Present)
              or else
                (Prover = "z3" and then not File_System.Install.Z3_Present)
            then
               Abort_Msg (Config,
                          "error: prover " & Prover &
                            " was selected, but it is not installed",
                          With_Help => False);
            end if;
         end loop;
      end Set_Provers;

      ---------------------
      -- Set_Report_Mode --
      ---------------------

      procedure Set_Report_Mode is
      begin
         Report := GPR_Fail;
         if CL_Switches.Report.all = "" then
            null;
         elsif CL_Switches.Report.all = "fail" then
            Report := GPR_Fail;
         elsif CL_Switches.Report.all = "all" then
            Report := GPR_All;
         elsif CL_Switches.Report.all = "provers" then
            Report := GPR_Provers;
         elsif CL_Switches.Report.all = "statistics" then
            Report := GPR_Statistics;
         else
            Abort_Msg (Config,
                       "error: wrong argument for --report",
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
            Warning_Mode := Gnat2Why_Args.SW_Normal;
         elsif Warn_Switch = "off" then
            Warning_Mode := Gnat2Why_Args.SW_Suppress;
         elsif Warn_Switch = "error" then
            Warning_Mode := Gnat2Why_Args.SW_Treat_As_Error;
         elsif Warn_Switch = "on"
           or else Warn_Switch = "continue"
         then
            Warning_Mode := Gnat2Why_Args.SW_Normal;
         else

            Abort_Msg (Config,
                       "error: wrong argument for --warnings",
                       With_Help => False);
         end if;
      end Set_Warning_Mode;

      --  Local variables

      First_Config : Command_Line_Configuration;

      Com_Lin : String_List :=
        (1 .. Ada.Command_Line.Argument_Count => <>);

      Usage_Message : constant String :=
        "-Pproj [switches] [-cargs switches]";

      Help_Message : constant String := Read_Help_Message;
      --  Help message read from a static file

      use CL_Switches;

   --  Start of processing for Read_Command_Line

   begin
      --  Call Set_Usage for both command line configurations

      Set_Usage
        (First_Config,
         Usage    => Usage_Message,
         Help_Msg => Help_Message);

      Set_Usage
        (Config,
         Usage    => Usage_Message,
         Help_Msg => Help_Message);

      --  If no arguments have been given, print help message and exit

      if Com_Lin'Length = 0 then
         Abort_Msg (Config, "", With_Help => True);
      end if;

      --  We parse the command line *twice*. The reason is that before parsing
      --  the command line, we need to load the project (e.g. because the
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
        (First_Config,
         CL_Switches.P'Access,
         "-P:");

      Define_Switch
        (First_Config,
         Version'Access,
         Long_Switch => "--version");

      Define_Switch
        (First_Config,
         List_Categories'Access,
         Long_Switch => "--list-categories");

      Define_Switch
        (First_Config,
         CL_Switches.V'Access,
         "-v",
         Long_Switch => "--verbose");

      Define_Switch
         (First_Config,
          Clean'Access,
          Long_Switch => "--clean");

      Define_Switch (First_Config, "-aP=");

      Define_Switch
        (First_Config,
         CL_Switches.Subdirs'Access,
         Long_Switch => "--subdirs=");

      Define_Switch (First_Config, "*", Help => "list of source files");

      --  We now initialize the project environment; it may be changed by the
      --  first parse of the command line.

      Initialize (Proj_Env);

      Getopt (First_Config,
              Callback    => Handle_Project_Loading_Switches'Access,
              Concatenate => False);

      Free (First_Config);

      if Version then
         Produce_Version_Output;
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      if List_Categories then
         Produce_List_Categories_Output;
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      --  The second parsing needs the info for all switches, including the
      --  ones that are only used by the first pass (e.g. -aP), so that they
      --  can be properly ignored. An exception is the option -X, which is
      --  explicitly ignored by the callback Handle_Switch

      Define_Switch (Config, "-aP=");

      Define_Switch
        (Config,
         CL_Switches.Checks_As_Errors'Access,
         Long_Switch => "--checks-as-errors");

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
          CL_Switches.Dbg_Proof_Only'Access,
          Long_Switch => "--dbg-proof-only");

      Define_Switch
        (Config, CL_Switches.P'Access,
         "-P:");

      Define_Switch
        (Config,
         CL_Switches.F'Access,
         "-f");

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
         CL_Switches.Mode'Access,
         Long_Switch => "--mode=");

      Define_Switch
        (Config,
         CL_Switches.M'Access,
         "-m");

      Define_Switch
        (Config,
         CL_Switches.Warnings'Access,
         Long_Switch => "--warnings=");

      Define_Switch
        (Config,
         CL_Switches.Proof'Access,
         Long_Switch => "--proof=");

      Define_Switch
        (Config,
         CL_Switches.CodePeer'Access,
         Long_Switch => "--codepeer=");

      Define_Switch
        (Config,
         CL_Switches.Coverage'Access,
         Long_Switch => "--coverage");

      Define_Switch
        (Config,
         CL_Switches.Debug_Save_VCs'Access,
         Long_Switch => "--debug-save-vcs");

      Define_Switch
        (Config,
         CL_Switches.Pedantic'Access,
         Long_Switch => "--pedantic");

      Define_Switch
        (Config,
         CL_Switches.Replay'Access,
         Long_Switch => "--replay");

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
         CL_Switches.Target'Access,
         Long_Switch => "--target=");

      Define_Switch
        (Config,
         CL_Switches.IDE_Progress_Bar'Access,
         Long_Switch => "--ide-progress-bar");

      Define_Switch
         (Config,
          CL_Switches.Q'Access,
          "-q", Long_Switch => "--quiet");

      Define_Switch
        (Config,
         CL_Switches.Report'Access,
         Long_Switch => "--report=");

      --  If not specified on the command-line, value of steps is invalid
      Define_Switch
         (Config, CL_Switches.Steps'Access,
          Long_Switch => "--steps=",
          Initial => Invalid_Steps);

      Define_Switch
         (Config, CL_Switches.Level'Access,
          Long_Switch => "--level=",
          Initial => Invalid_Level);

      Define_Switch
         (Config,
          CL_Switches.Timeout'Access,
          Long_Switch => "--timeout=");

      Define_Switch
        (Config,
         CL_Switches.Memlimit'Access,
         Long_Switch => "--memlimit=");

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
         CL_Switches.V'Access,
         "-v", Long_Switch => "--verbose");

      Define_Switch
        (Config,
         CL_Switches.Assumptions'Access,
         Long_Switch => "--assumptions");

      Define_Switch
        (Config,
         CL_Switches.Limit_Region'Access,
         Long_Switch => "--limit-region=");

      Define_Switch
        (Config,
         CL_Switches.Limit_Line'Access,
         Long_Switch => "--limit-line=");

      Define_Switch (Config, "*");

      Define_Switch
        (Config,
         CL_Switches.Limit_Subp'Access,
         Long_Switch => "--limit-subp=");

      Define_Switch
        (Config,
         CL_Switches.Prover'Access,
         Long_Switch => "--prover=");

      Define_Switch
        (Config,
         CL_Switches.No_Axiom_Guard'Access,
         Long_Switch => "--no-axiom-guard");

      Define_Switch
        (Config,
         CL_Switches.Proof_Warnings'Access,
         Long_Switch => "--proof-warnings");

      Define_Switch
        (Config,
         CL_Switches.No_Counterexample'Access,
         Long_Switch => "--no-counterexample");

      Define_Switch
        (Config,
         CL_Switches.Z3_Counterexample'Access,
         Long_Switch => "--z3-counterexample");

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
         CL_Switches.No_Global_Generation'Access,
         Long_Switch => "--no-global-generation");

      Define_Switch
        (Config,
         CL_Switches.No_Subprojects'Access,
         Long_Switch => "--no-subprojects");

      Define_Switch
        (Config,
         CL_Switches.Output_Header'Access,
         Long_Switch => "--output-header");

      Define_Switch
        (Config,
         CL_Switches.Output_Msg_Only'Access,
         Long_Switch => "--output-msg-only");

      Define_Switch
        (Config, CL_Switches.Why3_Conf'Access,
         Long_Switch => "--why3-conf=");

      --  This switch is not documented on purpose. We provide the fake_*
      --  binaries instead of the real prover binaries. This helps when
      --  collecting benchmarks for prover developers.
      Define_Switch
         (Config, CL_Switches.Benchmark'Access,
          Long_Switch => "--benchmark");

      Define_Switch
         (Config, CL_Switches.Memcached_Server'Access,
          Long_Switch => "--memcached-server=");

      Define_Switch
         (Config,
          CL_Switches.Info'Access,
          Long_Switch => "--info");

      Define_Section (Config, "cargs");
      Define_Switch (Config, "*", Section => "cargs");

      --  Before doing the actual second parsing, we read the project file in

      Tree := Init;

      if Clean then
         Clean_Up (Tree);
         GNAT.OS_Lib.OS_Exit (0);
      end if;

      declare
         use Ada.Strings.Unbounded;

         Proj_Type      : constant Project_Type := Root_Project (Tree);
         Extra_Switches : constant String_List_Access :=
           Attribute_Value (Proj_Type, Build ("Prove", "Switches"));

      begin
         if Extra_Switches /= null then
            declare
               All_Switches        : constant String_List :=
                 Extra_Switches.all & Com_Lin;
               All_Access          : constant String_List_Access :=
                 new String_List'(All_Switches);
               Parser              : Opt_Parser;
               Extra_Switches_Line : Unbounded_String;

            begin
               Initialize_Option_Scan (Parser, All_Access);
               Getopt (Config,
                       Callback => Handle_Switch'Access,
                       Parser   => Parser,
                       Concatenate => False);

               --  Add GNATprove switches in environment for printing in header
               --  of generated file "gnatprove.out"
               for J in Extra_Switches'Range loop
                  if J /= Extra_Switches'First then
                     Append (Extra_Switches_Line, " ");
                  end if;
                  Append (Extra_Switches_Line, Extra_Switches (J).all);
               end loop;

               if CL_Switches.V then
                  Put_Line ("export GNATPROVE_SWITCHES="
                            & To_String (Extra_Switches_Line));
               end if;

               Ada.Environment_Variables.Set
                 ("GNATPROVE_SWITCHES", To_String (Extra_Switches_Line));
            end;
         else
            Getopt (Config,
                    Callback => Handle_Switch'Access,
                    Concatenate => False);
         end if;

         --  Release copies of command line arguments; they were already parsed
         --  twice and are no longer needed.
         Free (Com_Lin);

         --  After the call to Init, the object directory includes the
         --  sub-directory "gnatprove" set through Set_Object_Subdir.
         Main_Subdir := new String'(Proj_Type.Artifacts_Dir.Display_Full_Name);

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
         end;
      end;

      Set_Project_Vars;
      Postprocess;

      if Is_Coq_Prover then
         Prepare_Prover_Lib (Config);
      end if;
      Sanitize_File_List (Tree);

      Free (Config);

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
      for Cursor in CL_Switches.File_List.Iterate loop
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
                       Create_From_Base (Ptype.File_From_Unit
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

   procedure Set_CodePeer_Mode
     (Config : Command_Line_Configuration;
      Input  : String) is
   begin
      CodePeer := False;
      if Input = "" then
         null;
      elsif Input = "on" then
         CodePeer := True;
      elsif Input = "off" then
         CodePeer := False;
      else
         Abort_Msg (Config,
                    "error: wrong argument for --codepeer, " &
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

end Configuration;
