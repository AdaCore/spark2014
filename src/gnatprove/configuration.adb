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
with Ada.Containers;    use Ada.Containers;
with Ada.IO_Exceptions;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;
with Ada.Unchecked_Deallocation;
with GNATCOLL.Tribooleans;
with Gnat2Why_Opts.Writing;
with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Directory_Operations;
with GNAT.Expect;
with GNAT.OS_Lib;
with GNAT.Regpat;       use GNAT.Regpat;
with GNAT.Strings;      use GNAT.Strings;
with GPR2.Build.Compilation_Unit;
with GPR2.Build.Compilation_Unit.Maps;
with GPR2.Build.Source;
with GPR2.Build.View_Db;
with GPR2.Log;
with GPR2.Message;
with GPR2.Options;
with GPR2.Path_Name;
with GPR2.Project.Attribute;
with GPR2.Project.Attribute_Index;
with GPR2.Project.Registry.Attribute;
with GPR2.Project.Registry.Attribute.Description;
with GPR2.Project.Registry.Exchange;
with GPR2.Project.Registry.Pack;
with GPR2.Project.Registry.Pack.Description;
with GPR2.Reporter.Console;

with Platform;     use Platform;
with SPARK2014VSN; use SPARK2014VSN;
with System.Multiprocessors;

package body Configuration is

   Invalid_Level   : constant := -1;
   Invalid_Steps   : constant := -1;
   Invalid_Timeout : constant := -1;

   Usage_Message : constant String := "-Pproj [switches] [-cargs switches]";
   --  Used to print part of the help message for gnatprove

   Clean : aliased Boolean;
   --  Set to True when --clean was given. Triggers cleanup of GNATprove
   --  intermediate files.

   Proj_Opt : Options.Object;
   --  This is the project environment used to load the project. It may be
   --  modified before loading it, e.g. -X switches

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

   procedure Handle_Project_Loading_Switches
     (Switch : String; Parameter : String; Section : String);
   --  Command line handler which deals with -X switches and -aP switches

   procedure Handle_Switch
     (Switch : String; Parameter : String; Section : String);
   --  Deal with all switches that are not automatic. In gnatprove, all
   --  recognized switches are automatic, so this procedure should only be
   --  called for unknown switches and for switches in section -cargs.

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

   procedure Produce_Version_Output;
   --  Print the version of gnatprove, why3 and shipped provers

   procedure Produce_List_Categories_Output;
   --  List information for all messages issued by the tool

   procedure Produce_Explain_Output;
   --  Print the explanation for the requested error/warning code

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

   function Artifact_Dir (Tree : GPR2.Project.Tree.Object) return Virtual_File
   is
   begin
      if Tree.Root_Project.Kind in GPR2.With_Object_Dir_Kind then
         --  we don't need to add "gnatprove" here as we configured the project
         --  with the correct subdir option.
         return Tree.Root_Project.Object_Directory.Virtual_File;
      else
         return Tree.Root_Project.Dir_Name.Virtual_File / "gnatprove";
      end if;
   end Artifact_Dir;

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
               if Verbose then
                  Ada.Text_IO.Put ("Deleting directory " & Rm_Dir & "...");
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

      --  Start of processing for Clean_Up

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

      --  Start of processing for Compute_Socket_Dir

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
         return Artifact_Dir (Tree).Display_Full_Name;
      end if;
   end Compute_Socket_Dir;

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

   -------------------------------------
   -- Handle_Project_Loading_Switches --
   -------------------------------------

   procedure Handle_Project_Loading_Switches
     (Switch : String; Parameter : String; Section : String)
   is
      pragma Unreferenced (Section);
   begin
      if Switch'Length > 2 and then Switch (Switch'First + 1) = 'X' then

         --  When a -X switch was found, we need to:
         --  * add the scenario variable to the environment that we use to load
         --    the project;
         --  * store the switch to add it to calls to gprbuild that we do later

         --  First we add the variable to the environment.

         Proj_Opt.Add_Switch
           (Options.X, Switch (Switch'First + 2 .. Switch'Last));

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
     (Switch : String; Parameter : String; Section : String)
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

      elsif Switch'Length >= 2 and then Switch (Switch'First + 1) = 'X' then
         null;
      elsif Switch = "-aP" then
         null;
      else
         raise Invalid_Switch;
      end if;
   end Handle_Switch;

   ---------------------
   -- Handle_W_Switch --
   ---------------------

   procedure Handle_Warning_Switches (Switch, Value : String) is
      Tag    : Misc_Warning_Kind;
      Status : Warning_Enabled_Status;
   begin

      --  Handling of pedantic and info

      if Switch = "--pedantic" then
         for WK in Pedantic_Warning_Kind loop
            Configuration.Warning_Status (WK) := VC_Kinds.WS_Enabled;
         end loop;
         return;
      end if;
      if Switch = "--info" then
         for WK in Info_Warning_Kind loop
            Configuration.Warning_Status (WK) := VC_Kinds.WS_Enabled;
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
            Configuration.Warning_Status (WK) := Status;
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

      Configuration.Warning_Status (Tag) := Status;
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

      --  Start of processing for No_Project_File_Mode

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
   -- Parse_Switches --
   --------------------

   procedure Parse_Switches (Mode : Parsing_Modes; Com_Lin : String_List) is

      procedure Free_Topmost is new
        Ada.Unchecked_Deallocation
          (Object => String_List,
           Name   => String_List_Access);

      Config         : Command_Line_Configuration;
      Parser         : Opt_Parser;
      Com_Lin_Access : String_List_Access := new String_List'(Com_Lin);

      use CL_Switches;

   begin
      Initialize_Option_Scan (Parser, Com_Lin_Access);
      Set_Usage
        (Config,
         Usage    => Usage_Message,
         Help_Msg => SPARK_Install.Help_Message);

      if Mode in Project_Parsing | All_Switches then
         Define_Switch (Config, "-aP=");
         Define_Switch (Config, Clean'Access, Long_Switch => "--clean");
         Define_Switch
           (Config,
            List_Categories'Access,
            Long_Switch => "--list-categories");
         Define_Switch (Config, CL_Switches.P'Access, "-P:");
         Define_Switch
           (Config, CL_Switches.Target'Access, Long_Switch => "--target=");
         Define_Switch
           (Config, CL_Switches.RTS'Access, Long_Switch => "--RTS=");
         Define_Switch
           (Config, CL_Switches.Subdirs'Access, Long_Switch => "--subdirs=");
         Define_Switch (Config, Version'Access, Long_Switch => "--version");
         Define_Switch (Config, Explain'Access, Long_Switch => "--explain=");
         Define_Switch
           (Config,
            CL_Switches.Print_Gpr_Registry'Access,
            Long_Switch => GPR2.Options.Print_GPR_Registry_Option);
         Define_Switch
           (Config, CL_Switches.Config'Access, Long_Switch => "--config=");
         Define_Switch
           (Config, CL_Switches.Autoconf'Access, Long_Switch => "--autoconf=");
      end if;

      if Mode in Project_Parsing | All_Switches | Global_Switches_Only then
         Define_Switch
           (Config, CL_Switches.V'Access, "-v", Long_Switch => "--verbose");
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
           (Config,
            CL_Switches.Benchmark'Access,
            Long_Switch => "--benchmark");
         Define_Switch
           (Config,
            CL_Switches.Checks_As_Errors'Access,
            Long_Switch => "--checks-as-errors=");
         Define_Switch
           (Config, CL_Switches.CWE'Access, Long_Switch => "--cwe");
         Define_Switch
           (Config, CL_Switches.D'Access, "-d", Long_Switch => "--debug");
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
            CL_Switches.Debug_Prover_Errors'Access,
            Long_Switch => "--debug-prover-errors");
         Define_Switch
           (Config,
            CL_Switches.Exclude_Line'Access,
            Long_Switch => "--exclude-line=");
         Define_Switch
           (Config,
            CL_Switches.Flow_Debug'Access,
            Long_Switch => "--flow-debug");
         Define_Switch
           (Config,
            CL_Switches.Flow_Show_GG'Access,
            Long_Switch => "--flow-show-gg");
         Define_Switch (Config, CL_Switches.F'Access, "-f");
         Define_Switch
           (Config,
            CL_Switches.IDE_Progress_Bar'Access,
            Long_Switch => "--ide-progress-bar");
         Define_Switch
           (Config, CL_Switches.J'Access, Long_Switch => "-j:", Initial => 1);
         Define_Switch (Config, CL_Switches.K'Access, "-k");
         Define_Switch
           (Config,
            CL_Switches.Limit_Line'Access,
            Long_Switch => "--limit-line=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Lines'Access,
            Long_Switch => "--limit-lines=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Name'Access,
            Long_Switch => "--limit-name=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Region'Access,
            Long_Switch => "--limit-region=");
         Define_Switch
           (Config,
            CL_Switches.Limit_Subp'Access,
            Long_Switch => "--limit-subp=");
         Define_Switch
           (Config,
            CL_Switches.Memcached_Server'Access,
            Long_Switch => "--memcached-server=");
         Define_Switch (Config, CL_Switches.M'Access, "-m");
         Define_Switch
           (Config,
            CL_Switches.No_Axiom_Guard'Access,
            Long_Switch => "--no-axiom-guard");
         Define_Switch
           (Config,
            CL_Switches.Function_Sandboxing'Access,
            Long_Switch => "--function-sandboxing=");
         Define_Switch
           (Config,
            CL_Switches.No_Global_Generation'Access,
            Long_Switch => "--no-global-generation");
         Define_Switch
           (Config,
            CL_Switches.No_Subprojects'Access,
            Long_Switch => "--no-subprojects");
         Define_Switch
           (Config, CL_Switches.Output'Access, Long_Switch => "--output=");
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
            CL_Switches.Proof_Warnings'Access,
            Long_Switch => "--proof-warnings=");
         Define_Switch
           (Config, CL_Switches.Q'Access, "-q", Long_Switch => "--quiet");
         Define_Switch
           (Config, CL_Switches.Replay'Access, Long_Switch => "--replay");
         Define_Switch
           (Config, CL_Switches.Report'Access, Long_Switch => "--report=");
         Define_Switch
           (Config, CL_Switches.Subdirs'Access, Long_Switch => "--subdirs=");
         Define_Switch (Config, CL_Switches.U'Access, "-u");
         Define_Switch (Config, CL_Switches.UU'Access, "-U");
         Define_Switch
           (Config, CL_Switches.Warnings'Access, Long_Switch => "--warnings=");
         Define_Switch
           (Config,
            CL_Switches.Why3_Conf'Access,
            Long_Switch => "--why3-conf=");
         Define_Switch
           (Config,
            CL_Switches.Why3_Debug'Access,
            Long_Switch => "--why3-debug=");
         Define_Switch
           (Config,
            CL_Switches.Why3_Logging'Access,
            Long_Switch => "--why3-logging");
         Define_Switch
           (Config,
            CL_Switches.Why3_Server'Access,
            Long_Switch => "--why3-server=");
         Define_Switch
           (Config,
            CL_Switches.Z3_Counterexample'Access,
            Long_Switch => "--z3-counterexample");
         Define_Section (Config, "cargs");
         Define_Switch (Config, "*", Section => "cargs");
      end if;

      if Mode in All_Switches | Global_Switches_Only | File_Specific_Only then
         Define_Switch
           (Config,
            CL_Switches.Level'Access,
            Long_Switch => "--level=",
            Initial     => Invalid_Level);
         Define_Switch
           (Config, CL_Switches.Memlimit'Access, Long_Switch => "--memlimit=");
         Define_Switch
           (Config,
            CL_Switches.Counterexamples'Access,
            Long_Switch => "--counterexamples=");
         Define_Switch
           (Config,
            CL_Switches.Check_Counterexamples'Access,
            Long_Switch => "--check-counterexamples=");
         Define_Switch
           (Config,
            CL_Switches.Gnattest_Values'Access,
            Long_Switch => "--gnattest-values=");
         Define_Switch
           (Config,
            CL_Switches.Debug_Exec_RAC'Access,
            Long_Switch => "--debug-exec-rac");
         Define_Switch
           (Config, Handle_Warning_Switches'Access, Long_Switch => "--info");
         Define_Switch
           (Config, CL_Switches.Mode'Access, Long_Switch => "--mode=");
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
            Handle_Warning_Switches'Access,
            Long_Switch => "--pedantic");
         Define_Switch
           (Config, CL_Switches.Proof'Access, Long_Switch => "--proof=");
         Define_Switch
           (Config, CL_Switches.Prover'Access, Long_Switch => "--prover=");
         Define_Switch (Config, Handle_Warning_Switches'Access, "-W=");
         Define_Switch (Config, Handle_Warning_Switches'Access, "-A=");
         Define_Switch (Config, Handle_Warning_Switches'Access, "-D=");

         --  If not specified on the command-line, value of steps is invalid
         Define_Switch
           (Config,
            CL_Switches.Steps'Access,
            Long_Switch => "--steps=",
            Initial     => Invalid_Steps);
         Define_Switch
           (Config,
            CL_Switches.CE_Steps'Access,
            Long_Switch => "--ce-steps=",
            Initial     => Invalid_Steps);
         Define_Switch
           (Config, CL_Switches.Timeout'Access, Long_Switch => "--timeout=");
         Define_Switch
           (Config,
            CL_Switches.Proof_Warn_Timeout'Access,
            Long_Switch => "--proof-warnings-timeout=",
            Initial     => Invalid_Timeout);
      end if;

      if Mode in All_Switches | Project_Parsing then
         Define_Switch (Config, "*", Help => "list of source files");
      end if;

      declare
         Callback : constant Switch_Handler :=
           (if Mode = Project_Parsing
            then Handle_Project_Loading_Switches'Access
            else Handle_Switch'Access);
      begin
         Getopt
           (Config,
            Callback    => Callback,
            Parser      => Parser,
            Concatenate => False);

      exception
         when Invalid_Switch =>
            Fail ("");
         when Exit_From_Command_Line =>
            Succeed;
         when Invalid_Parameter =>
            Abort_Msg
              ("No parameter given to switch -" & Full_Switch (Parser),
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
                  Coqc_Bin : String_Access :=
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

   procedure Produce_Explain_Output is
      C : constant String :=
        Ada.Characters.Handling.To_Upper (CL_Switches.Explain.all);
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

      --  Start of processing for Produce_List_Categories_Output

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
      use Ada.Strings.Unbounded;
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

      procedure Init (Tree : out Project.Tree.Object);
      --  Load the project file; This function requires the project file to be
      --  present.

      procedure Parse_Proof_Switches (Com_Lin : String_List);
      --  Parse the Switches and Proof_Switches attributes in project files.
      --  The regular command line is needed to interpret them properly.

      procedure Postprocess;
      --  Read the switch variables set by command-line parsing and set the
      --  gnatprove variables.

      procedure File_Specific_Postprocess (FS : out File_Specific);
      --  Same as Postprocess, but for the switches that can be file-specific.
      --  For example, --level, --timeout are handled here.

      procedure Check_Obsolete_Prove_Switches (View : Project.View.Object);
      --  Check for the obsolete Prove.Switches attribute and issue a warning
      --  if present.

      procedure Set_Mode (FS : in out File_Specific);
      procedure Set_Output_Mode;
      procedure Set_Warning_Mode;
      procedure Set_Report_Mode;

      procedure Set_Level_Timeout_Steps_Provers (FS : out File_Specific);
      --  Using the --level, --timeout, --steps, --provers, --ce-steps,
      --  --counterexamples and --proof-warning-timeout switches, set the
      --  corresponding variables.

      procedure Set_Proof_Mode (FS : in out File_Specific);
      procedure Process_Limit_Switches;
      procedure Set_Provers
        (Prover : GNAT.Strings.String_Access; FS : in out File_Specific);
      procedure Set_Proof_Dir (View : GPR2.Project.View.Object);
      --  If attribute Proof_Dir is set in the project file,
      --  set global variable Proof_Dir to the full path
      --  <path-to-project-file>/<value-of-proof-dir>.

      procedure Sanity_Checking;
      --  Check the command line flags for conflicting flags

      function List_From_Attr
        (Attribute : GPR2.Project.Attribute.Object) return String_List_Access;
      --  Helper function to convert attribute to list of strings

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

      procedure File_Specific_Postprocess (FS : out File_Specific) is
      begin
         Set_Level_Timeout_Steps_Provers (FS);
         Set_Proof_Mode (FS);
         Set_Mode (FS);
         FS.No_Inlining := CL_Switches.No_Inlining;
         FS.No_Loop_Unrolling := CL_Switches.No_Loop_Unrolling;
         FS.Proof_Warnings := Proof_Warnings;
         FS.No_Inlining :=
           CL_Switches.No_Inlining or CL_Switches.No_Global_Generation;
         FS.Warning_Status := Configuration.Warning_Status;
      end File_Specific_Postprocess;

      ----------
      -- Init --
      ----------

      procedure Init (Tree : out Project.Tree.Object) is

      begin
         if not Null_Or_Empty_String (CL_Switches.Subdirs) then
            Phase2_Subdir :=
              Filesystem_String (CL_Switches.Subdirs.all) / Phase2_Subdir;

         end if;

         Proj_Opt.Add_Switch
           (Options.Subdirs, Phase2_Subdir.Display_Full_Name);
         if not Null_Or_Empty_String (CL_Switches.Config) then
            Proj_Opt.Add_Switch (Options.Config, CL_Switches.Config.all);
         end if;
         if not Null_Or_Empty_String (CL_Switches.Autoconf) then
            Proj_Opt.Add_Switch (Options.Autoconf, CL_Switches.Autoconf.all);
         end if;
         Project.Registry.Pack.Add
           (+"Prove", Project.Registry.Pack.Everywhere);
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
            & "invokation of GNATprove. Only the following switches are "
            & "allowed for file-specific switches: '--steps', '--timeout', "
            & "'--memlimit', '--proof', '--prover', '--level', '--mode', "
            & "'--counterexamples', '--no-inlining', '--no-loop-unrolling'");
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

         if CL_Switches.Print_Gpr_Registry then
            --  Print registered gpr attributes and exit as requested
            --  This should be done here before any warning/error outputs.

            GPR2.Project.Registry.Exchange.Export
              (Output => Ada.Text_IO.Put'Access);
            Succeed;
         end if;

         if CL_Switches.Target /= null and then CL_Switches.Target.all /= ""
         then
            Proj_Opt.Add_Switch (Options.Target, CL_Switches.Target.all);
         end if;
         if CL_Switches.RTS /= null and then CL_Switches.RTS.all /= "" then
            Proj_Opt.Add_Switch (Options.RTS, CL_Switches.RTS.all);
         end if;

         for S of CL_Switches.GPR_Project_Path loop
            Proj_Opt.Add_Switch (Options.AP, S);
         end loop;

         declare
            Project_File : constant String :=
              (if Null_Or_Empty_String (CL_Switches.P)
               then No_Project_File_Mode
               else CL_Switches.P.all);
            Status       : Boolean;

            --  Do not display warnings, as those messages will be duplicated
            --  during the call to gprbuild.
            Reporter : Spark_Reporter :=
              (GPR2.Reporter.Console.Create (GPR2.Reporter.No_Warnings)
               with null record);
         begin
            Proj_Opt.Add_Switch (Options.P, Project_File);

            Status :=
              Tree.Load
                (Proj_Opt,
                 Reporter         => Reporter,
                 Absent_Dir_Error => GPR2.No_Error);

            if not Status then
               Fail ("");
            end if;

            --  When updating the sources we now need both warnings and
            --  errors, in particular since duplicated body situation is
            --  a warning.

            Reporter.Set_Verbosity (GPR2.Reporter.Regular);
            Tree.Set_Reporter (Reporter);

            if not Tree.Update_Sources then
               Fail ("");
            end if;
         end;
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

      --------------------------
      -- Parse_Proof_Switches --
      --------------------------

      procedure Parse_Proof_Switches (Com_Lin : String_List) is

         function Concat
           (A, B : String_List_Access; C : String_List) return String_List;

         function Concat
           (A, B, C : String_List_Access; D : String_List) return String_List;

         procedure Expand_Ada_Switches (View : Project.View.Object);
         --  Replace the "Ada" section of the File_Specific_Map by entries for
         --  all files in the project, except for those which already have an
         --  entry.

         procedure Reset_File_Specific_Switches;
         --  Reset file-specific switches between parsing of the full
         --  command-line for each file.

         ------------
         -- Concat --
         ------------

         function Concat
           (A, B : String_List_Access; C : String_List) return String_List is
         begin
            return
              (if A = null then [] else A.all)
              & (if B = null then [] else B.all)
              & C;
         end Concat;

         function Concat
           (A, B, C : String_List_Access; D : String_List) return String_List
         is
         begin
            return
              (if A = null then [] else A.all)
              & (if B = null then [] else B.all)
              & (if C = null then [] else C.all)
              & D;
         end Concat;

         procedure Expand_Ada_Switches (View : Project.View.Object) is

            Gen : constant File_Specific := File_Specific_Map ("Ada");

            Messages : GPR2.Log.Object;
            pragma Unreferenced (Messages);
            Units    : GPR2.Build.Compilation_Unit.Maps.Map := View.Own_Units;
            Position : File_Specific_Maps.Cursor;
            Inserted : Boolean;
         begin
            File_Specific_Map.Delete ("Ada");
            for C in Units.Iterate loop
               File_Specific_Map.Insert
                 (Key      => String (Units (C).Main_Part.Source.Simple_Name),
                  New_Item => Gen,
                  Position => Position,
                  Inserted => Inserted);
            end loop;
         end Expand_Ada_Switches;

         ----------------------------------
         -- Reset_File_Specific_Switches --
         ----------------------------------

         procedure Reset_File_Specific_Switches is
         begin
            CL_Switches.Steps := Invalid_Steps;
            CL_Switches.CE_Steps := Invalid_Steps;
            CL_Switches.Timeout := null;
            CL_Switches.Memlimit := 0;
            CL_Switches.Proof := null;
            CL_Switches.Prover := null;
            CL_Switches.Level := Invalid_Level;
            CL_Switches.Counterexamples := null;
            CL_Switches.No_Inlining := False;
            CL_Switches.Mode := null;
            CL_Switches.No_Loop_Unrolling := False;
            CL_Switches.Proof_Warnings := null;
            CL_Switches.Proof_Warn_Timeout := Invalid_Timeout;
         end Reset_File_Specific_Switches;

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
               Parsed_Cmdline     : constant String_List :=
                 Concat (Prove_Switches, Proof_Switches_Ada, Com_Lin);
            begin
               --  parse all switches that apply to all files, concatenated in
               --  the right order (most important is last).

               Parse_Switches (All_Switches, Parsed_Cmdline);
               Postprocess;
               File_Specific_Postprocess (FS);
               File_Specific_Map.Insert ("Ada", FS);
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
                        FS             : File_Specific;
                        FS_Switches    : constant String_List_Access :=
                          List_From_Attr (Attr);
                        Parsed_Cmdline : constant String_List :=
                          Concat
                            (Prove_Switches,
                             Proof_Switches_Ada,
                             FS_Switches,
                             Com_Lin);
                     begin
                        if FS_Switches /= null then

                           --  parse the file switches to check if they contain
                           --  invalid switches; this is for error reporting
                           --  only.

                           Parse_Switches
                             (File_Specific_Only, FS_Switches.all);
                        end if;

                        --  parse all switches that apply to a single file,
                        --  *including* the global switches. File-specific
                        --  switches are more important than the other switches
                        --  in the project file, but less so than the command
                        --  line switches.

                        Reset_File_Specific_Switches;
                        Parse_Switches (All_Switches, Parsed_Cmdline);
                        File_Specific_Postprocess (FS);
                        File_Specific_Map.Insert (Attr.Index.Text, FS);
                     end;
                  end if;
               end loop;
               if First then
                  First := False;
                  declare
                     Default : constant File_Specific :=
                       File_Specific_Map ("Ada");
                  begin
                     File_Specific_Map.Insert ("default", Default);
                  end;
               end if;
               Expand_Ada_Switches (View);
            end;
         end loop;
      end Parse_Proof_Switches;

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
            Location : String_Access := GNAT.OS_Lib.Locate_Exec_On_Path (Exec);

            Present : constant Boolean := Location /= null;

         begin
            Free (Location);
            return Present;
         end On_Path;

         --  Start of processing for Postprocess

      begin
         Sanity_Checking;

         SPARK_Install.Z3_Present := On_Path ("z3");
         SPARK_Install.CVC5_Present := On_Path ("cvc5");
         SPARK_Install.Colibri_Present := On_Path ("colibri");

         Debug := CL_Switches.D or CL_Switches.Flow_Debug;
         Debug_Exec_RAC := CL_Switches.Debug_Exec_RAC;

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
            Abort_Msg ("error: wrong argument for -j", With_Help => False);
         else
            Parallel := CL_Switches.J;
         end if;

         if CL_Switches.No_Counterexample then
            Ada.Text_IO.Put_Line
              ("Note: switch ""--no-counterexample"" is ignored.");
            Ada.Text_IO.Put_Line
              ("Note: use ""--counterexamples=off"" instead.");
         end if;

         if CL_Switches.No_Axiom_Guard then
            Ada.Text_IO.Put_Line
              ("Note: switch ""--no-axiom-guard"" is ignored.");
            Ada.Text_IO.Put_Line
              ("Note: use ""--function-sandboxing=off"" instead.");
         end if;

         if CL_Switches.Function_Sandboxing.all not in "" | "on" | "off" then
            Abort_Msg
              ("error: wrong argument for --function-sandboxing, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         if CL_Switches.Checks_As_Errors.all = ""
           or else CL_Switches.Checks_As_Errors.all = "off"
         then
            Checks_As_Errors := False;
         elsif CL_Switches.Checks_As_Errors.all = "on" then
            Checks_As_Errors := True;
         else
            Abort_Msg
              ("error: wrong argument """
               & CL_Switches.Checks_As_Errors.all
               & """ for --checks-as-errors, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         if CL_Switches.Proof_Warnings.all = ""
           or else CL_Switches.Proof_Warnings.all = "off"
         then
            Proof_Warnings := False;
         elsif CL_Switches.Proof_Warnings.all = "on" then
            Proof_Warnings := True;
         else
            Abort_Msg
              ("error: wrong argument """
               & CL_Switches.Proof_Warnings.all
               & """ for --proof-warnings, "
               & "must be one of (on, off)",
               With_Help => False);
         end if;

         --  Handling of Only_Given and Filelist

         Only_Given :=
           CL_Switches.U
           or not Null_Or_Empty_String (CL_Switches.Limit_Subp)
           or not Null_Or_Empty_String (CL_Switches.Limit_Line)
           or not Null_Or_Empty_String (CL_Switches.Limit_Lines);

         if CL_Switches.U and then CL_Switches.File_List.Is_Empty then
            Ada.Text_IO.Put_Line
              (Ada.Text_IO.Standard_Error,
               "warning: switch -u without a file name is equivalent to "
               & "switch --no-subproject");
         end if;

         Process_Limit_Switches;

         GnateT_Switch := new String'(Check_gnateT_Switch (Tree.Root_Project));
         Set_Output_Mode;
         Set_Warning_Mode;
         Set_Report_Mode;
         Set_Proof_Dir (Tree.Root_Project);

         Use_Semaphores := not Debug and then not CL_Switches.Dbg_No_Sem;
      end Postprocess;

      ----------------------------
      -- Process_Limit_Switches --
      ----------------------------

      procedure Process_Limit_Switches is

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

            if not All_Projects then
               CL_Switches.File_List.Append
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

         --  Start of processing for Process_Limit_Switches

      begin

         --  We do not allow mixing of --limit-* switches, except for the
         --  combination of --limit-subp + --limit-line or --limit-region,
         --  as this is used by the gnatstudio plug-in.

         Check_Switch (CL_Switches.Limit_Name);
         Check_Switch (CL_Switches.Limit_Subp);
         Check_Switch (CL_Switches.Limit_Region);
         Check_Switch (CL_Switches.Limit_Line);
         Check_Switch (CL_Switches.Limit_Lines);
         if Switch_Count > 1 then
            if Switch_Count = 2
              and then not Null_Or_Empty_String (CL_Switches.Limit_Subp)
              and then
                (not Null_Or_Empty_String (CL_Switches.Limit_Region)
                 or else not Null_Or_Empty_String (CL_Switches.Limit_Line))
            then
               null;
            else
               Abort_Msg
                 ("Switches --limit-line, --limit-name, --limit-region and "
                  & "--limit-subp are mutually exclusive",
                  With_Help => False);
            end if;
         end if;

         Process_Limit_Directive ("limit-subp", CL_Switches.Limit_Subp);
         Process_Limit_Directive ("limit-region", CL_Switches.Limit_Region);
         Process_Limit_Directive ("limit-line", CL_Switches.Limit_Line);
         if not Null_Or_Empty_String (CL_Switches.Limit_Line) then
            Process_Limit_Line (CL_Switches.Limit_Line.all);
         end if;
         if not Null_Or_Empty_String (CL_Switches.Limit_Lines) then
            declare
               File_Handle : Ada.Text_IO.File_Type;
               Line_Count  : Integer := 1;
            begin
               Ada.Text_IO.Open
                 (File_Handle,
                  Ada.Text_IO.In_File,
                  CL_Switches.Limit_Lines.all);
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

      procedure Sanity_Checking is
      begin
         if (CL_Switches.Output_Msg_Only and CL_Switches.Replay)
           or else (CL_Switches.Output_Msg_Only and CL_Switches.F)
           or else (CL_Switches.F and CL_Switches.Replay)
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

      procedure Set_Level_Timeout_Steps_Provers (FS : out File_Specific) is
      begin

         case CL_Switches.Level is

            --  If level switch was not provided, set other switches to their
            --  default values.

            when Invalid_Level =>

               FS.Provers.Append ("cvc5");

               --  Default steps are used only if none of --steps and --timeout
               --  is used (either explicitly or through --level). Otherwise
               --  set to zero to indicate steps are not used.

               if CL_Switches.Steps = Invalid_Steps
                 and then CL_Switches.Timeout.all = ""
               then
                  FS.Steps := Default_Steps;
               else
                  FS.Steps := 0;
               end if;

               FS.Timeout := 0;
               FS.Memlimit := 0;
               FS.Counterexamples := False;

            --  See the UG for the meaning of the level switches

            when 0             =>
               FS.Provers.Append ("cvc5");
               FS.Steps := 0;
               FS.Timeout := 1;
               FS.Memlimit := 1000;
               FS.Counterexamples := False;

            when 1             =>
               FS.Provers.Append ("cvc5");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 1;
               FS.Memlimit := 1000;
               FS.Counterexamples := False;

            when 2             =>
               FS.Provers.Append ("cvc5");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 5;
               FS.Memlimit := 1000;
               FS.Counterexamples := True;

            when 3             =>
               FS.Provers.Append ("cvc5");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 20;
               FS.Memlimit := 2000;
               FS.Counterexamples := True;

            when 4             =>
               FS.Provers.Append ("cvc5");
               FS.Provers.Append ("z3");
               FS.Provers.Append ("altergo");
               FS.Steps := 0;
               FS.Timeout := 60;
               FS.Memlimit := 2000;
               FS.Counterexamples := True;

            when others        =>
               Abort_Msg
                 ("error: wrong argument for --level", With_Help => False);
         end case;

         FS.Check_Counterexamples := True;
         FS.CE_Steps := 0;
         FS.Proof_Warn_Timeout := Invalid_Timeout;

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
                  Abort_Msg
                    ("error: wrong argument for --timeout, "
                     & "must be a non-negative integer",
                     With_Help => False);
            end;
         end if;

         if CL_Switches.Memlimit = 0 then
            null;
         elsif CL_Switches.Memlimit < 0 then
            Abort_Msg
              ("error: wrong argument for --memlimit, "
               & "must be a non-negative integer",
               With_Help => False);
         else
            FS.Memlimit := CL_Switches.Memlimit;
         end if;

         if CL_Switches.Steps = Invalid_Steps then
            null;
         elsif CL_Switches.Steps < 0 then
            Abort_Msg
              ("error: wrong argument for --steps", With_Help => False);
         else
            FS.Steps := CL_Switches.Steps;
         end if;

         if CL_Switches.CE_Steps = Invalid_Steps then
            null;
         elsif CL_Switches.CE_Steps < 0 then
            Abort_Msg
              ("error: wrong argument for --ce-steps", With_Help => False);
         else
            FS.CE_Steps := CL_Switches.CE_Steps;
         end if;

         if CL_Switches.Proof_Warn_Timeout = Invalid_Timeout then
            null;
         elsif CL_Switches.Proof_Warn_Timeout < 0 then
            Abort_Msg
              ("error: wrong argument for --proof-warn-timeout",
               With_Help => False);
         else
            FS.Proof_Warn_Timeout := CL_Switches.Proof_Warn_Timeout;
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

         Set_Provers (CL_Switches.Prover, FS);

         if CL_Switches.Output_Msg_Only then
            FS.Provers.Clear;
         end if;

         if CL_Switches.Counterexamples.all = "" then
            null;
         elsif CL_Switches.Counterexamples.all = "on" then
            FS.Counterexamples := True;
         elsif CL_Switches.Counterexamples.all = "off" then
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
           and then not CL_Switches.Output_Msg_Only;

         if CL_Switches.Check_Counterexamples.all = "" then
            null;
         elsif CL_Switches.Check_Counterexamples.all = "on" then
            FS.Check_Counterexamples := True;
         elsif CL_Switches.Check_Counterexamples.all = "off" then
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

      procedure Set_Mode (FS : in out File_Specific) is
      begin
         if CL_Switches.Mode.all = "" then
            FS.Mode := GPM_All;
         elsif CL_Switches.Mode.all = "prove" then
            FS.Mode := GPM_Prove;
         elsif CL_Switches.Mode.all = "check" then
            FS.Mode := GPM_Check;
         elsif CL_Switches.Mode.all = "check_all"
           or else CL_Switches.Mode.all = "stone"
         then
            FS.Mode := GPM_Check_All;
         elsif CL_Switches.Mode.all = "flow"
           or else CL_Switches.Mode.all = "bronze"
         then
            FS.Mode := GPM_Flow;
         elsif CL_Switches.Mode.all = "all"
           or else CL_Switches.Mode.all = "silver"
           or else CL_Switches.Mode.all = "gold"
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

      procedure Set_Output_Mode is
      begin
         if CL_Switches.Output.all = "" then
            Output := GPO_Pretty_Simple;
         elsif CL_Switches.Output.all = "brief" then
            Output := GPO_Brief;
         elsif CL_Switches.Output.all = "oneline" then
            Output := GPO_Oneline;
         elsif CL_Switches.Output.all = "pretty" then
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

      procedure Set_Proof_Mode (FS : in out File_Specific) is
         Input       : String renames CL_Switches.Proof.all;
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
        (Prover : GNAT.Strings.String_Access; FS : in out File_Specific)
      is
         First : Integer;
         S     : constant String :=
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
            Abort_Msg
              ("error: wrong argument for --report", With_Help => False);
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
         elsif Warn_Switch = "on" or else Warn_Switch = "continue" then
            Warning_Mode := Gnat2Why_Opts.SW_Normal;
         else

            Abort_Msg
              ("error: wrong argument for --warnings", With_Help => False);
         end if;
      end Set_Warning_Mode;

      --  Local variables

      Com_Lin : String_List := [1 .. Ada.Command_Line.Argument_Count => <>];
      Attr    : GPR2.Project.Attribute.Object;

      --  Help message read from a static file

      use CL_Switches;

      --  Start of processing for Read_Command_Line

   begin

      for Index in 1 .. Com_Lin'Last loop
         Com_Lin (Index) := new String'(Ada.Command_Line.Argument (Index));
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

      --  This call to Parse_Switches just parses project-relevant switches
      --  (-P, -X etc) and ignores the rest.

      Parse_Switches (Project_Parsing, Com_Lin);

      if CL_Switches.Version then
         Produce_Version_Output;
         Succeed;
      end if;

      if CL_Switches.List_Categories then
         Produce_List_Categories_Output;
         Succeed;
      end if;

      if CL_Switches.Explain /= null and then CL_Switches.Explain.all /= ""
      then
         Produce_Explain_Output;
         Succeed;
      end if;

      --  Before doing the actual second parsing, we read the project file in

      Init (Tree);
      Check_Obsolete_Prove_Switches (Tree.Root_Project);

      if Clean then
         Clean_Up (Tree);
         Succeed;
      end if;

      if Tree.Root_Project.Check_Attribute
           ((+"Prove", +"Switches"), Result => Attr)
      then
         declare
            L : String_List_Access := List_From_Attr (Attr);
         begin
            --  parse the Switches attribute of the project file; this is to
            --  detect invalid switches only.

            Parse_Switches (Global_Switches_Only, L.all);
            Free (L);
         end;
      end if;

      if Tree.Root_Project.Check_Attribute
           ((+"Prove", +"Proof_Switches"),
            Index  => GPR2.Project.Attribute_Index.Create ("Ada"),
            Result => Attr)
      then
         declare
            L : String_List_Access := List_From_Attr (Attr);
         begin
            --  parse the Proof_Switches ("Ada") attribute of the project file;
            --  this is to detect invalid switches only.

            Parse_Switches (Global_Switches_Only, L.all);
            Free (L);
         end;
      end if;

      Parse_Proof_Switches (Com_Lin);

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
              (Tree
                 .Root_Project
                 .Object_Directory
                 .Virtual_File
                 .Display_Full_Name);
         end if;
      end;
      Sanitize_File_List (Tree);

      --   Set the maximum number of concurrent gnatwhy3 processes based on
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
   end Read_Command_Line;

   ------------------------
   -- Sanitize_File_List --
   ------------------------

   procedure Sanitize_File_List (Tree : Project.Tree.Object) is
      use String_Lists;
   begin
      if CL_Switches.File_List.Is_Empty then
         return;
      end if;

      --  We iterate over all names in the file list

      for Cursor in CL_Switches.File_List.Iterate loop

         declare
            File_Entry       : String renames CL_Switches.File_List (Cursor);
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
                        CL_Switches.File_List.Replace_Element
                          (Cursor, String (CU.Main_Part.Source.Simple_Name));
                        Found := True;
                     end if;
                  end if;
               end;
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
        (if CL_Switches.Why3_Conf.all /= ""
         then Create (Filesystem_String (CL_Switches.Why3_Conf.all))
         else No_File);
      Gnatwhy3_Conf : constant String :=
        (if Why3_VF /= No_File
         then
           (if Is_Absolute_Path (Why3_VF)
            then CL_Switches.Why3_Conf.all
            else
              Ada.Directories.Compose
                (+Get_Current_Dir.Full_Name, CL_Switches.Why3_Conf.all))
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
         GNAT.OS_Lib.Spawn
           (Program_Name => Gnatwhy3, Args => Args, Success => Res);
         Free (Args);
         Ada.Directories.Set_Directory (Old_Dir);
         if Verbose then
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

      if CL_Switches.Why3_Debug.all /= "" then
         Args.Append ("--debug-why3");
         Args.Append (CL_Switches.Why3_Debug.all);
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

      if CL_Switches.Z3_Counterexample then
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

      if CL_Switches.Debug_Prover_Errors then
         Args.Append ("--debug-prover-errors");
      end if;

      if CL_Switches.Why3_Logging then
         Args.Append ("--logging");
      end if;

      Args.Append ("--ce-timeout");
      Args.Append (Image (FS.CE_Timeout, 1));

      return Args;
   end Compute_Why3_Args;

end Configuration;
