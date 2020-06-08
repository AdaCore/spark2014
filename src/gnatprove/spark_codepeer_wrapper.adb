------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--               S P A R K _ C O D E P E E R _ W R A P P E R                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2008-2020, AdaCore                     --
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

with Ada.Characters;
with Ada.Characters.Handling;
with Ada.Command_Line;           use Ada.Command_Line;
with Ada.Containers.Hashed_Sets;
with Ada.Directories;            use Ada.Directories;
with Ada.Strings.Fixed;
with Ada.Text_IO;                use Ada.Text_IO;

with GNAT.OS_Lib;                use GNAT.OS_Lib;
with GNAT.Strings;

with GNATCOLL.Utils;             use GNATCOLL.Utils;
with GNATCOLL.VFS;               use GNATCOLL.VFS;
with GNATCOLL.Projects;          use GNATCOLL.Projects;

with String_Utils;               use String_Utils;

--  Wrapper around the codepeer_be executable for SPARK integration

procedure SPARK_CodePeer_Wrapper
  with No_Return
is

   subtype String_Access is GNAT.OS_Lib.String_Access;

   Verbose             : Boolean := False;
   Help_Requested      : Boolean := False;
   Compile_All_Sources : Boolean := False;

   Num_Procs : String_Access;
   --  Number of processors to use, null if unspecified

   Steps : String_Access;
   --  Number of allowed steps, null if unspecified

   Project_File : Virtual_File := No_File;
   --  project file, provided with -P switch

   File         : Virtual_File := No_File;
   --  variable for -file switch

   RTS_Arg      : String_Access;
   --  contains the argument --RTS=<path> (including the --RTS prefix), if
   --  present

   Target_Arg   : String_Access;
   --  contains the argument --target=targ (including the --target prefix), if
   --  present

   Subdirs      : Virtual_File := Create ("gnatprove") / "codepeer";

   Library      : String_Access;

   Ext_Vars     : String_Lists.List;

   Scil_Dir_Arg : Virtual_File := No_File;
   --  we need a single SCIL dir to pass to codepeer via -scil-dir, doesn't
   --  matter which one we pick

   procedure Error (Message : String) with No_Return;
   --  Display error message and exit the application

   function Locate_Exec (Exec : String) return String_Access;
   --  Locate Exec either from argv(0) or from the PATH

   procedure Parse_Command_Line;
   --  Parse command line arguments

   procedure Parse_Project (Project : Virtual_File; Tree : out Project_Tree);
   --  Parse .gpr project file into tree

   procedure Create_Library
     (Tree    :     Project_Tree;
      Library : out String_Access);
   --  Create library file from project Tree.
   --  Set name of library file created in Library

   generic
      Args      : in out Argument_List;
      Arg_Count : in out Natural;
   procedure Generic_Append_Arg (Arg : String);
   --  Append Arg in Args, and increment Arg_Count accordingly

   procedure Generate_SCIL (Project : Virtual_File);
   --  (Re)generate SCIL files on project Project by calling gprbuild

   function Local_Spawn (Exe : String; Args : Argument_List) return Integer;
   --  Spawn Exe with given Args.
   --  Check for validity of the command before spawning.
   --  Return exit status of spawned command.

   procedure Free (Args : in out Argument_List);
   --  Free all elements of Args

   function Object_Directory (Project : Project_Type) return Virtual_File;
   --  Return object dir associated with Project, or the project's directory if
   --  none.

   function Output_Directory (Project : Project_Type) return Virtual_File;
   --  Return directory which is used by CodePeer to output results

   function Database_Directory (Project : Project_Type) return Virtual_File;
   --  Return directory which is used by CodePeer to store SQLite DB files

   function Library_File_Name
     (Project : Project_Type;
      Suffix  : String := "") return Virtual_File;
   --  Return the name of a CodePeer library file, for the given Project and
   --  additional optional suffix.

   procedure Display_Help with No_Return;
   --  Display help message and exit

   -----------
   -- Error --
   -----------

   procedure Error (Message : String) is
   begin
      Put_Line (Message);
      OS_Exit (1);
   end Error;

   ------------------------
   -- Generic_Append_Arg --
   ------------------------

   procedure Generic_Append_Arg (Arg : String) is
   begin
      Arg_Count := Arg_Count + 1;
      Args (Arg_Count) := new String'(Arg);
   end Generic_Append_Arg;

   Args_Padding : constant := 128;
   --  Plenty of room for extra switches

   Count    : constant Natural := Argument_Count;
   Msg_Args : Argument_List (1 .. Count + Args_Padding);

   ----------------------
   -- Object_Directory --
   ----------------------

   function Object_Directory (Project : Project_Type) return Virtual_File is
      Obj : constant Virtual_File := Project.Object_Dir;
   begin
      if Obj /= No_File then
         return Obj;
      else
         return Project.Project_Path.Dir;
      end if;
   end Object_Directory;

   ----------------------
   -- Output_Directory --
   ----------------------

   function Output_Directory (Project : Project_Type) return Virtual_File is
      Name      : constant Filesystem_String :=
        Filesystem_String
          (Ada.Characters.Handling.To_Lower
             (String (Project_Path (Project).Base_Name)));
      Extension : constant Filesystem_String :=
        Project_Path (Project).File_Extension;

   begin
      return Create_From_Dir
        (Object_Directory (Project),
         Name (Name'First .. Name'Last - Extension'Length) & ".output");
   end Output_Directory;

   ------------------------
   -- Database_Directory --
   ------------------------

   function Database_Directory
     (Project : Project_Type) return Virtual_File
   is
      Name      : constant Filesystem_String :=
        Filesystem_String
          (Ada.Characters.Handling.To_Lower
             (String (Project_Path (Project).Base_Name)));
      Extension : constant Filesystem_String :=
        Project_Path (Project).File_Extension;

   begin
      return Create_From_Dir
        (Object_Directory (Project),
         Name (Name'First .. Name'Last - Extension'Length) & ".db");
   end Database_Directory;

   -----------------------
   -- Library_File_Name --
   -----------------------

   function Library_File_Name
     (Project : Project_Type;
      Suffix  : String := "") return Virtual_File
   is
      Name      : constant Filesystem_String :=
        Filesystem_String (String (Project_Path (Project).Base_Name));
      Extension : constant Filesystem_String :=
        Project_Path (Project).File_Extension;

   begin
      return
        Create_From_Dir
          (Object_Directory (Project),
           Name (Name'First .. Name'Last - Extension'Length)
           & Filesystem_String (Suffix)
           & ".library");
   end Library_File_Name;

   -------------------
   -- Parse_Project --
   -------------------

   procedure Parse_Project (Project : Virtual_File; Tree : out Project_Tree) is
      Proj_Env     : Project_Environment_Access;
      GNAT_Version : GNAT.Strings.String_Access;
   begin
      Initialize (Proj_Env);
      Set_Path_From_Gnatls (Proj_Env.all, "codepeer-gnatls", GNAT_Version);
      Free (GNAT_Version);
      Set_Object_Subdir (Proj_Env.all,
                         Filesystem_String (Subdirs.Display_Full_Name));
      Proj_Env.Register_Default_Language_Extension ("C", ".h", ".c");
      for Ext of Ext_Vars loop
         declare
            Equal : constant Natural := Ada.Strings.Fixed.Index (Ext, "=");
         begin
            Proj_Env.Change_Environment
              (Ext (Ext'First + 2 .. Equal - 1),
               Ext (Equal + 1 .. Ext'Last));
         end;
      end loop;
      Tree.Load (Project, Proj_Env, Recompute_View => True);
   exception
      when others =>
         Error ("cannot parse project file " & Project.Display_Base_Name);
   end Parse_Project;

   -------------------
   -- Generate_SCIL --
   -------------------

   procedure Generate_SCIL (Project : Virtual_File) is
      Args      : Argument_List (1 .. 128);
      --  There should be as many elements in Args as there are calls to
      --  Append_Arg below. Add enough padding for future calls.

      Arg_Count : Natural := 0;
      Status    : Integer;

      procedure Append_Arg is new Generic_Append_Arg (Args, Arg_Count);
   begin
      --  Call gprbuild:
      --  codepeer-gprbuild -c --codepeer <other options> [-jxx] -Pproject

      Append_Arg ("-c");
      Append_Arg ("--codepeer");
      Append_Arg ("--restricted-to-languages=ada");

      --  Do not assume that the first bounds of an array index is within the
      --  bounds of the index subtype. It might be only within the bounds of
      --  the base type, like an empty string with bounds 0 and -1. This is an
      --  unsound assumption that is made by CodePeer to avoid false positives,
      --  that is not valid for use in GNATprove.

      Append_Arg ("-gnatd.7");

      if Num_Procs /= null then
         Append_Arg ("-j" & Num_Procs.all);
      end if;

      if Compile_All_Sources then
         Append_Arg ("-U");
      end if;

      if Verbose then
         Append_Arg ("-v");
      else
         Append_Arg ("-q");
         Append_Arg ("-ws");
         Append_Arg ("--no-exit-message");
      end if;

      if File /= No_File then
         Append_Arg ("-u");
         Append_Arg (File.Display_Base_Name);
      end if;

      if RTS_Arg /= null then
         Append_Arg (RTS_Arg.all);
      end if;

      if Target_Arg /= null then
         Append_Arg (Target_Arg.all);
      end if;

      --  Compilation switch -gnateF ensures that CodePeer interprets
      --  floating-point overflows as errors even for the predefined
      --  floating-point types.

      Append_Arg ("-gnateF");

      Append_Arg ("--subdirs=" & Subdirs.Display_Full_Name);
      Append_Arg ("-P" & Project.Display_Full_Name);

      for Ext of Ext_Vars loop
         Append_Arg (Ext);
      end loop;

      Status := Local_Spawn ("codepeer-gprbuild", Args (1 .. Arg_Count));
      Free (Args);

      --  If gprbuild failed, something unexpected happened, exit immediately

      if Status /= 0 then
         OS_Exit (Status);
      end if;
   end Generate_SCIL;

   -----------------
   -- Locate_Exec --
   -----------------

   function Locate_Exec (Exec : String) return String_Access is
      Command     : constant String := Command_Name;
      Exe         : String_Access := Get_Target_Executable_Suffix;
      Exec_Suffix : constant String := Exe.all;

   begin
      Free (Exe);

      if Is_Absolute_Path (Command)
        and then Is_Executable_File
          (Compose (Containing_Directory (Command), Exec & Exec_Suffix))
      then
         return new String'(Compose (Containing_Directory (Command), Exec));
      else
         return Locate_Exec_On_Path (Exec);
      end if;
   end Locate_Exec;

   --------------------
   -- Create_Library --
   --------------------

   procedure Create_Library
     (Tree    :     Project_Tree;
      Library : out String_Access)
   is
      procedure Generate_Source_Directive
        (Lib_File : Ada.Text_IO.File_Type;
         Scil_Dir : GNATCOLL.VFS.Virtual_File);
      --  Generates Source directive for the specific SCIL directory in the
      --  library file, unless it contains no SCIL files, in which case it
      --  does nothing.

      -------------------------------
      -- Generate_Source_Directive --
      -------------------------------

      procedure Generate_Source_Directive
        (Lib_File : Ada.Text_IO.File_Type;
         Scil_Dir : GNATCOLL.VFS.Virtual_File)
      is
         function Has_Scil_Files (Dir : String) return Boolean;
         --  Return True iff directory Dir contains SCIL files

         --------------------
         -- Has_Scil_Files --
         --------------------

         function Has_Scil_Files (Dir : String) return Boolean is
            Scil_Search : Search_Type;
         begin
            Start_Search (Scil_Search, Dir, "*.scil");
            return More_Entries (Scil_Search);
         end Has_Scil_Files;

         Scil_Dir_Name : constant String := Scil_Dir.Display_Dir_Name & "SCIL";

      --  Start of processing for Generate_Source_Directive

      begin
         --  Do not generate a Source directive if the SCIL directory does
         --  not exist or does not contain SCIL files, to avoid a warning
         --  from CodePeer.

         if Exists (Scil_Dir_Name)
           and then Has_Scil_Files (Scil_Dir_Name)
         then
            Ada.Text_IO.Put_Line
              (Lib_File, "Source (Directory => """ & Scil_Dir_Name & """,");
            Ada.Text_IO.Put_Line
              (Lib_File, "        Files     => (""*.scil""),");
            Ada.Text_IO.Put_Line
              (Lib_File, "        Language  => SCIL);");
         end if;
      end Generate_Source_Directive;

      F       : Ada.Text_IO.File_Type;
      Project : Project_Type;

   --  Start of processing for Generate_Source_Directive

   begin
      Project := Tree.Root_Project;
      Library := new String'
        (String (Library_File_Name (Project, "").Full_Name.all));

      Ada.Text_IO.Create (F, Ada.Text_IO.Out_File, Library.all);
      Ada.Text_IO.Put_Line
        (F,
         "Output_Dir := """
         & (+Output_Directory (Project).Full_Name) & """;");
      Ada.Text_IO.Put_Line
        (F,
         "Database_Dir := """
         & (+Database_Directory (Project).Full_Name) & """;");
      Ada.Text_IO.New_Line (F);

      --  Only generate one Source directive for a given object directory, to
      --  correctly deal with the case where multiple sub-projects share the
      --  same object directory.

      declare
         Object_Dirs : constant File_Array :=
           Tree.Root_Project.Object_Path
             (Recursive           => True,
              Including_Libraries => False);

         package Virtual_File_Sets is new Ada.Containers.Hashed_Sets
           (Element_Type        => Virtual_File,
            Hash                => Full_Name_Hash,
            Equivalent_Elements => "=",
            "="                 => "=");
         use Virtual_File_Sets;

         Seen : Virtual_File_Sets.Set;

      begin
         for Dir of Object_Dirs loop
            if not Seen.Contains (Dir) then
               Generate_Source_Directive (F, Dir);
               Seen.Insert (Dir);
            end if;
         end loop;

         --  If Seen was empty, we wouldn't have any object dir. I don't think
         --  that's actually possible, and we would have problems earlier
         --  anyway.

         Scil_Dir_Arg := Virtual_File_Sets.Element (Seen.First);
      end;

      Ada.Text_IO.Close (F);
   end Create_Library;

   Args      : Argument_List (1 .. Count + Args_Padding);
   Arg_Count : Natural := 0;

   procedure Append_Arg is new Generic_Append_Arg (Args, Arg_Count);

   ------------------------
   -- Parse_Command_Line --
   ------------------------

   procedure Parse_Command_Line is
      Index : Positive := 1;
   begin
      while Index <= Count loop
         declare
            S : String renames Argument (Index);
         begin
            pragma Assert (S'First = 1);
            if S = "-verbose" then
               Verbose := True;

            elsif Starts_With (S, "-P") then
               if S'Length = 2 then
                  --  There is a separation between the "-P" and the name of
                  --  the project file, so the name of the project is the next
                  --  command-line argument.

                  Index := Index + 1;

                  if Index > Count then
                     Error ("missing -P parameter.");
                  end if;

                  Project_File := GNATCOLL.VFS.Create_From_Base
                    (Filesystem_String (Argument (Index)));

               else
                  --  No separation between the "-P" and the name of the
                  --  project file, so we just skip the "-P" characters.

                  Project_File := GNATCOLL.VFS.Create_From_Base
                    (Filesystem_String (S (3 .. S'Last)));
               end if;

               Append_Arg ("-all");

            elsif Starts_With (S, "--RTS=") then

               RTS_Arg := new String'(S);

            elsif Starts_With (S, "--target=") then

               Target_Arg := new String'(S);

            elsif Starts_With (S, "--subdirs=") then

               Subdirs :=
                 Filesystem_String (S (11 .. S'Last)) / Subdirs;

            elsif Starts_With (S, "-j") then
               Num_Procs := new String'(S (3 .. S'Last));

            elsif Starts_With (S, "-steps=") then
               Steps := new String'(S (8 .. S'Last));

            elsif S = "-file" then
               Index := Index + 1;

               if Index > Count then
                  Put_Line ("missing -file parameter.");
                  OS_Exit (2);
               end if;

               File := GNATCOLL.VFS.Create_From_Base
                 (Filesystem_String (Argument (Index)));

            elsif S = "--help" then
               Help_Requested := True;

            elsif S = "-U" then
               Compile_All_Sources := True;

            elsif Starts_With (S, "-X") then
               Ext_Vars.Append (S);

            else
               Put_Line ("unknown switch: " & S);
               Help_Requested := True;
            end if;
         end;

         Index := Index + 1;
      end loop;
   end Parse_Command_Line;

   -----------------
   -- Local_Spawn --
   -----------------

   function Local_Spawn (Exe : String; Args : Argument_List) return Integer is
      Exec   : String_Access;
      Status : Integer;

   begin
      --  Display command line if -verbose

      if Verbose then
         Put (Exe);

         for Arg of Args loop
            Put (" " & Arg.all);
         end loop;

         New_Line;
      end if;

      --  Spawn command

      Exec := Locate_Exec (Exe);

      if Exec = null then
         Error (Exe & " executable not found, exiting.");
      end if;

      Status := Spawn (Exec.all, Args);

      Free (Exec);
      return Status;
   end Local_Spawn;

   ----------
   -- Free --
   ----------

   procedure Free (Args : in out Argument_List) is
   begin
      for Arg of Args loop
         Free (Arg);
      end loop;
   end Free;

   ------------------
   -- Display_Help --
   ------------------

   procedure Display_Help is
   begin
      Error
        ("usage: codepeer_spark_wrapper -P <project-file>" &
           " [-j<num-of-procs>]" &
           " [-steps=<num-of-steps>]" &
           " [--RTS=<runtime>]" &
           " [--target=<target>]" &
           " [--subdirs=<subdir>]" &
           " [-U]" &
           " [-X]");
   end Display_Help;

   Status : Integer;
   Tree   : Project_Tree;

begin
   --  Parse command line, and recognize special switches

   Parse_Command_Line;

   if Help_Requested or else Project_File = No_File then
      Display_Help;
   end if;

   --  Generate SCIL files via codepeer-gprbuild. Do that first, so that we
   --  can detect object directories with no SCIL files, for which we do not
   --  generate an entry in the library file.

   Generate_SCIL (Project_File);

   --  Support for .gpr files:
   --  - set environment (so that e.g. codepeer-gnatls can be found)
   --  - parse project file
   --  - create a low level .library file corresponding to the .gpr to give to
   --    codepeer_be which is not project aware
   --  - switch current directory to the object directory so that e.g.
   --    any partition library file will be created there

   Parse_Project (Project_File, Tree);
   Create_Library
     (Tree      => Tree,
      Library   => Library);
   Append_Arg ("-lib");
   Append_Arg (Library.all);
   Set_Directory (Object_Directory (Tree.Root_Project).Display_Full_Name);

   --  Common switches

   if not Verbose then
      Append_Arg ("-quiet");
   end if;

   Append_Arg ("-no-race-conditions");
   Append_Arg ("-no-preconditions");
   Append_Arg ("-no-text-output");
   Append_Arg ("-no-html-output");

   if Num_Procs /= null then
      Append_Arg ("-jobs");
      Append_Arg (Num_Procs.all);
   end if;

   if Steps /= null then
      Append_Arg ("-steps");
      Append_Arg (Steps.all);
   end if;

   --  Append low level switches corresponding to the analysis requested

   Append_Arg ("-global");
   Append_Arg ("-sa-messages");
   Append_Arg ("-messages");
   Append_Arg ("max");
   Append_Arg ("-dbg-vn-limit");
   Append_Arg ("60000");
   Append_Arg ("-no-presumptions");
   Append_Arg ("-no-db-msgs");

   --  CodePeer needs one of the SCIL directories passed using -scil-dir, we
   --  use the one we stored earlier in Scil_Dir_Arg

   Append_Arg ("-scil-dir");
   Append_Arg (Scil_Dir_Arg.Display_Full_Name);

   Normalize_Arguments (Args);

   --  Spawn codepeer_be which does the core analysis

   Status := Local_Spawn ("codepeer_be", Args (1 .. Arg_Count));
   Free (Args);
   Free (Msg_Args);
   Free (Library);
   OS_Exit (Status);
end SPARK_CodePeer_Wrapper;
