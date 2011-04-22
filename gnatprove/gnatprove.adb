------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;
with Ada.Environment_Variables;
with Altergo;           use Altergo;

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Expect;       use GNAT.Expect;
with GNAT.OS_Lib;       use GNAT.OS_Lib;
with GNAT.Strings;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.Utils;    use GNATCOLL.Utils;
with GNATCOLL.VFS;      use GNATCOLL.VFS;

with Ada.Text_IO;

procedure Gnatprove is

   --  Variables for command line parsing
   Config       : Command_Line_Configuration;
   Verbose      : aliased Boolean;
   --  True if -v switch is present. All executed commands are printed.
   Report       : aliased Boolean;
   --  True if --report switch is present. A message is printed for all VCs.
   All_VCs      : aliased Boolean;
   --  True if --all-vcs switch is present. Do not pass option "-gnatd.G" to
   --  gnat2why

   Project_File : aliased GNAT.Strings.String_Access;
   --  The project file name, given with option -P

   Subdir_Name  : constant Filesystem_String := "gnatprove";
   WHYLIB       : constant String := "WHYLIB";
   Exec_Loc     : constant String := Executable_Location;
   Why_Lib_Dir  : constant String :=
      Ada.Directories.Compose ("lib", "why");
   Gpr_Cnf_File : constant String :=
      Ada.Directories.Compose
         (Ada.Directories.Compose
            (Ada.Directories.Compose (Exec_Loc, "share"),
             "gprbuild"),
          "gnat2why.cgpr");
   Main_Suffix  : constant String := "__package";

   procedure Call_Gnatmake (Project_File : String);
   --  Call gnatmake using the given project file.

   procedure Call_Gprbuild (Project_File : String);
   --  Call gnatmake using the given project file.

   procedure Call_Why (Proj : Project_Tree; File : Virtual_File);
   --  Call why on all the generated files that belong to a certain file
   --  in a project.
   --  example: if File is "example.adb", we call why on file
   --  "example__package.why".

   function Get_Ada_Include return String;
   --  Return the Ada include directory, using "gnatls".

   generic
      with procedure Action (Proj : Project_Tree; File : Virtual_File);
   procedure Iter_Project_Source_Files (Proj : Project_Tree);
   --  Iterate over all source files of a project.

   procedure Make_Standard_Package (Proj : Project_Tree);
   --  Produce the file "_standard.why".

   -------------------
   -- Call_Gnatmake --
   -------------------

   procedure Call_Gnatmake (Project_File : String) is
   begin
      Call_Exit_On_Failure
        (Command   => "gnatmake",
         Arguments => (1 => new String'("-P"),
                       2 => new String'(Project_File),
                       3 => new String'("--subdirs=" & String (Subdir_Name)),
                       4 => new String'("-gnatc"),      --  only generate ALI
                       5 => new String'("-gnatd.F")),   --  ALFA section in ALI
         Verbose   => Verbose);
   end Call_Gnatmake;

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild (Project_File : String)
   is
      Arguments : Argument_List :=
         (1 => new String'("-P"),
          2 => new String'(Project_File),
          3 => new String'("--subdirs=" & String (Subdir_Name)),
          4 => new String'("--config=" & Gpr_Cnf_File));
   begin
      Arguments :=
         (if Verbose then
            Arguments & (1 => new String'("-v"))
         else
            Arguments & (1 => new String'("-q")));
      if All_VCs then
         Call_Exit_On_Failure
           (Command   => "gprbuild",
            Arguments => Arguments,
            Verbose   => Verbose);
      else
         Call_Exit_On_Failure
           (Command   => "gprbuild",
            Arguments =>
               Arguments &
                  (1 => new String'("-cargs:Ada"),
                   2 => new String'("-gnatd.G")),
            Verbose   => Verbose);
      end if;
   end Call_Gprbuild;

   --------------
   -- Call_Why --
   --------------

   procedure Call_Why (Proj : Project_Tree; File : Virtual_File) is
      pragma Unreferenced (Proj);

      Base : constant String :=
           Ada.Directories.Base_Name (+Full_Name (File));

   begin
      --  Assuming 'base' to be the filename without suffix, call the
      --  command
      --  why --multiwhy --explain --locs <base>.locs <base>.why

      --  ??? It would be good to generate VCs for all objectives, as --all-vc
      --  would permit, but currently this generates VCs which we cannot match
      --  back to user source code. (e.g. for a trivially True pre- or
      --  postcondition introduced by gnat2why)

      Call_Exit_On_Failure
        (Command   => "why",
         Arguments =>
           ((1 => new String'("--multi-why"),
             2 => new String'("--fast-wp"),
             3 => new String'("--explain"),
             4 => new String'("--locs"),
             5 => new String'(Base & Main_Suffix & ".loc"),
             6 => new String'(Base & Main_Suffix & ".why"))),
         Verbose   => Verbose);
   end Call_Why;

   ---------------------
   -- Get_Ada_Include --
   ---------------------

   function Get_Ada_Include return String is
      D : Process_Descriptor;
      A : Expect_Match;
   begin
      GNAT.Expect.Non_Blocking_Spawn
        (Descriptor => D,
         Command    => "gnatls",
         Args       => (1 => new String'("-v")));
      GNAT.Expect.Expect
        (Descriptor => D,
         Result => A,
         Regexp => "[^ \n].*adainclude[^\n ]*");
      return Expect_Out_Match (D);
   end Get_Ada_Include;

   -------------------------------
   -- Iter_Project_Source_Files --
   -------------------------------

   procedure Iter_Project_Source_Files (Proj : Project_Tree) is
      Proj_Type : constant Project_Type := Proj.Root_Project;
      File_List : constant File_Array_Access := Proj_Type.Source_Files;
   begin
      for Index in File_List'Range loop
         declare
            Inf : constant File_Info := Info (Proj, File_List (Index));
         begin
            case Unit_Part (Inf) is
               when Unit_Body =>
                  Action (Proj, File_List (Index));

               when Unit_Spec =>
                  if File_From_Unit
                       (Proj_Type,
                        Unit_Name (Inf),
                        Unit_Body,
                        "ada") = ""
                  then
                     Action (Proj, File_List (Index));
                  end if;

               when others =>
                  null;

            end case;

         end;
      end loop;
   end Iter_Project_Source_Files;

   procedure Make_Standard_Package (Proj : Project_Tree)
   is
      Ada_Ads : constant String :=
         Ada.Directories.Compose (Get_Ada_Include, "ada.ads");
   begin
      pragma Unreferenced (Proj);
      Call_Exit_On_Failure
        (Command   => "gnat2why",
         Arguments =>
            (1 => new String'("-gnatd.H"),
             2 => new String'("-gnatg"),
             3 => new String'(Ada_Ads)),
         Verbose   => Verbose);
   end Make_Standard_Package;

   Tree      : Project_Tree;
   Proj_Type : Project_Type;
   Proj_Env  : Project_Environment_Access;

   procedure Call_Altergo_Wrap (Proj : Project_Tree; File : Virtual_File);

   procedure Call_Altergo_Wrap (Proj : Project_Tree; File : Virtual_File) is
   begin
      Call_Altergo (Proj, File, Verbose, Report);
   end Call_Altergo_Wrap;

   procedure Iterate_Altergo is
     new Iter_Project_Source_Files (Call_Altergo_Wrap);

   procedure Iterate_Why is
     new Iter_Project_Source_Files (Call_Why);

   --  begin processing for Gnatprove

begin
   --  Install command line config

   Define_Switch (Config, Verbose'Access,
                  "-v", Long_Switch => "--verbose",
                  Help => "Output extra verbose information");

   Define_Switch (Config, All_VCs'Access,
                  Long_Switch => "--all-vcs",
                  Help => "Activate generation of VCs for subprograms");

   Define_Switch (Config, Report'Access,
                  Long_Switch => "--report",
                  Help => "Print messages for all generated VCs");

   Define_Switch (Config, Project_File'Access,
                  "-P:",
                  Help => "The name of the project file");

   Getopt (Config);

   if Project_File.all = "" then
      Ada.Text_IO.Put_Line
        (Ada.Text_IO.Standard_Error,
         "No project file given, aborting.");
      GNAT.OS_Lib.OS_Exit (1);
   end if;

   Initialize (Proj_Env);
   Set_Object_Subdir (Proj_Env.all, Subdir_Name);
   Tree.Load
     (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
      Proj_Env);
   Proj_Type := Root_Project (Tree);
   --  Call gnatmake before changing the directory, for the project file to
   --  be in the path
   Call_Gnatmake (Project_File.all);

   Call_Gprbuild (Project_File.all);

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);
   Make_Standard_Package (Tree);

   --  Set the environment variable WHYLIB, if necessary, to indicate the
   --  placement for Why
   if not Ada.Environment_Variables.Exists (WHYLIB) then
      Ada.Environment_Variables.Set (WHYLIB,
         Ada.Directories.Compose (Exec_Loc, Why_Lib_Dir));
   end if;

   Iterate_Why (Tree);
   Iterate_Altergo (Tree);
exception
   when Invalid_Project =>
      Ada.Text_IO.Put
        (Ada.Text_IO.Standard_Error,
         "Error: could not find project file: ");
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Project_File.all);
end Gnatprove;
