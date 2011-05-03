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
      Ada.Directories.Compose
         (Ada.Directories.Compose (Exec_Loc, "lib"),
          "why");
   Gpr_Cnf_Dir  : constant String :=
      Ada.Directories.Compose
        (Ada.Directories.Compose (Exec_Loc, "share"),
         "gnatprove");
   Gpr_Ada_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "gnat2why.cgpr");
   Gpr_Why_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "why.cgpr");

   procedure Call_Gprbuild (Arguments : Argument_List);
   --  Call gprbuild with the given arguments

   procedure Compute_ALI_Information (Project_File : String);
   --  Compute ALI information for all source units, using gnatmake.

   procedure Compute_VCs (Proj : Project_Tree);
   --  Compute Verification conditions using Why, driven by gprbuild.

   function Generate_Why_Project_File (Source_Dir : String)
       return String;
   --  Extract the necessary information from the user project to generate a
   --  Why project file; Write the file to disk and return the file name.

   generic
      with procedure Action (Proj : Project_Tree; File : Virtual_File);
   procedure Iter_Project_Source_Files (Proj : Project_Tree);
   --  Iterate over all source files of a project.

   procedure Make_Standard_Package (Proj : Project_Tree);
   --  Produce the file "_standard.mlw".

   procedure Translate_To_Why (Project_File : String);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.

   procedure Read_Command_Line;
   --  Parse command line and set up configuration.

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild (Arguments : Argument_List)
   is
      Extra_Args : constant Argument_List :=
         (if Verbose then
            (1 => new String'("-v"))
         else
            (1 => new String'("-q")));
   begin
      Call_Exit_On_Failure
        (Command   => "gprbuild",
         Arguments => Extra_Args & Arguments,
         Verbose   => Verbose);
   end Call_Gprbuild;

   -----------------------------
   -- Compute_ALI_Information --
   -----------------------------

   procedure Compute_ALI_Information (Project_File : String) is
   begin
      Call_Exit_On_Failure
        (Command   => "gnatmake",
         Arguments => (1 => new String'("-P"),
                       2 => new String'(Project_File),
                       3 => new String'("--subdirs=" & String (Subdir_Name)),
                       4 => new String'("-gnatc"),      --  only generate ALI
                       5 => new String'("-gnatd.F")),   --  ALFA section in ALI
         Verbose   => Verbose);
   end Compute_ALI_Information;

   -----------------
   -- Compute_VCs --
   -----------------

   procedure Compute_VCs (Proj : Project_Tree)
   is
      Proj_Type     : constant Project_Type := Proj.Root_Project;
      Why_Proj_File : constant String :=
         Generate_Why_Project_File (Proj_Type.Object_Dir.Display_Full_Name);
   begin
      --  Set the environment variable WHYLIB, if necessary, to indicate the
      --  placement for Why
      if not Ada.Environment_Variables.Exists (WHYLIB) then
         Ada.Environment_Variables.Set (WHYLIB, Why_Lib_Dir);
      end if;
      Call_Gprbuild (
         (1 => new String'("-P"),
          2 => new String'(Why_Proj_File),
          3 => new String'("--config=" & Gpr_Why_Cnf_File)));
   end Compute_VCs;

   -------------------------------
   -- Generate_Why_Project_File --
   -------------------------------

   function Generate_Why_Project_File (Source_Dir : String)
      return String
   is
      File : Ada.Text_IO.File_Type;
      Why_File_Name : constant String := "why.gpr";
   begin
      Ada.Text_IO.Create (File, Ada.Text_IO.Out_File, Why_File_Name);
      Ada.Text_IO.Put_Line (File, "project Why is");
      Ada.Text_IO.Put (File, "for Source_Dirs use (""");
      Ada.Text_IO.Put (File, Source_Dir);
      Ada.Text_IO.Put_Line (File, """);");
      Ada.Text_IO.Put_Line (File, "end Why;");
      Ada.Text_IO.Close (File);
      return Why_File_Name;
   end Generate_Why_Project_File;

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

   ---------------------------
   -- Make_Standard_Package --
   ---------------------------

   procedure Make_Standard_Package (Proj : Project_Tree)
   is
   begin
      pragma Unreferenced (Proj);
      Call_Exit_On_Failure
        (Command   => "gnat2why",
         Arguments =>
            (1 => new String'("-gnatd.H"),
             2 => new String'(Gpr_Ada_Cnf_File)),
         Verbose   => Verbose);
   end Make_Standard_Package;

   Tree      : Project_Tree;
   Proj_Type : Project_Type;
   Proj_Env  : Project_Environment_Access;

   procedure Read_Command_Line is
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
   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
   end Read_Command_Line;

   ----------------------
   -- Translate_To_Why --
   ----------------------

   procedure Translate_To_Why (Project_File : String)
   is
      Arguments : constant Argument_List :=
         (1 => new String'("-P"),
          2 => new String'(Project_File),
          3 => new String'("--subdirs=" & String (Subdir_Name)),
          4 => new String'("--config=" & Gpr_Ada_Cnf_File));
   begin
      if All_VCs then
         Call_Gprbuild (Arguments);
      else
         Call_Gprbuild
            (Arguments &
               (1 => new String'("-cargs:Ada"),
                2 => new String'("-gnatd.G")));
      end if;
   end Translate_To_Why;

   procedure Call_Altergo_Wrap (Proj : Project_Tree; File : Virtual_File);

   procedure Call_Altergo_Wrap (Proj : Project_Tree; File : Virtual_File) is
   begin
      Call_Altergo (Proj, File, Verbose, Report);
   end Call_Altergo_Wrap;

   procedure Iterate_Altergo is
     new Iter_Project_Source_Files (Call_Altergo_Wrap);

   --  begin processing for Gnatprove

begin
   Read_Command_Line;
   Initialize (Proj_Env);
   Set_Object_Subdir (Proj_Env.all, Subdir_Name);
   Tree.Load
     (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
      Proj_Env);
   Proj_Type := Root_Project (Tree);

   Compute_ALI_Information (Project_File.all);

   Translate_To_Why (Project_File.all);

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);

   Make_Standard_Package (Tree);

   Compute_VCs (Tree);
   Iterate_Altergo (Tree);
exception
   when Invalid_Project =>
      Ada.Text_IO.Put
        (Ada.Text_IO.Standard_Error,
         "Error: could not find project file: ");
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Project_File.all);
end Gnatprove;
