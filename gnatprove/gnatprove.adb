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
with Ada.Strings;
with Ada.Strings.Fixed;
with Call;              use Call;
with Explanations;      use Explanations;
with String_Utils;      use String_Utils;

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.OS_Lib;       use GNAT.OS_Lib;
with GNAT.Strings;
with GNAT.Directory_Operations.Iteration;

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
   No_Proof     : aliased Boolean;
   --  True if --no-proof switch is present. Do not call Alt-Ergo.
   Alfa_Report  : aliased Boolean;
   --  True if --alfa-report switch is present. Pass option "-gnatd.K" to
   --  gnat2why.
   Force_Alfa   : aliased Boolean;
   --  True if --force-alfa switch is present. Issue errors on constructs not
   --  in Alfa, and warnings on constructs not yet implemented in GNATprove.
   --  Pass option "-gnatd.E" to gnat2why.
   Parallel     : aliased Integer;
   --  The number of parallel processes.
   Timeout      : aliased Integer;
   Steps        : aliased Integer;
   --  The Timeout and Step for Alt-Ergo

   Project_File : aliased GNAT.Strings.String_Access;
   --  The project file name, given with option -P

   Subdir_Name  : constant Filesystem_String := "gnatprove";
   WHYLIB       : constant String := "WHYLIB";
   Prefix       : constant String := Executable_Location;
   Lib_Dir      : constant String := Ada.Directories.Compose (Prefix, "lib");
   Why_Lib_Dir  : constant String := Ada.Directories.Compose (Lib_Dir, "why");
   Gpr_Cnf_Dir  : constant String :=
      Ada.Directories.Compose
        (Ada.Directories.Compose (Prefix, "share"),
         "gnatprove");
   Stdlib_ALI_Dir   : constant String :=
      Ada.Directories.Compose (Lib_Dir, "gnatprove");
   Gpr_Ada_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "gnat2why.cgpr");
   Gpr_Why_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "why.cgpr");
   Gpr_Altergo_Cnf_File : constant String :=
      Ada.Directories.Compose (Gpr_Cnf_Dir, "altergo.cgpr");
   Alfa_Report_File : constant String := "gnatprove.out";

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
       Compiler_Args : in out String_Lists.List);
   --  Call gprbuild with the given arguments

   procedure Compute_ALI_Information (Project_File : String);
   --  Compute ALI information for all source units, using gnatmake.

   procedure Compute_VCs (Proj : Project_Tree);
   --  Compute Verification conditions using Why, driven by gprbuild.

   procedure Generate_Alfa_Report
      (Proj_Type : Project_Type;
       Obj_Path : File_Array);
   --  Generate the Alfa report.

   procedure Generate_Project_File
      (Filename : String;
       Project_Name : String;
       Source_Dir : String);
   --  Generate project file at given place, with given name and source dir.

   function Generate_Why_Project_File (Source_Dir : String)
       return String;
   --  Generate project file with the given source dir. Write the file to disk
   --  and return the file name.

   function Generate_Altergo_Project_File (Source_Dir : String)
       return String;
   --  Generate project file with the given source dir. Write the file to disk
   --  and return the file name.

   procedure Make_Standard_Package (Proj : Project_Tree);
   --  Produce the file "_standard.mlw".

   procedure Prove_VCs (Proj : Project_Tree);
   --  Prove the VCs.

   procedure Report_VCs;
   --  Print error/info messages on VCs.

   procedure Translate_To_Why (Project_File : String);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.

   procedure Read_Command_Line;
   --  Parse command line and set up configuration.

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
       Compiler_Args : in out String_Lists.List)
   is
   begin
      if Verbose then
         Compiler_Args.Prepend ("-v");
      else
         Compiler_Args.Prepend ("-q");
      end if;
      if Parallel > 1 then
         Compiler_Args.Prepend ("-j" & Int_Image (Parallel));
      end if;
      Compiler_Args.Prepend ("-c");
      Compiler_Args.Prepend (Project_File);
      Compiler_Args.Prepend ("-P");
      Compiler_Args.Prepend ("--config=" & Config_File);

      Call_Exit_On_Failure
        (Command   => "gprbuild",
         Arguments => Compiler_Args,
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
                       4 => new String'("-U"),
                       5 => new String'("-gnatc"),      --  only generate ALI
                       6 => new String'("-gnatd.F")),   --  ALFA section in ALI
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
      Args          : String_Lists.List := String_Lists.Empty_List;
   begin
      --  Set the environment variable WHYLIB, if necessary, to indicate the
      --  placement for Why
      if not Ada.Environment_Variables.Exists (WHYLIB) then
         Ada.Environment_Variables.Set (WHYLIB, Why_Lib_Dir);
      end if;
      Call_Gprbuild (Why_Proj_File, Gpr_Why_Cnf_File, Args);
   end Compute_VCs;

   --------------------------
   -- Generate_Alfa_Report --
   --------------------------

   procedure Generate_Alfa_Report
      (Proj_Type : Project_Type;
       Obj_Path : File_Array)
   is
      use Ada.Text_IO;
      Obj_Dir_File : Ada.Text_IO.File_Type;
      Obj_Dir_Fn   : constant String :=
         Ada.Directories.Compose
            (Proj_Type.Object_Dir.Display_Full_Name,
             "gnatprove.alfad");
      Success      : aliased Boolean;
   begin
      Create (Obj_Dir_File, Out_File, Obj_Dir_Fn);
      for Index in Obj_Path'Range loop
         Put_Line (Obj_Dir_File, Obj_Path (Index).Display_Full_Name);
      end loop;
      Close (Obj_Dir_File);
      Call_Exit_On_Failure
        (Command   => "alfa_report",
         Arguments => (1 => new String'(Obj_Dir_Fn)),
         Verbose   => Verbose);
      Delete_File (Obj_Dir_Fn, Success);
      if Alfa_Report then
         Cat (Alfa_Report_File);
      end if;
   end Generate_Alfa_Report;

   ---------------------------
   -- Generate_Project_File --
   ---------------------------

   procedure Generate_Project_File
      (Filename : String;
       Project_Name : String;
       Source_Dir : String)
   is
      File : Ada.Text_IO.File_Type;
   begin
      Ada.Text_IO.Create (File, Ada.Text_IO.Out_File, Filename);
      Ada.Text_IO.Put (File, "project ");
      Ada.Text_IO.Put (File, Project_Name);
      Ada.Text_IO.Put_Line (File, " is");
      Ada.Text_IO.Put (File, "for Source_Dirs use (""");
      Ada.Text_IO.Put (File, Source_Dir);
      Ada.Text_IO.Put_Line (File, """);");
      Ada.Text_IO.Put (File, "end ");
      Ada.Text_IO.Put (File, Project_Name);
      Ada.Text_IO.Put_Line (File, ";");
      Ada.Text_IO.Close (File);
   end Generate_Project_File;

   -------------------------------
   -- Generate_Why_Project_File --
   -------------------------------

   function Generate_Why_Project_File (Source_Dir : String)
      return String
   is
      Why_File_Name : constant String := "why.gpr";
   begin
      Generate_Project_File (Why_File_Name, "Why", Source_Dir);
      return Why_File_Name;
   end Generate_Why_Project_File;

   -----------------------------------
   -- Generate_Altergo_Project_File --
   -----------------------------------

   function Generate_Altergo_Project_File (Source_Dir : String)
      return String
   is
      Altergo_Filename : constant String := "altergo.gpr";
   begin
      Generate_Project_File (Altergo_Filename, "Altergo", Source_Dir);
      return Altergo_Filename;
   end Generate_Altergo_Project_File;

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

   ---------------
   -- Prove_VCs --
   ---------------

   procedure Prove_VCs (Proj : Project_Tree)
   is
      use String_Lists;
      Proj_Type         : constant Project_Type := Proj.Root_Project;
      Altergo_Proj_File : constant String :=
         Generate_Altergo_Project_File
           (Proj_Type.Object_Dir.Display_Full_Name);
      Args              : List := Empty_List;
   begin
      if Timeout /= 0 then
         Args.Append ("--timeout=" & Int_Image (Timeout));
      end if;
      if Steps /= 0 then
         Args.Append ("--steps=" & Int_Image (Steps));
      end if;
      if Integer (Args.Length) > 0 then
         Args.Prepend ("-cargs:AltErgo");
      end if;

      Call_Gprbuild (Altergo_Proj_File, Gpr_Altergo_Cnf_File, Args);
   end Prove_VCs;

   Tree      : Project_Tree;
   Proj_Type : Project_Type;
   Proj_Env  : Project_Environment_Access;

   -----------------------
   -- Read_Command_Line --
   -----------------------

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

      Define_Switch
        (Config,
         Alfa_Report'Access,
         Long_Switch => "--alfa-report",
         Help => "Disable generation of VCs, only output Alfa information");

      Define_Switch
        (Config,
         Force_Alfa'Access,
         Long_Switch => "--force-alfa",
         Help => "Output errors on non-Alfa constructs, "
           & "and warnings on unimplemented ones");

      Define_Switch
        (Config,
         No_Proof'Access,
         Long_Switch => "--no-proof",
         Help => "Disable proof of VCs, only generate VCs");

      Define_Switch
         (Config, Timeout'Access,
          Long_Switch => "--timeout=",
          Help => "Set the timeout for Alt-Ergo in seconds (default is 10)");

      Define_Switch
         (Config, Steps'Access,
          Long_Switch => "--steps=",
          Help => "Set the maximum number of proof steps for Alt-Ergo");

      Define_Switch
         (Config, Parallel'Access,
          Long_Switch => "-j:",
          Help => "Set the number of parallel processes (default is 1)");

      Define_Switch (Config, Project_File'Access,
                     "-P:",
                     Help => "The name of the project file");

      Getopt (Config);
      if Project_File.all = "" then
         Abort_With_Message ("No project file given, aborting.");
      end if;
   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
   end Read_Command_Line;

   ----------------
   -- Report_VCs --
   ----------------

   procedure Report_VCs
   is

      procedure Report_VC
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean);
      --  Report a single VC

      ---------------
      -- Report_VC --
      ---------------
      procedure Report_VC
        (Item    : String;
         Index   : Positive;
         Quit    : in out Boolean)
      is
         Base_Name : constant String :=
            Ada.Directories.Base_Name (Item);
         Rgo_Name : constant String := Base_Name & ".rgo";
         Xpl_Name : constant String := Base_Name & ".xpl";
         Rgo_File : Ada.Text_IO.File_Type;
         Proved : Boolean;
      begin
         pragma Unreferenced (Index);
         pragma Unreferenced (Quit);

         Ada.Text_IO.Open (Rgo_File, Ada.Text_IO.In_File, Rgo_Name);
         if Ada.Strings.Fixed.Index
              (Ada.Text_IO.Get_Line (Rgo_File), "Valid") > 0 then
            Proved := True;
         else
            Proved := False;
         end if;
         Ada.Text_IO.Close (Rgo_File);

         if not Proved or else Report then
            Print_Error_Msg (Get_VC_Explanation (Xpl_Name), Proved);
         end if;
      end Report_VC;

      procedure Iterate is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
           (Action => Report_VC);

   begin
      Iterate (Path => "*package_po*.why");
   end Report_VCs;

   ----------------------
   -- Translate_To_Why --
   ----------------------

   procedure Translate_To_Why (Project_File : String)
   is
      use String_Lists;
      Args : String_Lists.List := Empty_List;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("-U");
      Args.Append ("-cargs:Ada");
      Args.Append ("-I");
      Args.Append (Stdlib_ALI_Dir);
      if not All_VCs then
         Args.Append ("-gnatd.G");
      end if;
      if Alfa_Report then
         Args.Append ("-gnatd.K");
      end if;
      if Force_Alfa then
         Args.Append ("-gnatd.E");
      end if;
      Call_Gprbuild (Project_File, Gpr_Ada_Cnf_File, Args);
   end Translate_To_Why;

   GNAT_Version : GNAT.Strings.String_Access;
   --  begin processing for Gnatprove

begin
   Read_Command_Line;
   Initialize (Proj_Env);
   Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
   Set_Object_Subdir (Proj_Env.all, Subdir_Name);
   Tree.Load
     (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
      Proj_Env);
   Proj_Type := Root_Project (Tree);

   declare
      Obj_Path : constant File_Array :=
         Object_Path (Proj_Type, Recursive => True);
   begin

      --  ??? Why version 2 only reads files in the current directory. As Why
      --  works in the object directory, this means that we only support a
      --  single object directory.
      --  Here we check that this is the case, and fail gracefully if not.

      if not Alfa_Report and then Obj_Path'Length > 1 then
         Abort_With_Message
            ("There is more than one object directory, aborting.");
      end if;

      Compute_ALI_Information (Project_File.all);

      Translate_To_Why (Project_File.all);

      Generate_Alfa_Report (Proj_Type, Obj_Path);
      if Alfa_Report then
         GNAT.OS_Lib.OS_Exit (0);
      end if;
   end;

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);
   Make_Standard_Package (Tree);
   Compute_VCs (Tree);

   if not No_Proof then
      Prove_VCs (Tree);
      Report_VCs;
   end if;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & Project_File.all);
end Gnatprove;
