------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                            G N A T P R O V E                             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Directories;
with Ada.Environment_Variables;
with Ada.Strings.Unbounded;
with Ada.Text_IO;       use Ada.Text_IO;
with Call;              use Call;
with Configuration;     use Configuration;

with GNAT.OS_Lib;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.VFS;      use GNATCOLL.VFS;
with GNATCOLL.Utils;    use GNATCOLL.Utils;

with String_Utils;      use String_Utils;
with GNAT.Strings;      use GNAT.Strings;

procedure Gnatprove is

   type Gnatprove_Step is (GS_ALI, GS_Gnat2Why, GS_Why);

   function Step_Image (S : Gnatprove_Step) return String is
      (Int_Image (Gnatprove_Step'Pos (S) + 1));

   function Final_Step return Gnatprove_Step is
     (case MMode is
       when GPM_Check | GPM_Flow => GS_Gnat2Why,
       when GPM_Prove | GPM_All => GS_Why);

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
       Parallel      : Integer;
       Compiler_Args : in out String_Lists.List;
       Status        : out Integer);
   --  Call gprbuild with the given arguments. Pass in explicitly a number of
   --  parallel processes, so that we can force sequential execution when
   --  needed.

   procedure Compute_ALI_Information
      (Project_File : String;
       Status : out Integer);
   --  Compute ALI information for all source units, using gnatmake.

   procedure Compute_VCs (Proj     : Project_Tree;
                          Obj_Path : File_Array;
                          Status   : out Integer);
   --  Compute Verification conditions using Why, driven by gprbuild.

   procedure Execute_Step
      (Step         : Gnatprove_Step;
       Project_File : String;
       Proj         : Project_Tree;
       Obj_Path     : File_Array);

   procedure Generate_SPARK_Report
     (Obj_Dir : String;
      Obj_Path  : File_Array);
   --  Generate the SPARK report.

   procedure Generate_Project_File
      (Filename     : String;
       Project_Name : String;
       Source_Files : File_Array_Access);
   --  Generate project file at given place, with given name and source files.

   function Generate_Why_Project_File (Proj : Project_Type)
                                       return String;
   --  Generate project file for Why3 phase. Write the file to disk
   --  and return the file name.

   procedure Generate_Why3_Conf_File
     (Gnatprove_Subdir : String;
      Obj_Path         : File_Array);

   procedure Translate_To_Why
      (Project_File : String;
       Status : out Integer);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.

   function Text_Of_Step (Step : Gnatprove_Step) return String;

   procedure Set_Gnat2why_Env_Var;
   --  Set the environment variable which passes some options to gnat2why

   procedure Unset_Gnat2why_Env_Var;
   --  unset the environment variable for gnat2why
   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
       Parallel      : Integer;
       Compiler_Args : in out String_Lists.List;
       Status        : out Integer)
   is
   begin
      if Verbose then
         Compiler_Args.Prepend ("-v");
      else
         Compiler_Args.Prepend ("-q");
         Compiler_Args.Prepend ("-ws");
      end if;
      if Parallel > 1 then
         Compiler_Args.Prepend ("-j" & Int_Image (Parallel));
      end if;
      if Force then
         Compiler_Args.Prepend ("-f");
      end if;
      if All_Projects then
         Compiler_Args.Prepend ("-U");
      end if;
      Compiler_Args.Prepend ("-c");
      if Project_File /= "" then
         Compiler_Args.Prepend (Project_File);
         Compiler_Args.Prepend ("-P");
      end if;
      if Config_File /= "" then
         Compiler_Args.Prepend ("--config=" & Config_File);
      end if;

      if Debug then
         Compiler_Args.Prepend ("-dn");
      end if;

      Call_With_Status
        (Command   => "gprbuild",
         Arguments => Compiler_Args,
         Status    => Status,
         Verbose   => Verbose);
   end Call_Gprbuild;

   -----------------------------
   -- Compute_ALI_Information --
   -----------------------------

   procedure Compute_ALI_Information
     (Project_File : String;
      Status       : out Integer)
   is
      use String_Lists;
      Args : List := Empty_List;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("--restricted-to-languages=ada");
      Args.Append ("--no-object-check");

      for Arg of Cargs_List loop
         Args.Append (Arg);
      end loop;

      --  Keep going after a compilation error in 'check' mode

      if MMode = GPM_Check then
         Args.Append ("-k");
      end if;

      for File of File_List loop
         Args.Append (File);
      end loop;

      Args.Append ("-cargs:Ada");
      Args.Append ("-gnatc");       --  only generate ALI
      Args.Append ("-gnatd.G");     --  ALI file generation
      if Pedantic then
         Args.Append ("-gnatd.D");
      end if;

      Call_Gprbuild (Project_File,
                     Gpr_Frames_Cnf_File,
                     Parallel,
                     Args,
                     Status);
   end Compute_ALI_Information;

   -----------------
   -- Compute_VCs --
   -----------------

   procedure Compute_VCs
     (Proj      : Project_Tree;
      Obj_Path  : File_Array;
      Status    : out Integer)
   is
      use Ada.Environment_Variables;
      Proj_Type     : constant Project_Type := Proj.Root_Project;
      Obj_Dir       : constant String :=
         Proj_Type.Object_Dir.Display_Full_Name;
      Why_Proj_File : constant String :=
         Generate_Why_Project_File (Proj_Type);
      Args          : String_Lists.List := String_Lists.Empty_List;
   begin
      Generate_Why3_Conf_File (Obj_Dir, Obj_Path);
      if Timeout /= 0 then
         Args.Append ("--timeout");
         Args.Append (Int_Image (Timeout));
      end if;

      --  The steps option is passed to alt-ergo via the why3.conf file. We
      --  still need to pass it to gnatwhy3 as well so that it is aware of the
      --  value of that switch.

      if Steps /= 0 then
         Args.Append ("--steps");
         Args.Append (Int_Image (Steps));
      end if;
      if Verbose then
         Args.Append ("--verbose");
      elsif Quiet then
         Args.Append ("--quiet");
      end if;
      Args.Append ("--report");
      case Report is
         when GPR_Fail =>
            Args.Append ("fail");

         when GPR_Verbose =>
            Args.Append ("all");

         when GPR_Statistics =>
            Args.Append ("statistics");

      end case;
      if Debug then
         Args.Append ("--debug");
      end if;
      if Force then
         Args.Append ("--force");
      end if;
      if Proof /= Then_Split then
         Args.Append ("--proof");
         Args.Append (To_String (Proof));
      end if;
      if IDE_Progress_Bar then
         Args.Append ("--ide-progress-bar");
      end if;
      if Show_Tag then
         Args.Append ("--show-tag");
      end if;
      if Parallel > 1 then
         Args.Append ("-j");
         Args.Append (Int_Image (Parallel));
      end if;
      if Limit_Line /= null and then Limit_Line.all /= "" then
         Args.Append ("--limit-line");
         Args.Append (Limit_Line.all);
      end if;
      if Limit_Subp /= null and then Limit_Subp.all /= "" then
         Args.Append ("--limit-subp");
         Args.Append (Limit_Subp.all);
      end if;
      if Alter_Prover /= null and then Alter_Prover.all /= "" then
         Args.Append ("--prover");
         Args.Append (Alter_Prover.all);
      end if;
      if Integer (Args.Length) > 0 then
         Args.Prepend ("-cargs:Why");
      end if;

      --  Always run gnatwhy3 on all files; it will detect itself if it is
      --  necessary to (re)do proofs

      Args.Prepend ("-f");

      if Only_Given then
         for File of File_List loop
            Args.Prepend
              (File (File'First .. File'Last - 4) & "__package.mlw");
         end loop;
         Args.Prepend ("-u");
      end if;

      --  Force sequential execution of gprbuild, so that gnatwhy3 can run
      --  prover in parallel.

      Set ("TEMP", Obj_Dir);
      Set ("TMPDIR", Obj_Dir);
      Call_Gprbuild (Why_Proj_File,
                     Gpr_Why_Cnf_File,
                     Parallel      => 1,
                     Compiler_Args => Args,
                     Status        => Status);
   end Compute_VCs;

   procedure Execute_Step
     (Step         : Gnatprove_Step;
      Project_File : String;
      Proj         : Project_Tree;
      Obj_Path     : File_Array)
   is
      Status : Integer;

   begin
      if not Quiet then
         Put_Line ("Phase " & Step_Image (Step)
                   & " of " & Step_Image (Final_Step)
                   & ": " & Text_Of_Step (Step) & " ...");
      end if;

      case Step is
         when GS_ALI =>
            Compute_ALI_Information (Project_File, Status);
            if Status /= 0
              and then MMode = GPM_Check
            then
               Status := 0;
            end if;

         when GS_Gnat2Why =>
            Translate_To_Why (Project_File, Status);
            if Status /= 0
              and then MMode = GPM_Check
            then
               Status := 0;
            end if;

         when GS_Why =>
            Compute_VCs (Proj,  Obj_Path, Status);

      end case;

      if Status /= 0 then
         Abort_With_Message
           ("gnatprove: error during " & Text_Of_Step (Step) & ", aborting.");
      end if;
   end Execute_Step;

   ---------------------------
   -- Generate_SPARK_Report --
   ---------------------------

   procedure Generate_SPARK_Report
     (Obj_Dir  : String;
      Obj_Path : File_Array)
   is
      Obj_Dir_File : File_Type;
      Obj_Dir_Fn   : constant String :=
         Ada.Directories.Compose
            (Obj_Dir,
             "gnatprove.alfad");

      function Append_To_Dir_Name (Dirname, Filename : String) return String;

      ------------------------
      -- Append_To_Dir_Name --
      ------------------------

      function Append_To_Dir_Name (Dirname, Filename : String) return String is
         use GNAT.OS_Lib;
      begin
         if Dirname = "" then
            return Filename;
         elsif Dirname (Dirname'Last) = Directory_Separator then
            return Dirname & Filename;
         else
            return Dirname & Directory_Separator & Filename;
         end if;
      end Append_To_Dir_Name;

      SPARK_Files_Wildcard : constant String :=
         Append_To_Dir_Name
           (Dirname  => Obj_Dir,
            Filename => "*.alfa");
      --  SPARK files for the current project. Other SPARK files are present in
      --  object directories of sub-projects, although we do not mention them
      --  in the message below.

      Success : Boolean;

   begin
      Create (Obj_Dir_File, Out_File, Obj_Dir_Fn);
      for Index in Obj_Path'Range loop
         Put_Line
            (Obj_Dir_File,
             Obj_Path (Index).Display_Full_Name);
      end loop;
      Close (Obj_Dir_File);

      Call_Exit_On_Failure
        (Command   => "spark_report",
         Arguments => (1 => new String'(Obj_Dir_Fn)),
         Verbose   => Verbose);

      if not Debug then
         GNAT.OS_Lib.Delete_File (Obj_Dir_Fn, Success);
      end if;

      if not Quiet then
         Put_Line ("Statistics logged in " & SPARK_Report_File (Obj_Dir));
         Put_Line
           ("(detailed info can be found in " & SPARK_Files_Wildcard & ")");
      end if;
   end Generate_SPARK_Report;

   ---------------------------
   -- Generate_Project_File --
   ---------------------------

   procedure Generate_Project_File
     (Filename     : String;
      Project_Name : String;
      Source_Files : File_Array_Access)
   is
      File      : File_Type;
      Follow_Up : Boolean := False;
   begin
      Create (File, Out_File, Filename);
      Put (File, "project ");
      Put (File, Project_Name);
      Put_Line (File, " is");
      Put_Line (File, "for Source_Files use (");

      for F of Source_Files.all loop
         if Follow_Up then
            Put_Line (File, ",");
         end if;
         Follow_Up := True;
         Put (File, "   """ & F.Display_Base_Name & """");
      end loop;
      Put_Line (File, ");");
      Put (File, "end ");
      Put (File, Project_Name);
      Put_Line (File, ";");
      Close (File);
   end Generate_Project_File;

   -------------------------------
   -- Generate_Why_Project_File --
   -------------------------------

   function Generate_Why_Project_File (Proj : Project_Type)
                                       return String
   is
      Why_File_Name : constant String := "why.gpr";
   begin
      Generate_Project_File (Why_File_Name,
                             "Why",
                             Proj.Library_Files (ALI_Ext => "__package.mlw"));
      return Why_File_Name;
   end Generate_Why_Project_File;

   -----------------------------
   -- Generate_Why3_Conf_File --
   -----------------------------

   procedure Generate_Why3_Conf_File (Gnatprove_Subdir : String;
                                      Obj_Path         : File_Array)
   is
      File : File_Type;
      Filename : constant String :=
         Ada.Directories.Compose (Gnatprove_Subdir, "why3.conf");

      procedure Put_Keyval (Key : String; Value : String);
      procedure Put_Keyval (Key : String; Value : Integer);
      procedure Start_Section (Section : String);

      ----------------
      -- Put_Keyval --
      ----------------

      procedure Put_Keyval (Key : String; Value : String)
      is
         use Ada.Strings.Unbounded;
         Value_Unb : Unbounded_String := To_Unbounded_String (Value);
      begin
         Replace (Value_Unb, "\", "\\");
         Put (File, Key);
         Put (File, " = """);
         Put (File, To_String (Value_Unb));
         Put_Line (File, """");
      end Put_Keyval;

      procedure Put_Keyval (Key : String; Value : Integer)
      is
      begin
         Put (File, Key);
         Put (File, " = ");
         Put_Line (File, Int_Image (Value));
      end Put_Keyval;

      -------------------
      -- Start_Section --
      -------------------

      procedure Start_Section (Section : String)
      is
      begin
         Put (File, "[");
         Put (File, Section);
         Put_Line (File, "]");
      end Start_Section;

      --  begin processing for Generate_Why3_Conf_File
   begin
      Create (File, Out_File, Filename);
      Start_Section ("main");
      Put_Keyval ("loadpath", Ada.Directories.Compose (Why3_Dir, "theories"));
      Put_Keyval ("loadpath", Ada.Directories.Compose (Why3_Dir, "modules"));
      Put_Keyval ("loadpath", Stdlib_Dir);
      Put_Keyval ("loadpath", Theories_Dir);
      for File of Obj_Path loop
         Put_Keyval ("loadpath", File.Display_Full_Name);
      end loop;
      Put_Keyval ("magic", 14);
      Put_Keyval ("memlimit", 0);
      Put_Keyval ("running_provers_max", 2);
      Start_Section ("prover");
      declare
         Altergo_Command : constant String :=
           "why3-cpulimit %t %m -s alt-ergo %f";
      begin
         if Steps /= 0 then
            Put_Keyval ("command",
                        Altergo_Command & " -steps " & Int_Image (Steps));
         else
            Put_Keyval ("command", Altergo_Command);
         end if;
      end;
      Put_Keyval ("driver",
                  Ada.Directories.Compose (Why3_Drivers_Dir,
                                           "alt_ergo.drv"));
      Put_Keyval ("name", "Alt-Ergo");
      Put_Keyval ("shortcut", "altergo");
      Put_Keyval ("version", "0.94");
      Close (File);
   end Generate_Why3_Conf_File;

   --------------------------
   -- Set_Gnat2why_Env_Var --
   --------------------------

   procedure Set_Gnat2why_Env_Var
   is
      use Ada.Strings.Unbounded;
      Val : Unbounded_String := Null_Unbounded_String;
   begin
      if Debug then
         Append (Val, " flow_dump_graphs");
      end if;
      case MMode is
         when GPM_Check =>
            Append (Val, " check_mode");
         when GPM_Flow | GPM_All =>
            Append (Val, " flow_analysis_mode");
         when GPM_Prove =>
            null;
      end case;
      if Pedantic then
         Append (Val, " strict_mode");
      end if;
      Ada.Environment_Variables.Set (Name  => GNAT2Why_Var,
                                     Value => To_String (Val));
   end Set_Gnat2why_Env_Var;

   ------------------
   -- Text_Of_Step --
   ------------------

   function Text_Of_Step (Step : Gnatprove_Step) return String is
   begin
      case Step is
         when GS_ALI =>
            return "frame condition computation";

         when GS_Gnat2Why =>
            if MMode = GPM_Check then
               return "detection of SPARK subprograms";
            else
               return "translation to intermediate language";
            end if;

         when GS_Why =>
            return "generation and proof of VCs";

      end case;
   end Text_Of_Step;

   ----------------------
   -- Translate_To_Why --
   ----------------------

   procedure Translate_To_Why
      (Project_File : String;
       Status : out Integer)
   is
      use String_Lists;
      Cur    : Cursor := First (Cargs_List);
      Args   : String_Lists.List := Empty_List;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("--restricted-to-languages=ada");
      for File of File_List loop
         Args.Append (File);
      end loop;
      Args.Append ("-cargs:Ada");
      Args.Append ("-gnatc");       --  No object file generation
      Args.Append ("-I");
      Args.Append (Stdlib_ALI_Dir);
      if Show_Tag then
         Args.Append ("-gnatw.d"); -- generation of unique tag
      end if;
      while Has_Element (Cur) loop
         Args.Append (Element (Cur));
         Next (Cur);
      end loop;
      Set_Gnat2why_Env_Var;
      Call_Gprbuild (Project_File,
                     Gpr_Translataion_Cnf_File,
                     Parallel,
                     Args,
                     Status);
      Unset_Gnat2why_Env_Var;
   end Translate_To_Why;

   ----------------------------
   -- Unset_Gnat2why_Env_Var --
   ----------------------------

   procedure Unset_Gnat2why_Env_Var is
   begin
      Ada.Environment_Variables.Clear (GNAT2Why_Var);
   end Unset_Gnat2why_Env_Var;

   Tree      : Project_Tree;
   --  GNAT project tree

   Proj_Type : Project_Type;
   --  GNAT project

--  Start processing for Gnatprove

begin
   Read_Command_Line (Tree);

   Proj_Type := Root_Project (Tree);

   declare
      Obj_Path : constant File_Array :=
        Object_Path (Proj_Type, Recursive => True);
   begin
      Execute_Step (GS_ALI, Project_File.all, Tree, Obj_Path);
      Execute_Step (GS_Gnat2Why, Project_File.all, Tree, Obj_Path);

      Generate_SPARK_Report (Proj_Type.Object_Dir.Display_Full_Name, Obj_Path);

      if MMode in GPM_Check | GPM_Flow then
         GNAT.OS_Lib.OS_Exit (0);
      end if;
      Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);
      Execute_Step (GS_Why, Project_File.all, Tree, Obj_Path);
   end;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & Project_File.all);
end Gnatprove;
