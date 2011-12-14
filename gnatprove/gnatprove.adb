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

with GNAT.Directory_Operations;
with GNAT.OS_Lib;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.VFS;      use GNATCOLL.VFS;
with GNATCOLL.Utils;    use GNATCOLL.Utils;

with String_Utils;      use String_Utils;
with System.OS_Lib;

procedure Gnatprove is

   type Gnatprove_Step is (GS_ALI, GS_Gnat2Why, GS_Why);

   function Step_Image (S : Gnatprove_Step) return String is
      (Int_Image (Gnatprove_Step'Pos (S) + 1));

   procedure Simple_Detection_Step;
   --  When no project file is given, but simple files, run gnat2why and
   --  nothing else

   function Final_Step return Gnatprove_Step is
     (case MMode is
       when GPM_Detect | GPM_Force => GS_Gnat2Why,
       when GPM_Check | GPM_Prove => GS_Why);

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
       Compiler_Args : in out String_Lists.List;
       Status        : out Integer);
   --  Call gprbuild with the given arguments

   procedure Compute_ALI_Information
      (Project_File : String;
       Status : out Integer);
   --  Compute ALI information for all source units, using gnatmake.

   procedure Compute_VCs (Proj : Project_Tree; Status : out Integer);
   --  Compute Verification conditions using Why, driven by gprbuild.

   procedure Execute_Step
      (Step         : Gnatprove_Step;
       Project_File : String;
       Proj         : Project_Tree);

   procedure Generate_Alfa_Report
     (Obj_Dir : String;
      Obj_Path  : File_Array);
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

   procedure Generate_Why3_Conf_File (Gnatprove_Subdir : String);

   procedure Translate_To_Why
      (Project_File : String;
       Status : out Integer);
   --  Translate all source units to Why, using gnat2why, driven by gprbuild.

   function Text_Of_Step (Step : Gnatprove_Step) return String;

   -------------------
   -- Call_Gprbuild --
   -------------------

   procedure Call_Gprbuild
      (Project_File  : String;
       Config_File   : String;
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
      Compiler_Args.Prepend ("-c");
      Compiler_Args.Prepend (Project_File);
      Compiler_Args.Prepend ("-P");
      Compiler_Args.Prepend ("--config=" & Config_File);

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
      Cur  : Cursor := First (Cargs_List);
   begin
      Args.Append ("-P");
      Args.Append (Project_File);
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("-U");
      Args.Append ("-gnatc");       --  only generate ALI
      Args.Append ("-gnatd.F");     --  ALFA section in ALI
      if Pedantic then
         Args.Append ("-gnatd.D");
      end if;

      if Force then
         Args.Append ("-f");
      end if;

      if not Verbose then
         Args.Append ("-q");
      end if;

      while Has_Element (Cur) loop
         Args.Append (Element (Cur));
         Next (Cur);
      end loop;

      --  Keep going after a compilation error in 'detect' and 'force' modes

      if MMode in GP_Alfa_Detection_Mode then
         Args.Append ("-k");
      end if;

      Call_With_Status
        (Command   => "gnatmake",
         Arguments => Args,
         Status    => Status,
         Verbose   => Verbose);
   end Compute_ALI_Information;

   -----------------
   -- Compute_VCs --
   -----------------

   procedure Compute_VCs
     (Proj   : Project_Tree;
      Status : out Integer)
   is
      use Ada.Environment_Variables;
      Proj_Type     : constant Project_Type := Proj.Root_Project;
      Obj_Dir       : constant String :=
         Proj_Type.Object_Dir.Display_Full_Name;
      Why_Proj_File : constant String :=
         Generate_Why_Project_File (Obj_Dir);
      Args          : String_Lists.List := String_Lists.Empty_List;
   begin
      Generate_Why3_Conf_File (Obj_Dir);
      if Timeout /= 0 then
         Args.Append ("--timeout");
         Args.Append (Int_Image (Timeout));
      end if;
      if Steps /= 0 then
         Args.Append ("--steps");
         Args.Append (Int_Image (Steps));
      end if;
      if Verbose then
         Args.Append ("--verbose");
      end if;
      Args.Append ("--report");
      case Report is
         when GPR_Fail =>
            Args.Append ("fail");

         when GPR_Verbose =>
            Args.Append ("all");

         when GPR_Detailed =>
            Args.Append ("detailed");

      end case;
      if Debug then
         Args.Append ("--debug");
      end if;
      if Force then
         Args.Append ("--force");
      end if;
      if Integer (Args.Length) > 0 then
         Args.Prepend ("-cargs:Why");
      end if;

      --  Always run gnatwhy3 on all files; it will detect itself if it is
      --  necessary to (re)do proofs

      Args.Prepend ("-f");

      Set ("TEMP", Obj_Dir);
      Set ("TMPDIR", Obj_Dir);
      Call_Gprbuild (Why_Proj_File, Gpr_Why_Cnf_File, Args, Status);
   end Compute_VCs;

   procedure Execute_Step
     (Step         : Gnatprove_Step;
      Project_File : String;
      Proj         : Project_Tree)
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
              and then MMode in GP_Alfa_Detection_Mode
            then
               Status := 0;
            end if;

         when GS_Gnat2Why =>
            Translate_To_Why (Project_File, Status);
            if Status /= 0
              and then MMode in GP_Alfa_Detection_Mode
            then
               Status := 0;
            end if;

         when GS_Why =>
            Compute_VCs (Proj, Status);

      end case;

      if Status /= 0 then
         Abort_With_Message
           ("gnatprove: error during " & Text_Of_Step (Step) & ", aborting.");
      end if;
   end Execute_Step;

   --------------------------
   -- Generate_Alfa_Report --
   --------------------------

   procedure Generate_Alfa_Report
     (Obj_Dir : String;
      Obj_Path  : File_Array)
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
         use System.OS_Lib;
      begin
         if Dirname = "" then
            return Filename;
         elsif Dirname (Dirname'Last) = Directory_Separator then
            return Dirname & Filename;
         else
            return Dirname & Directory_Separator & Filename;
         end if;
      end Append_To_Dir_Name;

      Alfa_Files_Wildcard : constant String :=
         Append_To_Dir_Name
           (Dirname  => Obj_Dir,
            Filename => "*.alfa");
      --  Alfa files for the current project. Other Alfa files are present in
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
        (Command   => "alfa_report",
         Arguments => (1 => new String'(Obj_Dir_Fn)),
         Verbose   => Verbose);

      if not Debug then
         GNAT.OS_Lib.Delete_File (Obj_Dir_Fn, Success);
      end if;

      if not Quiet then
         if MMode = GPM_Detect then
            Put_Line ("**********************************");
            Cat (File                  => Alfa_Report_File,
                 Cut_Non_Blank_Line_At => Max_Non_Blank_Lines);
            Put_Line ("**********************************");
            Put_Line ("Statistics above are logged in " & Alfa_Report_File);
         else
            Put_Line ("Statistics logged in " & Alfa_Report_File);
         end if;

         Put_Line
            ("(detailed info can be found in " & Alfa_Files_Wildcard & ")");
      end if;
   end Generate_Alfa_Report;

   ---------------------------
   -- Generate_Project_File --
   ---------------------------

   procedure Generate_Project_File
     (Filename     : String;
      Project_Name : String;
      Source_Dir   : String)
   is
      File : File_Type;
   begin
      Create (File, Out_File, Filename);
      Put (File, "project ");
      Put (File, Project_Name);
      Put_Line (File, " is");
      Put (File, "for Source_Dirs use (""");
      Put (File, Source_Dir);
      Put_Line (File, """);");
      Put (File, "end ");
      Put (File, Project_Name);
      Put_Line (File, ";");
      Close (File);
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

   -----------------------------
   -- Generate_Why3_Conf_File --
   -----------------------------

   procedure Generate_Why3_Conf_File (Gnatprove_Subdir : String)
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
      Put_Keyval ("loadpath", Gnatprove_Subdir);
      Put_Keyval ("magic", 8);
      Put_Keyval ("memlimit", 0);
      Put_Keyval ("running_provers_max", 2);
      Put_Keyval ("timelimit", 10);  --  Limit used when no explicit --timeout
      Start_Section ("prover alt-ergo");
      Put_Keyval ("command", "why3-cpulimit %t %m -s alt-ergo -proof %f");
      Put_Keyval ("driver",
                  Ada.Directories.Compose (Why3_Drivers_Dir,
                                           "alt_ergo_trunk.drv"));
      Put_Keyval ("name", "Alt-Ergo");
      Close (File);
   end Generate_Why3_Conf_File;

   Tree      : Project_Tree;
   Proj_Type : Project_Type;

   ---------------------------
   -- Simple_Detection_Step --
   ---------------------------

   procedure Simple_Detection_Step
   is
      use String_Lists;
      Cur      : Cursor := First (File_List);
      Carg_Cur : Cursor := First (Cargs_List);
      Args     : List := Empty_List;
      Status   : Integer;
   begin
      Ch_Dir_Create_If_Needed (String (Subdir_Name));
      Args.Append ("-gnatd.F");
      Args.Append ("-I");
      Args.Append (Stdlib_ALI_Dir);
      if MMode /= GPM_Prove then
         Args.Append ("-gnatd.G");
      end if;
      if MMode = GPM_Detect then
         Args.Append ("-gnatd.K");
      end if;
      if MMode = GPM_Force then
         Args.Append ("-gnatd.E");
      end if;
      if Pedantic then
         Args.Append ("-gnatd.D");
      end if;
      while Has_Element (Carg_Cur) loop
         Args.Append (Element (Carg_Cur));
         Next (Carg_Cur);
      end loop;
      while Has_Element (Cur) loop
         Args.Append ("../" & Element (Cur));
         Call_With_Status ("gnat2why", Args, Status, Verbose);
         Args.Delete_Last;
         Next (Cur);
      end loop;
      GNAT.Directory_Operations.Change_Dir ("..");
      Generate_Alfa_Report
         (String (Subdir_Name),
          (1 => Create_From_Base (Subdir_Name)));
   end Simple_Detection_Step;

   ------------------
   -- Text_Of_Step --
   ------------------

   function Text_Of_Step (Step : Gnatprove_Step) return String is
   begin
      case Step is
         when GS_ALI =>
            return "frame condition computation";

         when GS_Gnat2Why =>
            if MMode = GPM_Detect
              or else MMode = GPM_Force
            then
               return "detection of Alfa subprograms";
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
      Args.Append ("-k");
      if Call_Mode = GPC_Project_Files then
         declare
            Cur : Cursor := First (File_List);
         begin
            Args.Append ("-u");
            while Has_Element (Cur) loop
               Args.Append (Element (Cur));
               Next (Cur);
            end loop;
         end;
      else
         Args.Append ("-U");
      end if;
      Args.Append ("-cargs:Ada");
      Args.Append ("-I");
      Args.Append (Stdlib_ALI_Dir);
      if MMode /= GPM_Prove then
         Args.Append ("-gnatd.G");
      end if;
      if MMode = GPM_Detect then
         Args.Append ("-gnatd.K");
      end if;
      if MMode = GPM_Force then
         Args.Append ("-gnatd.E");
      end if;
      if Pedantic then
         Args.Append ("-gnatd.D");
      end if;
      while Has_Element (Cur) loop
         Args.Append (Element (Cur));
         Next (Cur);
      end loop;
      Call_Gprbuild (Project_File, Gpr_Ada_Cnf_File, Args, Status);
   end Translate_To_Why;

   --  begin processing for Gnatprove

begin
   Read_Command_Line;
   if Call_Mode = GPC_Only_Files then
      Simple_Detection_Step;
      GNAT.OS_Lib.OS_Exit (0);
   end if;

   Init (Tree);

   Proj_Type := Root_Project (Tree);

   declare
      Obj_Path : constant File_Array :=
         Object_Path (Proj_Type, Recursive => True);
   begin

      --  ??? Why version 2 only reads files in the current directory. As Why
      --  works in the object directory, this means that we only support a
      --  single object directory.
      --  Here we check that this is the case, and fail gracefully if not.

      if not (MMode = GPM_Detect) and then Obj_Path'Length > 1 then
         Abort_With_Message
            ("There is more than one object directory, aborting.");
      end if;

      if not (Call_Mode = GPC_Project_Files) then
         Execute_Step (GS_ALI, Project_File.all, Tree);
      end if;

      Execute_Step (GS_Gnat2Why, Project_File.all, Tree);

      Generate_Alfa_Report (Proj_Type.Object_Dir.Display_Full_Name, Obj_Path);

      if MMode in GP_Alfa_Detection_Mode then
         GNAT.OS_Lib.OS_Exit (0);
      end if;
   end;

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);

   Execute_Step (GS_Why, Project_File.all, Tree);

exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & Project_File.all);
end Gnatprove;
