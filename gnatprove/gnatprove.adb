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

with GNAT.Directory_Operations.Iteration;
with GNAT.OS_Lib;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.VFS;      use GNATCOLL.VFS;

with Configuration;     use Configuration;

with Ada.Text_IO;

procedure Gnatprove is

   type Gnatprove_Step is (GS_ALI, GS_Gnat2Why, GS_Why, GS_AltErgo);

   Skip_Rest    : Boolean := False;
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

   procedure Prove_VCs (Proj : Project_Tree; Status : out Integer);
   --  Prove the VCs.

   procedure Report_VCs;
   --  Print error/info messages on VCs.

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
       Status : out Integer)
   is
      Args          : String_Lists.List := String_Lists.Empty_List;
   begin
      Args.Append ("-P");
      Args.Append (Project_File);
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("-U");
      Args.Append ("-gnatc");       --  only generate ALI
      Args.Append ("-gnatd.F");     --  ALFA section in ALI
      if Force then
         Args.Append ("-f");
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
      (Proj : Project_Tree;
       Status : out Integer)
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
      Call_Gprbuild (Why_Proj_File, Gpr_Why_Cnf_File, Args, Status);
   end Compute_VCs;

   procedure Execute_Step
      (Step         : Gnatprove_Step;
       Project_File : String;
       Proj         : Project_Tree)
   is
      use Ada.Text_IO;
      Status : Integer;
   begin
      if Skip_Rest then
         Put (Standard_Error, "gnatprove: skipped ");
         Put_Line (Standard_Error, Text_Of_Step (Step));
         return;
      end if;
      case Step is
         when GS_ALI =>
            Compute_ALI_Information (Project_File, Status);

         when GS_Gnat2Why =>
            Translate_To_Why (Project_File, Status);

         when GS_Why =>
            Compute_VCs (Proj, Status);

         when GS_AltErgo =>
            Prove_VCs (Proj, Status);
            Report_VCs;

      end case;
      if Status /= 0 then
         Skip_Rest := True;
         Put (Standard_Error, "gnatprove: error during ");
         Put_Line (Standard_Error, Text_Of_Step (Step));
      end if;
   end Execute_Step;

   --------------------------
   -- Generate_Alfa_Report --
   --------------------------

   procedure Generate_Alfa_Report
      (Proj_Type : Project_Type;
       Obj_Path : File_Array)
   is
      Obj_Dir_File : Ada.Text_IO.File_Type;
      Obj_Dir_Fn   : constant String :=
         Ada.Directories.Compose
            (Proj_Type.Object_Dir.Display_Full_Name,
             "gnatprove.alfad");
      Success      : aliased Boolean;

   begin
      Ada.Text_IO.Create (Obj_Dir_File, Ada.Text_IO.Out_File, Obj_Dir_Fn);
      for Index in Obj_Path'Range loop
         Ada.Text_IO.Put_Line
            (Obj_Dir_File,
             Obj_Path (Index).Display_Full_Name);
      end loop;
      Ada.Text_IO.Close (Obj_Dir_File);

      Call_Exit_On_Failure
        (Command   => "alfa_report",
         Arguments => (1 => new String'(Obj_Dir_Fn)),
         Verbose   => Verbose);
      if not Debug then
         GNAT.OS_Lib.Delete_File (Obj_Dir_Fn, Success);
      end if;

      if Mode = GPM_Detect
        and then not Quiet
      then
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

   procedure Prove_VCs (Proj : Project_Tree; Status : out Integer)
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

      Call_Gprbuild (Altergo_Proj_File, Gpr_Altergo_Cnf_File, Args, Status);
   end Prove_VCs;

   Tree      : Project_Tree;
   Proj_Type : Project_Type;

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

   ------------------
   -- Text_Of_Step --
   ------------------

   function Text_Of_Step (Step : Gnatprove_Step) return String
   is
   begin
      case Step is
         when GS_ALI =>
            return "frame condition computation";

         when GS_Gnat2Why =>
            return "translation to intermediate language";

         when GS_Why =>
            return "generation of VCs";

         when GS_AltErgo =>
            return "proof of VCs";
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
      Args   : String_Lists.List := Empty_List;
   begin
      Args.Append ("--subdirs=" & String (Subdir_Name));
      Args.Append ("-U");
      Args.Append ("-k");
      Args.Append ("-cargs:Ada");
      Args.Append ("-I");
      Args.Append (Stdlib_ALI_Dir);
      if Mode /= GPM_Prove then
         Args.Append ("-gnatd.G");
      end if;
      if Mode = GPM_Detect then
         Args.Append ("-gnatd.K");
      end if;
      if Mode = GPM_Force then
         Args.Append ("-gnatd.E");
      end if;
      Call_Gprbuild (Project_File, Gpr_Ada_Cnf_File, Args, Status);
   end Translate_To_Why;

   --  begin processing for Gnatprove

begin
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

      if not (Mode = GPM_Detect) and then Obj_Path'Length > 1 then
         Abort_With_Message
            ("There is more than one object directory, aborting.");
      end if;

      Execute_Step (GS_ALI, Project_File.all, Tree);

      Execute_Step (GS_Gnat2Why, Project_File.all, Tree);

      Generate_Alfa_Report (Proj_Type, Obj_Path);
      if Mode = GPM_Detect then
         GNAT.OS_Lib.OS_Exit (0);
      end if;
   end;

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);
   Make_Standard_Package (Tree);

   Execute_Step (GS_Why, Project_File.all, Tree);

   if not No_Proof then
      Execute_Step (GS_AltErgo, Project_File.all, Tree);
   end if;
exception
   when Invalid_Project =>
      Abort_With_Message
         ("Error while loading project file: " & Project_File.all);
end Gnatprove;
