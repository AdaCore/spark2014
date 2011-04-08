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

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Directory_Operations.Iteration;
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
   All_VCs      : aliased Boolean;
   Project_File : aliased GNAT.Strings.String_Access;

   Subdir_Name  : constant Filesystem_String := "gnatprove";
   WHYLIB       : constant String := "WHYLIB";
   Why_Lib_Dir  : constant String := "lib/why";
   Main_Suffix  : constant String := "__package";

   procedure Call_Altergo (Proj : Project_Tree; File : Virtual_File);
   --  Call Alt-Ergo on all VC files that correspond to a given source file of
   --  a project

   procedure Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Timeout     : Natural);
   --  Call Altergo on a single File. Produce a file containing the result of
   --  the run with name Result_File. Don't take more time than the given
   --  Timeout in seconds.

   procedure Call_Exit_On_Failure
     (Command : String;
      Arguments : Argument_List);
   --  Call the given command using the given argument list.
   --  Free all argument access values
   --  If the command exit status is not 0, print its output and exit.

   procedure Call_Gnatmake (Project_File : String);
   --  Call gnatmake using the given project file.

   procedure Call_Gnat2Why
      (Proj     : Project_Tree;
       File     : Virtual_File;
       Inc_Args : Argument_List);
   --  Call gnat2why on a single source file of a project. The Inc_Args is an
   --  array that contains the include arguments that are necessary for the
   --  call to gnat2why

   procedure Call_Why (Proj : Project_Tree; File : Virtual_File);
   --  Call why on all the generated files that belong to a certain file
   --  in a project.
   --  example: if File is "example.adb", we call why on file
   --  "example__package.why".

   procedure Cat
      (Files   : Argument_List;
       Target  : String;
       Success : out Boolean);
   --  Cat all the Files together into the Target.

   generic
      with procedure Action (Proj : Project_Tree; File : Virtual_File);
   procedure Iter_Project_Source_Files (Proj : Project_Tree);
   --  Iterate over all source files of a project.

   ------------------
   -- Call_Altergo --
   ------------------

   procedure Call_Altergo (Proj : Project_Tree; File : Virtual_File) is
      pragma Unreferenced (Proj);

      Base : constant String := Ada.Directories.Base_Name (+Base_Name (File));

      procedure Call_AltErgo_On_Vc
        (Item  : String;
         Index : Positive;
         Quit : in out Boolean);
      --  Call Altergo on the VC that corresponds to the file
      --  'Item'; take into account the context file.

      ------------------------
      -- Call_AltErgo_On_Vc --
      ------------------------

      procedure Call_AltErgo_On_Vc
        (Item  : String;
         Index : Positive;
         Quit : in out Boolean)
      is
         pragma Unreferenced (Index);
         Target : constant String := "new.why";
         Success : aliased Boolean;
         Base_Of_VC : constant String :=
            Ada.Directories.Base_Name (Item);
      begin
         Delete_File (Target, Success);
         Cat (Files =>
               (1 => new String'(Base & Main_Suffix & "_ctx.why"),
                2 => new String'(Item)),
              Target => Target,
              Success => Success);
         --  ??? use 10 as timeout for now
         Call_AltErgo_On_File (Target, Base_Of_VC & ".rgo", 10);
         Quit := not Success;
         Delete_File (Target, Success);
      end Call_AltErgo_On_Vc;

      procedure Iterate is new
         GNAT.Directory_Operations.Iteration.Wildcard_Iterator
           (Action => Call_AltErgo_On_Vc);

      --  beginning of processing for Call_Altergo

   begin
      Iterate (Path => Base & Main_Suffix & "_po*.why");
   end Call_Altergo;

   --------------------------
   -- Call_AltErgo_On_File --
   --------------------------

   procedure Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Timeout     : Natural) is
   begin
      if Verbose then
         Ada.Text_IO.Put_Line ("calling Alt-ergo on " & File);
      end if;

      declare
         Status : aliased Integer;
         S  : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => "why-cpulimit",
               Arguments =>
                 ((1 => new String'(Natural'Image (Timeout)),
                   2 => new String'("alt-ergo"),
                   3 => new String'(File))),
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
         FT : Ada.Text_IO.File_Type;

      begin
         Ada.Text_IO.Create (FT, Ada.Text_IO.Out_File, Result_File);

         if Status /= 0 or else S'Length = 0 then
            Ada.Text_IO.Put (FT, "File """);
            Ada.Text_IO.Put (FT, File);
            Ada.Text_IO.Put_Line (FT, """:Failure or Timeout");

         else
            Ada.Text_IO.Put (FT, S);
         end if;

         Ada.Text_IO.Close (FT);
      end;
   end Call_AltErgo_On_File;

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List)
   is
      Status : aliased Integer;

      procedure Print_Command_Line;
      --  print the command line for debug purposes

      ------------------------
      -- Print_Command_Line --
      ------------------------

      procedure Print_Command_Line is
      begin
         Ada.Text_IO.Put (Command);

         for Index in Arguments'Range loop
            declare
               S : constant String_Access := Arguments (Index);
            begin
               Ada.Text_IO.Put (" ");
               Ada.Text_IO.Put (S.all);
            end;
         end loop;
      end Print_Command_Line;

   begin
      if Verbose then
         Print_Command_Line;
         Ada.Text_IO.Put_Line ("");
      end if;

      declare
         S : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => Command,
               Arguments => Arguments,
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
      begin
         if Status /= 0 then
            Print_Command_Line;
            Ada.Text_IO.Put_Line (" failed.");
            Ada.Text_IO.Put (S);
            GNAT.OS_Lib.OS_Exit (1);
         end if;

         for Index in Arguments'Range loop
            declare
               S : String_Access := Arguments (Index);
            begin
               Free (S);
            end;
         end loop;
      end;
   end Call_Exit_On_Failure;

   -------------------
   -- Call_Gnatmake --
   -------------------

   procedure Call_Gnatmake (Project_File : String) is
   begin
      Call_Exit_On_Failure
        (Command => "gnatmake",
         Arguments => (1 => new String'("-P"),
                       2 => new String'(Project_File),
                       3 => new String'("--subdirs=" & String (Subdir_Name)),
                       4 => new String'("-gnatc"),      --  only generate ALI
                       5 => new String'("-gnatd.F")));  --  ALFA section in ALI
   end Call_Gnatmake;

   -------------------
   -- Call_Gnat2Why --
   -------------------

   procedure Call_Gnat2Why
      (Proj     : Project_Tree;
       File     : Virtual_File;
       Inc_Args : Argument_List) is
      Switch         : GNAT.Strings.String_List_Access;
      Default        : Boolean;
      Proj_Type      : constant Project_Type := Root_Project (Proj);
      Local_Inc_Args : Argument_List (Inc_Args'First .. Inc_Args'Last);
   begin
      --  We need to copy the Inc_Args argument because it is used across all
      --  gnat2why calls
      for Index in Inc_Args'Range loop
         Local_Inc_Args (Index) := new String'(Inc_Args (Index).all);
      end loop;

      Switches
        (Project  => Proj_Type,
         In_Pkg   => "compiler",
         File     => File,
         Language => "Ada",
         Value    => Switch,
         Is_Default_Value => Default);
      declare
         Arguments : constant Argument_List :=
         ((1 => new String'("-gnatd.F"),  --  ALFA marks in AST
           2 => new String'(+Full_Name (File))) &
             Switch.all &
             Local_Inc_Args);
      begin
         if All_VCs then
            Call_Exit_On_Failure
              (Command   => "gnat2why",
               Arguments => Arguments);
         else
            Call_Exit_On_Failure
              (Command   => "gnat2why",
               Arguments => Arguments & (1 => new String'("-gnatd.G")));
         end if;
      end;
   end Call_Gnat2Why;

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

      Call_Exit_On_Failure
        (Command   => "why",
         Arguments =>
           ((1 => new String'("--multi-why"),
             2 => new String'("--explain"),
             3 => new String'("--locs"),
             4 => new String'(Base & Main_Suffix & ".loc"),
             5 => new String'(Base & Main_Suffix & ".why"))));
   end Call_Why;

   ---------
   -- Cat --
   ---------

   procedure Cat
     (Files   : Argument_List;
      Target  : String;
      Success : out Boolean) is
   begin
      if Verbose then
         Ada.Text_IO.Put ("cat ");

         for Index in Files'Range loop
            Ada.Text_IO.Put (Files (Index).all);
            Ada.Text_IO.Put (" ");
         end loop;

         Ada.Text_IO.Put ("> ");
         Ada.Text_IO.Put_Line (Target);
      end if;

      for Index in Files'Range loop
         Copy_File
           (Name     => Files (Index).all,
            Pathname => Target,
            Success  => Success,
            Mode     => Append,
            Preserve => None);
         exit when not Success;
      end loop;
   end Cat;

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

   Tree      : Project_Tree;
   Proj_Type : Project_Type;
   Proj_Env  : Project_Environment_Access;

   procedure Iterate_Altergo is
     new Iter_Project_Source_Files (Call_Altergo);

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

   Ada.Directories.Set_Directory (Proj_Type.Object_Dir.Display_Full_Name);

   declare
      Src_Dirs      : constant File_Array :=
         Source_Dirs (Proj_Type, Recursive => True);
      Include_Args  : aliased Argument_List (1 .. 2 * Src_Dirs'Length);
      Cnt           : Integer range 1 .. 2 * (Src_Dirs'Length + 1) := 1;

      procedure Call_Gnat2why_Gen (Proj : Project_Tree; File : Virtual_File);
      --  Wrapper for Call_Gnat2Why, fix the Inc_Args argument to the
      --  precomputed one.

      -----------------------
      -- Call_Gnat2why_Gen --
      -----------------------

      procedure Call_Gnat2why_Gen (Proj : Project_Tree; File : Virtual_File)
      is
      begin
         Call_Gnat2Why (Proj, File, Include_Args);
      end Call_Gnat2why_Gen;

      procedure Iterate_Gnat2Why is
        new Iter_Project_Source_Files (Call_Gnat2Why_Gen);
   begin
      for Index in Src_Dirs'Range loop
         Include_Args (Cnt) := new String'("-I");
         Include_Args (Cnt + 1) := new String'(+Full_Name (Src_Dirs (Index)));
         Cnt := Cnt + 2;
      end loop;
      Iterate_Gnat2Why (Tree);
   end;

   --  Set the environment variable WHYLIB, if necessary, to indicate the
   --  placement for Why
   if not Ada.Environment_Variables.Exists (WHYLIB) then
      Ada.Environment_Variables.Set
        (WHYLIB,
         Executable_Location & Why_Lib_Dir);
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
