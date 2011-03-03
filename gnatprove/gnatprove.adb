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

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Directory_Operations.Iteration;
with GNAT.Expect;       use GNAT.Expect;
with GNAT.OS_Lib;       use GNAT.OS_Lib;
with GNAT.Strings;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.VFS;      use GNATCOLL.VFS;

with Text_IO;

procedure Gnatprove is

   --  Variables for command line parsing
   Config       : Command_Line_Configuration;
   Verbose      : aliased Boolean;
   Project_File : aliased GNAT.Strings.String_Access;

   Subdir_Name  : constant Filesystem_String := "gnatprove";

   procedure Call_Altergo (Proj : Project_Tree; File : Virtual_File);
   --  Call Alt-Ergo on all VC files that correspond to a given source file of
   --  a project

   procedure Call_AltErgo_On_File
      (File : String;
       Result_File : String;
       Timeout : Natural);
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

   procedure Call_Gnat2Why (Proj : Project_Tree; File : Virtual_File);
   --  Call gnat2why on a single source file of a project.

   procedure Call_Why (Proj : Project_Tree; File : Virtual_File);
   --  Call why on all the generated files that belong to a certain file
   --  in a project.
   --  example: if File is "example.adb", we call why on file "example.why".

   procedure Cat
      (Files   : Argument_List;
       Target  : String;
       Success : out Boolean);
   --  Cat all the Files together into the Target.

   function Get_Ada_Include return String;

   generic
      with procedure Action (Proj : Project_Tree; File : Virtual_File);
   procedure Iter_Project_Source_Files (Proj : Project_Tree);
   --  Iterate over all source files of a project.

   ------------------
   -- Call_Altergo --
   ------------------

   procedure Call_Altergo (Proj : Project_Tree; File : Virtual_File)
   is
      pragma Unreferenced (Proj);
      Base : constant String :=
         Ada.Directories.Base_Name (+Base_Name (File));

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
               (1 => new String'(Base & "_ctx.why"),
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
      Iterate (Path => Base & "_po*.why");
   end Call_Altergo;

   --------------------------
   -- Call_AltErgo_On_File --
   --------------------------

   procedure Call_AltErgo_On_File
      (File : String;
       Result_File : String;
       Timeout : Natural)
   is
   begin
      if Verbose then
         Text_IO.Put ("calling Alt-ergo on ");
         Text_IO.Put_Line (File);
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
         FT : Text_IO.File_Type;
      begin
         Text_IO.Create (FT, Text_IO.Out_File, Result_File);
         if Status /= 0 or else S'Length = 0 then
            Text_IO.Put (FT, "File """);
            Text_IO.Put (FT, File);
            Text_IO.Put_Line (FT, """:Failure or Timeout");
         else
            Text_IO.Put (FT, S);
         end if;
         Text_IO.Close (FT);
      end;
   end Call_AltErgo_On_File;

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
      (Command : String;
       Arguments : Argument_List)
   is
      Status : aliased Integer;
      procedure Print_Command_Line;
      --  print the command line for debug purposes

      ------------------------
      -- Print_Command_Line --
      ------------------------

      procedure Print_Command_Line
      is
      begin
         Text_IO.Put (Command);
         for Index in Arguments'Range loop
            declare
               S : constant String_Access := Arguments (Index);
            begin
               Text_IO.Put (" ");
               Text_IO.Put (S.all);
            end;
         end loop;
      end Print_Command_Line;
   begin
      if Verbose then
         Print_Command_Line;
         Text_IO.Put_Line ("");
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
            Text_IO.Put_Line (" failed.");
            Text_IO.Put (S);
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

   procedure Call_Gnatmake (Project_File : String)
   is
   begin
      Call_Exit_On_Failure
        (Command => "gnatmake",
         Arguments => (1 => new String'("-P"),
                       2 => new String'(Project_File),
                       3 => new String'("--subdirs=" & String (Subdir_Name)),
                       4 => new String'("-gnata"),      --  generate assertions
                       5 => new String'("-gnat2012"),   --  enable Ada 2012
                       6 => new String'("-gnatc"),      --  only generate ALI
                       7 => new String'("-f"),          --  Force recompilation
                       8 => new String'("-gnatd.F")));  --  ALFA section in ALI

   end Call_Gnatmake;

   -------------------
   -- Call_Gnat2Why --
   -------------------

   procedure Call_Gnat2Why (Proj : Project_Tree; File : Virtual_File)
   is
      Switch : GNAT.Strings.String_List_Access;
      Default : Boolean;
      Proj_Type : constant Project_Type := Root_Project (Proj);
   begin
      Switches
         (Project  => Proj_Type,
          In_Pkg   => "compiler",
          File     => File,
          Language => "Ada",
          Value    => Switch,
          Is_Default_Value => Default);
      --  We force the use of switch -gnata, because gnat2why may be
      --  incorrect otherwise
      Call_Exit_On_Failure
        (Command   => "gnat2why",
         Arguments =>
           ((1 => new String'("-I"),
             2 => new String'(Get_Ada_Include),
             3 => new String'("-gnata"),
             4 => new String'("-gnat2012"),
             5 => new String'("-gnato"),
             6 => new String'("-gnatd.F"),  --  ALFA marks in AST
             7 => new String'(+Full_Name (File))) &
             Switch.all));
   end Call_Gnat2Why;

   --------------
   -- Call_Why --
   --------------

   procedure Call_Why (Proj : Project_Tree; File : Virtual_File)
   is
      pragma Unreferenced (Proj);
      Base : constant String :=
           Ada.Directories.Base_Name (+Full_Name (File));
   begin
      --  assuming 'base' to be the filename without suffix, call the
      --  command
      --  why --multiwhy --explain --locs <base>.locs <base>.why
      Call_Exit_On_Failure
        (Command   => "why",
         Arguments =>
           ((1 => new String'("--multi-why"),
             2 => new String'("--explain"),
             3 => new String'("--locs"),
             4 => new String'(Base & ".loc"),
             5 => new String'(Base & ".why"))));
   end Call_Why;

   ---------
   -- Cat --
   ---------

   procedure Cat
      (Files   : Argument_List;
       Target  : String;
       Success : out Boolean)
   is
   begin
      if Verbose then
         Text_IO.Put ("cat ");
         for Index in Files'Range loop
            declare
               Cur_File : constant String_Access := Files (Index);
            begin
               Text_IO.Put (Cur_File.all);
               Text_IO.Put (" ");
            end;
         end loop;
         Text_IO.Put ("> ");
         Text_IO.Put_Line (Target);
      end if;
      for Index in Files'Range loop
         declare
            Cur_File : constant String_Access := Files (Index);
         begin
            Copy_File
              (Name     => Cur_File.all,
               Pathname => Target,
               Success  => Success,
               Mode     => Append,
               Preserve => None);
            exit when not Success;
         end;
      end loop;
   end Cat;

   ---------------------
   -- Get_Ada_Include --
   ---------------------

   function Get_Ada_Include return String
   is
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

   procedure Iter_Project_Source_Files (Proj : Project_Tree)
   is
      Proj_Type : constant Project_Type := Root_Project (Proj);
      File_List : constant File_Array_Access := Source_Files (Proj_Type);
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
                      "ada") = "" then
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

   procedure Iterate_Gnat2Why is
      new Iter_Project_Source_Files (Call_Gnat2Why);

   procedure Iterate_Why is
      new Iter_Project_Source_Files (Call_Why);

   --  begin processing for Gnatprove
begin
   --  Install command line config
   Define_Switch (Config, Verbose'Access,
                  "-v", Long_Switch => "--verbose",
                  Help => "Output extra verbose information");

   Define_Switch (Config, Project_File'Access,
                  "-P:",
                  Help => "The name of the project file");

   Getopt (Config);

   Initialize (Proj_Env);
   Set_Object_Subdir (Proj_Env.all, Subdir_Name);
   Tree.Load
      (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
       Proj_Env);
   Proj_Type := Root_Project (Tree);
   declare
      Working_Dir : constant String :=
         String (Full_Name (Object_Dir (Proj_Type)).all);
   begin
      --  Call gnatmake before changing the directory, for the project file to
      --  be in the path
      Call_Gnatmake (Project_File.all);

      Ada.Directories.Set_Directory (Working_Dir);

      Iterate_Gnat2Why (Tree);

      Iterate_Why (Tree);

      Iterate_Altergo (Tree);
   end;

end Gnatprove;
