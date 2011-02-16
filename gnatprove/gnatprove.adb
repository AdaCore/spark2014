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

   procedure Call_Altergo (Proj : Project_Tree);
   --  Call Alt-Ergo on all generated PO files of the project.

   procedure Call_Exit_On_Failure
      (Command : String;
       Arguments : Argument_List);
   --  Call the given command using the given argument list.
   --  Free all argument access values
   --  If the command exit status is not 0, print its output and exit.

   procedure Call_Gnatmake (Project_File : String);
   --  Call gnatmake using the given project file.

   procedure Call_Gnat2Why (Proj : Project_Tree);
   --  Call gnat2why on all source files of the project.

   procedure Call_Why (Proj : Project_Tree);
   --  Call why on all generated why files of the project.

   procedure Cat
      (Files   : Argument_List;
       Target  : String;
       Success : out Boolean);
   --  Cat all the files together into the target

   function Get_Ada_Include return String;

   ------------------
   -- Call_Altergo --
   ------------------

   procedure Call_Altergo (Proj : Project_Tree)
   is
      Proj_Type : constant Project_Type := Root_Project (Proj);
      File_List : constant File_Array_Access := Source_Files (Proj_Type);
   begin
      for Index in File_List'Range loop
         declare
            Cur_File : constant Virtual_File := File_List (Index);
            Base : constant String :=
               Ada.Directories.Base_Name (+Base_Name (Cur_File));
         begin
            --  assuming 'base' to be the filename without suffix,
            --  call the command
            --    why-cpulimit <timeout> alt-ergo <file>
            --  for each 'file' of the form
            --    <base_po*.why>
            if Unit_Part (Info (Proj, Cur_File)) = Unit_Body then
               declare
                  procedure Call_AltErgo_OnFile (Item  : String);

                  procedure Call_AltErgo_On_Vc
                    (Item  : String;
                     Index : Positive;
                     Quit : in out Boolean);
                  --  Call Altergo on the VC that corresponds to the file
                  --  'Item'; take into account the context file.

                  -------------------------
                  -- Call_AltErgo_OnFile --
                  -------------------------

                  procedure Call_AltErgo_OnFile (Item  : String)
                  is
                  begin
                     --  ??? use 10 as timeout for now
                     Call_Exit_On_Failure
                       (Command   => "why-cpulimit",
                        Arguments =>
                          ((1 => new String'("10"),
                            2 => new String'("alt-ergo"),
                            3 => new String'(Item))));
                  end Call_AltErgo_OnFile;

                  ------------------------
                  -- Call_AltErgo_On_Vc --
                  ------------------------

                  procedure Call_AltErgo_On_Vc
                    (Item  : String;
                     Index : Positive;
                     Quit : in out Boolean)
                  is
                     Target : constant String := "new.why";
                     Success : aliased Boolean;
                  begin
                     Delete_File (Target, Success);
                     Cat (Files =>
                           (1 => new String'(Base & "_ctx.why"),
                            2 => new String'(Item)),
                          Target => Target,
                          Success => Success);
                     Call_AltErgo_OnFile (Target);
                     Quit := not Success;
                     if Index > 1 then
                        Quit := False;
                     end if;
                     Delete_File (Target, Success);
                  end Call_AltErgo_On_Vc;

                  procedure Iterate is new
                     GNAT.Directory_Operations.Iteration.Wildcard_Iterator
                       (Action => Call_AltErgo_On_Vc);
               begin
                  Iterate (Path => Base & "_po*.why");
               end;
            end if;
         end;
      end loop;
   end Call_Altergo;

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
                       3 => new String'("-gnatc")));

   end Call_Gnatmake;

   -------------------
   -- Call_Gnat2Why --
   -------------------

   procedure Call_Gnat2Why (Proj : Project_Tree)
   is
      Proj_Type : constant Project_Type := Root_Project (Proj);
      File_List : constant File_Array_Access := Source_Files (Proj_Type);
   begin
      for Index in File_List'Range loop
         declare
            Cur_File : constant Virtual_File := File_List (Index);
         begin
            if Unit_Part (Info (Proj, Cur_File)) = Unit_Body then
               declare
                  Switch : GNAT.Strings.String_List_Access;
                  Default : Boolean;
               begin
                  Switches
                     (Project  => Proj_Type,
                      In_Pkg   => "compiler",
                      File     => Cur_File,
                      Language => "Ada",
                      Value    => Switch,
                      Is_Default_Value => Default);
                  Call_Exit_On_Failure
                    (Command   => "gnat2why",
                     Arguments =>
                       ((1 => new String'("-I"),
                         2 => new String'(Get_Ada_Include),
                         3 => new String'(+Full_Name (Cur_File))) &
                         Switch.all));
               end;
            end if;
         end;
      end loop;
   end Call_Gnat2Why;

   --------------
   -- Call_Why --
   --------------

   procedure Call_Why (Proj : Project_Tree)
   is
      Proj_Type : constant Project_Type := Root_Project (Proj);
      File_List : constant File_Array_Access := Source_Files (Proj_Type);
   begin
      for Index in File_List'Range loop
         declare
            Cur_File : constant Virtual_File := File_List (Index);
            Base : constant String :=
               Ada.Directories.Base_Name (+Full_Name (Cur_File));
         begin
            --  assuming 'base' to be the filename without suffix, call the
            --  command
            --  why --multiwhy --explain --locs <base>.locs <base>.why
            if Unit_Part (Info (Proj, Cur_File)) = Unit_Body then
               Call_Exit_On_Failure
                 (Command   => "why",
                  Arguments =>
                    ((1 => new String'("--multi-why"),
                      2 => new String'("--explain"),
                      3 => new String'("--locs"),
                      4 => new String'(Base & ".loc"),
                      5 => new String'(Base & ".why"))));
            end if;
         end;
      end loop;
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

   Tree      : Project_Tree;
   Proj_Type : Project_Type;

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

   Call_Gnatmake (Project_File.all);

   Tree.Load (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)));
   Proj_Type := Root_Project (Tree);
   Ada.Directories.Set_Directory
     (Attribute_Value (Proj_Type, Obj_Dir_Attribute));

   Call_Gnat2Why (Tree);

   Call_Why (Tree);

   Call_Altergo (Tree);
end Gnatprove;
