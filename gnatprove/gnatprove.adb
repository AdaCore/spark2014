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

with GNAT.OS_Lib; use GNAT.OS_Lib;
with GNAT.Expect; use GNAT.Expect;
with GNAT.Strings;

with GNATCOLL.Projects; use GNATCOLL.Projects;
with GNATCOLL.VFS;  use GNATCOLL.VFS;

with Ada.Command_Line;
with Text_IO;

procedure Gnatprove is

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

   function Get_Ada_Include return String;

   function Load_Project_Filename return String;
   --  Get the Project Filename from the command line.

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
      (Command : String;
       Arguments : Argument_List)
   is
      Status : aliased Integer;
      S      : constant String :=
         GNAT.Expect.Get_Command_Output
           (Command   => Command,
            Arguments => Arguments,
            Input     => "",
            Status    => Status'Access,
            Err_To_Out => True);
   begin
      for Index in Arguments'Range loop
         declare
            S : String_Access := Arguments (Index);
         begin
            Free (S);
         end;
      end loop;
      if Status /= 0 then
         Text_IO.Put (Command);
         Text_IO.Put_Line (" failed.");
         Text_IO.Put (S);
         GNAT.OS_Lib.OS_Exit (1);
      end if;
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

   ---------------------------
   -- Load_Project_Filename --
   ---------------------------

   function Load_Project_Filename return String
   is
      use Ada.Command_Line;
   begin
      if Argument_Count >= 1 then
         return Argument (1);
      else
         Text_IO.Put_Line ("No project file given.");
         GNAT.OS_Lib.OS_Exit (1);
      end if;
   end Load_Project_Filename;
   Tree         : Project_Tree;
   Project_File : constant String := Load_Project_Filename;

   --  begin processing for Gnatprove
begin
   Call_Gnatmake (Project_File);

   Tree.Load (GNATCOLL.VFS.Create (+Project_File));

   Call_Gnat2Why (Tree);
end Gnatprove;
