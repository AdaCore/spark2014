------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
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

with Ada.IO_Exceptions;
with Ada.Text_IO;
with GNAT.Directory_Operations;

package body Call is

   function Argument_List_Of_String_List (S : String_Lists.List)
      return Argument_List;
   --  Convert a String List into an Argument List

   procedure Free_Argument_List (L : Argument_List);
   --  free all strings in an argument list

   procedure Print_Command_Line
      (Command : String;
       Arguments : Argument_List);
   --  print the command line for debug purposes

   ------------------------
   -- Abort_With_Message --
   ------------------------

   procedure Abort_With_Message (Msg : String) is
   begin
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      GNAT.OS_Lib.OS_Exit (1);
   end Abort_With_Message;

   ----------------------------------
   -- Argument_List_Of_String_List --
   ----------------------------------

   function Argument_List_Of_String_List (S : String_Lists.List)
      return Argument_List
   is
      use String_Lists;
      Arguments : Argument_List := (1 .. Integer (S.Length) => <>);
      Cur       : Cursor        := First (S);
      Cnt       : Integer       := 1;
   begin
      while Has_Element (Cur) loop
         Arguments (Cnt) := new String'(Element (Cur));
         Next (Cur);
         Cnt := Cnt + 1;
      end loop;
      return Arguments;
   end Argument_List_Of_String_List;

   ------------------------
   -- Print_Command_Line --
   ------------------------

   procedure Print_Command_Line
      (Command : String;
       Arguments : Argument_List)
   is
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

   ----------------------
   -- Call_With_Status --
   ----------------------

   procedure Call_With_Status
     (Command   : String;
      Arguments : Argument_List;
      Status    : out Integer;
      Verbose   : Boolean := False)
   is
      Executable : String_Access :=
         Locate_Exec_On_Path (Command);
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;
      if Verbose then
         Print_Command_Line (Command, Arguments);
         Ada.Text_IO.New_Line;
      end if;
      Spawn (Executable.all, Arguments, Standout, Status, Err_To_Out => True);
      Free_Argument_List (Arguments);
      Free (Executable);
   end Call_With_Status;

   procedure Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Verbose   : Boolean := False)
   is
   begin
      Call_With_Status
        (Command,
         Argument_List_Of_String_List (Arguments),
         Status,
         Verbose);
   end Call_With_Status;

   --------------------------
   -- Call_Exit_On_Failure --
   --------------------------

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : Argument_List;
      Verbose   : Boolean := False)
   is
      Status     : Integer;
      Executable : String_Access :=
         Locate_Exec_On_Path (Command);
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;
      if Verbose then
         Print_Command_Line (Executable.all, Arguments);
         Ada.Text_IO.New_Line;
      end if;
      Spawn (Executable.all, Arguments, Standout, Status, Err_To_Out => True);
      if Status /= 0 then
         Print_Command_Line (Executable.all, Arguments);
         Ada.Text_IO.Put_Line (" failed.");
         GNAT.OS_Lib.OS_Exit (1);
      else
         Ada.Text_IO.New_Line;
      end if;
      Free_Argument_List (Arguments);
      Free (Executable);
   end Call_Exit_On_Failure;

   procedure Call_Exit_On_Failure
     (Command   : String;
      Arguments : String_Lists.List;
      Verbose   : Boolean := False)
   is
   begin
      Call_Exit_On_Failure
        (Command,
         Argument_List_Of_String_List (Arguments),
         Verbose);
   end Call_Exit_On_Failure;

   ---------
   -- Cat --
   ---------

   procedure Cat (File : String; Cut_Non_Blank_Line_At : Natural := 0) is

      Count_Non_Blank_Lines : Natural := 0;
      First_Line_Skipped    : Boolean := False;

      procedure Print_Line (Line : String);
      --  Print a single line to stdout. Skip the line if not blank and count
      --  of non-blank lines exceeds the positive value (if non-zero) of
      --  Cut_Non_Blank_Line_At. Instead, prints a line suggesting
      --  continuation "(...)".

      ----------------
      -- Print_Line --
      ----------------

      procedure Print_Line (Line : String) is
      begin
         if Is_Blank (Line) then
            First_Line_Skipped := False;
            Count_Non_Blank_Lines := 0;
            Ada.Text_IO.Put_Line (Line);

         elsif Cut_Non_Blank_Line_At > 0
           and then Count_Non_Blank_Lines > Cut_Non_Blank_Line_At
         then
            if not First_Line_Skipped then
               First_Line_Skipped := True;
               Ada.Text_IO.Put_Line ("(...)");
            end if;

         else
            First_Line_Skipped := False;
            Count_Non_Blank_Lines := Count_Non_Blank_Lines + 1;
            Ada.Text_IO.Put_Line (Line);
         end if;
      end Print_Line;

      procedure My_Cat is new For_Line_In_File (Print_Line);
   begin
      My_Cat (File);
   end Cat;

   -----------------------------
   -- Ch_Dir_Create_If_Needed --
   -----------------------------

   procedure Ch_Dir_Create_If_Needed (Dir : String) is
      use GNAT.Directory_Operations;
   begin
      Change_Dir (Dir);
   exception
      when Directory_Error =>
         Make_Dir (Dir);
         Change_Dir (Dir);
   end Ch_Dir_Create_If_Needed;

   ----------------------
   -- For_Line_In_File --
   ----------------------

   procedure For_Line_In_File (File : String)
   is
      use Ada.Text_IO;
      File_Handle : File_Type;
   begin
      Open (File_Handle, In_File, File);
      while True loop
         declare
            Line : constant String := Get_Line (File_Handle);
         begin
            Handle_Line (Line);
         end;
      end loop;
   exception
      when Ada.IO_Exceptions.End_Error =>
         Close (File_Handle);
   end For_Line_In_File;

   ------------------------
   -- Free_Argument_List --
   ------------------------

   procedure Free_Argument_List (L : Argument_List)
   is
   begin
      for Index in L'Range loop
         declare
            S : String_Access := L (Index);
         begin
            Free (S);
         end;
      end loop;
   end Free_Argument_List;

end Call;
