------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2018, AdaCore                   --
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
with Ada.Strings.Unbounded;
with Ada.Text_IO;
with GNAT.Directory_Operations;
with GNATCOLL.Utils;

package body Call is

   procedure Print_Command_Line
      (Command   : String;
       Arguments : Argument_List);
   --  Print the command line for debug purposes

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
      Cnt       : Positive      := 1;
   begin
      for Elem of S loop
         Arguments (Cnt) := new String'(Elem);
         Cnt := Cnt + 1;
      end loop;
      return Arguments;
   end Argument_List_Of_String_List;

   ----------------------
   -- Call_With_Status --
   ----------------------

   procedure Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Output_FD : File_Descriptor := Standout;
      Verbose   : Boolean := False)
   is
      Executable : String_Access := Locate_Exec_On_Path (Command);
      Arg_List : Argument_List :=
        Argument_List_Of_String_List (Arguments);
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;

      if Verbose then
         Print_Command_Line (Command, Arg_List);
         Ada.Text_IO.New_Line;
      end if;

      Spawn (Executable.all, Arg_List, Output_FD, Status, Err_To_Out => True);
      GNATCOLL.Utils.Free (Arg_List);
      Free (Executable);
   end Call_With_Status;

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
         if GNATCOLL.Utils.Is_Blank_Line (Line) then
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

   --  Start of processing for Cat

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
   -- Print_Command_Line --
   ------------------------

   procedure Print_Command_Line
      (Command   : String;
       Arguments : Argument_List)
   is
   begin
      Ada.Text_IO.Put (Command);

      for Arg of Arguments loop
         Ada.Text_IO.Put (" ");
         Ada.Text_IO.Put (Arg.all);
      end loop;
   end Print_Command_Line;

   ---------------------------
   -- Read_File_Into_String --
   ---------------------------

   function Read_File_Into_String (Fn : String) return String
   is
      use Ada.Strings.Unbounded;
      U : Unbounded_String := Null_Unbounded_String;

      procedure Append_To_Buf (S : String);

      -------------------
      -- Append_To_Buf --
      -------------------

      procedure Append_To_Buf (S : String) is
      begin
         Append (U, S);
      end Append_To_Buf;

      procedure Do_It is new Call.For_Line_In_File (Append_To_Buf);

   --  Start of processing for Read_File_Into_String

   begin
      Do_It (Fn);
      return To_String (U);
   end Read_File_Into_String;

end Call;
